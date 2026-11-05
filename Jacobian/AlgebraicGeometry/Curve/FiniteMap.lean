import Jacobian.AlgebraicGeometry.Birational.ValuativeExtension
import Jacobian.AlgebraicGeometry.Curve.Dimension
import Jacobian.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Finite flat morphisms between smooth proper curves

A morphism between integral smooth curves that carries the generic point to the
generic point is finite, surjective and flat if its source is proper and its target
is separated over the ground field. Finiteness
follows from the finite fibres, and flatness follows from torsion-freeness over
the valuation local rings of the target.

A nonconstant map from the function field to a smooth proper curve extends by
the valuative criterion and gives such a finite flat morphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Scheme

/-- A generically dominant morphism of integral smooth curves with proper source
and separated target is finite, surjective and flat. -/
theorem isFinite_surjective_flat_of_genericPoint_eq {baseField : Type u} [Field baseField]
    {source target : Scheme.{u}} [source.Over (Spec (.of baseField))]
    [target.Over (Spec (.of baseField))] [IsIntegral source] [IsIntegral target]
    [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
    [SmoothOfRelativeDimension 1 (target ↘ Spec (.of baseField))]
    [IsProper (source ↘ Spec (.of baseField))]
    [IsSeparated (target ↘ Spec (.of baseField))]
    (morphism : source ⟶ target) [morphism.IsOver (Spec (.of baseField))]
    (generic_image : morphism (genericPoint source) = genericPoint target) :
    IsFinite morphism ∧ Surjective morphism ∧ Flat morphism := by
  have : Smooth (source ↘ Spec (.of baseField)) := SmoothOfRelativeDimension.smooth 1 _
  have : Smooth (target ↘ Spec (.of baseField)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsLocallyNoetherian source :=
    LocallyOfFiniteType.isLocallyNoetherian (source ↘ Spec (.of baseField))
  have : CompactSpace source :=
    QuasiCompact.compactSpace_of_compactSpace (source ↘ Spec (.of baseField))
  have : IsNoetherian source := {}
  have source_dimension : topologicalKrullDim source ≤ 1 := by
    exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension
      (source ↘ Spec (.of baseField)) 1
  have : IsProper morphism := by
    have : IsProper (morphism ≫ target ↘ Spec (.of baseField)) := by
      rw [HomIsOver.comp_over]
      infer_instance
    exact IsProper.of_comp morphism (target ↘ Spec (.of baseField))
  have generic_not_closed : ¬ IsClosed ({genericPoint target} : Set target) := by
    intro closed
    have dimension := ringKrullDim_stalk_eq_one_of_isClosed
      (target ↘ Spec (.of baseField)) closed
    rw [ringKrullDim_eq_zero_of_isField (Field.toIsField target.functionField)] at dimension
    exact zero_ne_one dimension
  have surjective : Surjective morphism := by
    refine ⟨fun point ↦ ?_⟩
    have closed_range : IsClosed (Set.range morphism) := morphism.isClosedMap.isClosed_range
    have contains_generic : closure {genericPoint target} ⊆ Set.range morphism :=
      closure_minimal (by rintro _ rfl; exact ⟨_, generic_image⟩) closed_range
    rw [show closure ({genericPoint target} : Set target) = Set.univ from
      genericPoint_spec target] at contains_generic
    exact contains_generic trivial
  have finite_fibres (point : target) : (morphism ⁻¹' {point}).Finite := by
    by_cases closed : IsClosed ({point} : Set target)
    · have closed_fibre : IsClosed (morphism ⁻¹' {point}) := closed.preimage morphism.continuous
      have generic_outside : genericPoint source ∉ morphism ⁻¹' {point} := by
        intro membership
        rw [Set.mem_preimage, Set.mem_singleton_iff, generic_image] at membership
        exact generic_not_closed (membership ▸ closed)
      have := IsOpen.finite_compl_of_topologicalKrullDim_le_one source_dimension
        closed_fibre.isOpen_compl ⟨_, generic_outside⟩
      simpa using this
    · refine (Set.finite_singleton (genericPoint source)).subset fun preimage membership ↦ ?_
      rw [Set.mem_preimage, Set.mem_singleton_iff] at membership
      refine eq_genericPoint_of_not_isClosed source_dimension fun preimage_closed ↦ closed ?_
      rw [← membership, ← Set.image_singleton]
      exact morphism.isClosedMap _ preimage_closed
  have : LocallyQuasiFinite morphism :=
    (locallyQuasiFinite_iff_finite_preimage_singleton).mpr finite_fibres
  have finite : IsFinite morphism := IsFinite.of_isProper_of_locallyQuasiFinite morphism
  have flat : Flat morphism := by
    refine Flat.of_stalkMap morphism fun point ↦ ?_
    have valuation := valuationRing_stalk (target ↘ Spec (.of baseField)) (morphism point)
    have injective : Function.Injective (morphism.stalkMap point) := by
      have compatibility := Scheme.Hom.stalkSpecializes_stalkMap morphism
        (genericPoint source) point ((genericPoint_spec source).specializes (Set.mem_univ point))
      have generic_field : IsField (target.presheaf.stalk (morphism (genericPoint source))) :=
        generic_image ▸ Field.toIsField target.functionField
      have generic_injective : Function.Injective
          (target.presheaf.stalkSpecializes
            (morphism.base.hom.map_specializes
              ((genericPoint_spec source).specializes (Set.mem_univ point))) ≫
            morphism.stalkMap (genericPoint source)) := by
        let := generic_field.toField
        exact (RingHom.injective (morphism.stalkMap (genericPoint source)).hom).comp
          (injective_stalkSpecializes _)
      rw [compatibility] at generic_injective
      exact fun left right equality ↦ generic_injective
        (by rw [CommRingCat.comp_apply, CommRingCat.comp_apply, equality])
    algebraize [(morphism.stalkMap point).hom]
    change Module.Flat (target.presheaf.stalk (morphism point)) (source.presheaf.stalk point)
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    refine eq_bot_iff.mpr fun element ⟨⟨scalar, regular⟩, annihilated⟩ ↦ ?_
    have scalar_nonzero : scalar ≠ 0 := nonZeroDivisors.ne_zero regular
    have image_nonzero : algebraMap (target.presheaf.stalk (morphism point))
        (source.presheaf.stalk point) scalar ≠ 0 := by
      exact fun equality ↦ scalar_nonzero
        (injective (equality.trans (morphism.stalkMap point).hom.map_zero.symm))
    rw [Submonoid.smul_def, Algebra.smul_def] at annihilated
    exact (mul_eq_zero.mp annihilated).resolve_left image_nonzero
  exact ⟨finite, surjective, flat⟩

/-- A nonconstant map from the function field of a smooth proper integral curve
to another smooth proper integral curve extends to a finite flat surjective map. -/
theorem exists_isFinite_flat_hom_of_functionField {baseField : Type u} [Field baseField]
    {source target : Scheme.{u}} [source.Over (Spec (.of baseField))]
    [target.Over (Spec (.of baseField))] [IsIntegral source] [IsIntegral target]
    [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
    [SmoothOfRelativeDimension 1 (target ↘ Spec (.of baseField))]
    [IsProper (source ↘ Spec (.of baseField))] [IsProper (target ↘ Spec (.of baseField))]
    (genericMap : Spec source.functionField ⟶ target)
    (over_base : genericMap ≫ target ↘ Spec (.of baseField) =
      source.fromSpecFunctionField ≫ source ↘ Spec (.of baseField))
    (nonconstant : ¬ IsClosed {genericMap (IsLocalRing.closedPoint source.functionField)}) :
    ∃ morphism : source ⟶ target, morphism.IsOver (Spec (.of baseField)) ∧
      IsFinite morphism ∧ Surjective morphism ∧ Flat morphism ∧
      LocallyOfFinitePresentation morphism ∧ source.fromSpecFunctionField ≫ morphism = genericMap := by
  have : Smooth (source ↘ Spec (.of baseField)) := SmoothOfRelativeDimension.smooth 1 _
  have : Smooth (target ↘ Spec (.of baseField)) := SmoothOfRelativeDimension.smooth 1 _
  have : target.IsSeparated :=
    ⟨by rw [← terminal.comp_from (target ↘ Spec (.of baseField))]; infer_instance⟩
  obtain ⟨morphism, over, generic_eq⟩ := exists_hom_of_valuationRing_stalk
    (base := Spec (.of baseField)) (valuationRing_stalk (source ↘ Spec (.of baseField)))
    genericMap over_base
  letI : morphism.IsOver (Spec (.of baseField)) := over
  have generic_image : morphism (genericPoint source) = genericPoint target := by
    have image : genericMap (IsLocalRing.closedPoint source.functionField) =
        morphism (genericPoint source) := by
      rw [← generic_eq]
      change morphism (source.fromSpecFunctionField
        (IsLocalRing.closedPoint source.functionField)) = _
      rw [Scheme.fromSpecStalk_closedPoint]
    have target_dimension : topologicalKrullDim target ≤ 1 := by
      exact_mod_cast
        (topologicalKrullDim_le_of_smoothOfRelativeDimension
          (target ↘ Spec (.of baseField)) 1)
    apply eq_genericPoint_of_not_isClosed target_dimension
    exact image ▸ nonconstant
  obtain ⟨finite, surjective, flat⟩ :=
    isFinite_surjective_flat_of_genericPoint_eq (baseField := baseField) morphism generic_image
  have : IsLocallyNoetherian target :=
    LocallyOfFiniteType.isLocallyNoetherian (target ↘ Spec (.of baseField))
  have : LocallyOfFinitePresentation morphism :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  exact ⟨morphism, over, finite, surjective, flat, inferInstance, generic_eq⟩

end AlgebraicGeometry.Scheme
