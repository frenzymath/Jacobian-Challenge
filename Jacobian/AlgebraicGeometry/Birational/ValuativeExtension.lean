import Jacobian.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Extending rational maps from valuation stalks

A rational map from an integral scheme with valuation local rings to a proper
separated scheme extends across every point, hence to the whole scheme. The
valuative criterion gives the local extensions and the maximal domain of the
rational map assembles them.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- A map from the function field of an integral scheme with valuation stalks to
a proper separated scheme extends over the entire source. -/
theorem exists_hom_of_valuationRing_stalk {source target base : Scheme.{u}}
    [source.Over base] [target.Over base] [IsIntegral source]
    [IsProper (target ↘ base)] [target.IsSeparated] [base.IsSeparated]
    (valuation : ∀ point : source, ValuationRing (source.presheaf.stalk point))
    (genericMap : Spec source.functionField ⟶ target)
    (over_base : genericMap ≫ target ↘ base = source.fromSpecFunctionField ≫ source ↘ base) :
    ∃ extension : source ⟶ target,
      extension.IsOver base ∧ source.fromSpecFunctionField ≫ extension = genericMap := by
  let rationalMap : source ⤏ target :=
    RationalMap.ofFunctionField (source ↘ base) (target ↘ base) genericMap over_base
  have generic_eq : rationalMap.fromFunctionField = genericMap :=
    RationalMap.fromFunctionField_ofFunctionField _ _ _ _
  have full_domain : rationalMap.domain = ⊤ := by
    refine eq_top_iff.mpr fun point _ ↦ ?_
    have domain : IsDomain (source.presheaf.stalk point) := inferInstance
    have := valuation point
    have square : CommSq genericMap
        (Spec.map (CommRingCat.ofHom
          (algebraMap (source.presheaf.stalk point) source.functionField)))
        (target ↘ base) (source.fromSpecStalk point ≫ source ↘ base) := ⟨by
      rw [over_base, ← Category.assoc]
      congr 1
      exact (SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes point)).symm⟩
    have existence : ValuativeCriterion.Existence (target ↘ base) :=
      (UniversallyClosed.eq_valuativeCriterion ▸
        (inferInstance : UniversallyClosed (target ↘ base))).1
    obtain ⟨⟨localMap, generic_commutes, base_commutes⟩⟩ := existence
      { R := source.presheaf.stalk point, domain := domain, K := source.functionField,
        i₁ := genericMap, i₂ := source.fromSpecStalk point ≫ source ↘ base, commSq := square }
    let partialMap := PartialMap.ofFromSpecStalk (source ↘ base) (target ↘ base)
      localMap (by rw [base_commutes])
    have point_mem : point ∈ partialMap.domain := PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
    refine RationalMap.mem_domain.mpr
      ⟨partialMap, point_mem, RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
    rw [generic_eq, RationalMap.fromFunctionField_toRationalMap]
    refine Eq.trans ?_ generic_commutes
    have local_eq : partialMap.fromSpecStalkOfMem point_mem = localMap :=
      PartialMap.fromSpecStalkOfMem_ofFromSpecStalk
        (source ↘ base) (target ↘ base) localMap (by rw [base_commutes])
    change _ = _ ≫ localMap
    rw [← local_eq]
    simp only [PartialMap.fromFunctionField, PartialMap.fromSpecStalkOfMem, ← Category.assoc]
    congr 1
    rw [← cancel_mono partialMap.domain.ι, Category.assoc, Opens.fromSpecStalkOfMem_ι,
      Opens.fromSpecStalkOfMem_ι]
    exact (SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes point)).symm
  let partialMap := rationalMap.toPartialMap
  have domain_eq : partialMap.domain = ⊤ := full_domain
  have : IsIso partialMap.domain.ι := by
    have top_inclusion {openSet : source.Opens} (equality : openSet = ⊤) :
        IsIso openSet.ι := by
      subst equality
      exact ⟨⟨source.topIso.inv, source.ι_toIso_inv, source.toIso_inv_ι⟩⟩
    exact top_inclusion domain_eq
  have : rationalMap.IsOver base := by
    rw [RationalMap.isOver_iff]
    exact ((RationalMap.equivFunctionField (source ↘ base) (target ↘ base))
      ⟨genericMap, over_base⟩).2
  have partial_over : partialMap.hom ≫ target ↘ base = partialMap.domain.ι ≫ source ↘ base :=
    PartialMap.isOver_iff.mp inferInstance
  refine ⟨inv partialMap.domain.ι ≫ partialMap.hom, ⟨?_⟩, ?_⟩
  · rw [Category.assoc, partial_over, IsIso.inv_hom_id_assoc]
  · have generic_mem : genericPoint source ∈ partialMap.domain := domain_eq ▸ trivial
    have generic_inclusion : source.fromSpecFunctionField ≫ inv partialMap.domain.ι =
        partialMap.domain.fromSpecStalkOfMem (genericPoint source) generic_mem := by
      rw [IsIso.comp_inv_eq, Opens.fromSpecStalkOfMem_ι]
    rw [← Category.assoc, generic_inclusion, ← generic_eq,
      ← rationalMap.toRationalMap_toPartialMap, RationalMap.fromFunctionField_toRationalMap]
    rfl

end AlgebraicGeometry.Scheme
