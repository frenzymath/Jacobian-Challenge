import Jacobian.AlgebraicGeometry.Curve.Basic
import Jacobian.AlgebraicGeometry.Curve.FiniteMap
import Jacobian.AlgebraicGeometry.Curve.SeparatingFunction
import Jacobian.AlgebraicGeometry.ProjectiveLine.Geometry
import Jacobian.AlgebraicGeometry.ProjectiveLine.RationalPoint

/-!
# Separating finite morphisms to the projective line

A smooth proper integral curve over a field has a finite flat morphism to the
projective line which is unramified at the generic point. A rational function
with nonzero differential defines the point `[1:t]` of the projective line over
the function field. The valuative criterion extends this point to the curve,
and the nonconstant-map criterion proves finiteness and flatness.

The final theorem applies directly to smooth proper geometrically irreducible
curves, without a choice of rational point or a prescribed rational function.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory KaehlerDifferential

namespace AlgebraicGeometry

namespace Scheme

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
variable [source.Over (Spec (.of baseField))] [IsIntegral source]

/-- A rational function used as the affine coordinate of a morphism to the
projective line lies in the image of its map on generic stalks. -/
theorem mem_range_stalkMap_genericPoint_of_affinePoint (element : source.functionField)
    (morphism : source ⟶ projectiveLine baseField)
    (agreement : source.fromSpecFunctionField ≫ morphism =
      ProjectiveLine.affinePoint (functionFieldRingHom baseField source) element) :
    element ∈ Set.range (morphism.stalkMap (genericPoint source)) := by
  have inRange := ProjectiveLine.mem_range_stalkClosedPointTo_affinePoint
    (functionFieldRingHom baseField source) element
  rw [← agreement] at inRange
  obtain ⟨stalkSection, image⟩ := inRange
  rw [stalkClosedPointTo_comp, CommRingCat.comp_apply,
    stalkClosedPointTo_fromSpecStalk] at image
  have transport (point : source) (point_eq : point = genericPoint source)
      (stalkSection : (projectiveLine baseField).presheaf.stalk (morphism point))
      (inseparable : Inseparable point (genericPoint source)) :
      (source.presheaf.stalkCongr inseparable).hom (morphism.stalkMap point stalkSection) ∈
        Set.range (morphism.stalkMap (genericPoint source)) := by
    subst point_eq
    exact ⟨stalkSection, by simp⟩
  exact image ▸ transport _ fromSpecStalk_closedPoint stalkSection _

/-- A nonzero differential of an affine coordinate makes the morphism to the
projective line formally unramified at the generic point. -/
theorem formallyUnramified_stalkMap_genericPoint_of_affinePoint
    [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
    (element : source.functionField)
    (nonzero : letI := (functionFieldRingHom baseField source).toAlgebra
      D baseField source.functionField element ≠ 0)
    (morphism : source ⟶ projectiveLine baseField)
    [morphism.IsOver (Spec (.of baseField))]
    (agreement : source.fromSpecFunctionField ≫ morphism =
      ProjectiveLine.affinePoint (functionFieldRingHom baseField source) element) :
    (morphism.stalkMap (genericPoint source)).hom.FormallyUnramified := by
  letI : Algebra baseField source.functionField :=
    (functionFieldRingHom baseField source).toAlgebra
  letI : Algebra baseField
      ((projectiveLine baseField).presheaf.stalk (morphism (genericPoint source))) :=
    (((Scheme.ΓSpecIso (.of baseField)).inv ≫
      (projectiveLineToSpec baseField).appTop ≫
        (projectiveLine baseField).presheaf.germ ⊤
          (morphism (genericPoint source)) trivial).hom).toAlgebra
  letI : Algebra ((projectiveLine baseField).presheaf.stalk (morphism (genericPoint source)))
      source.functionField := (morphism.stalkMap (genericPoint source)).hom.toAlgebra
  have naturality :
      (source ↘ Spec (.of baseField)).appTop ≫
          source.presheaf.germ ⊤ (genericPoint source) trivial =
        ((projectiveLineToSpec baseField).appTop ≫
          (projectiveLine baseField).presheaf.germ ⊤
            (morphism (genericPoint source)) trivial) ≫
              morphism.stalkMap (genericPoint source) := by
    rw [Category.assoc, Scheme.Hom.germ_stalkMap, ← Category.assoc]
    rw [← HomIsOver.comp_over (f := morphism) (S := Spec (.of baseField))]
    rfl
  have : IsScalarTower baseField
      ((projectiveLine baseField).presheaf.stalk (morphism (genericPoint source)))
      source.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change (((Scheme.ΓSpecIso (.of baseField)).inv ≫
      (source ↘ Spec (.of baseField)).appTop) ≫
        source.presheaf.germ ⊤ (genericPoint source) trivial).hom =
      (((Scheme.ΓSpecIso (.of baseField)).inv ≫
        (projectiveLineToSpec baseField).appTop ≫
          (projectiveLine baseField).presheaf.germ ⊤
            (morphism (genericPoint source)) trivial) ≫
              morphism.stalkMap (genericPoint source)).hom
    congr 1
    simpa only [Category.assoc] using congrArg
      (fun homomorphism ↦ (Scheme.ΓSpecIso (.of baseField)).inv ≫ homomorphism) naturality
  exact Algebra.FormallyUnramified.of_finrank_kaehlerDifferential_eq_one
    (finrank_kaehlerDifferential_functionField (source ↘ Spec (.of baseField)) 1
      (Scheme.ΓSpecIso (.of baseField)).symm.commRingCatIsoToRingEquiv rfl)
    nonzero (mem_range_stalkMap_genericPoint_of_affinePoint element morphism agreement)

/-- Every smooth proper integral curve admits a finite flat morphism to the
projective line, formally unramified at every point whose local ring is a field. -/
theorem exists_isFinite_flat_hom_projectiveLine
    [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
    [IsProper (source ↘ Spec (.of baseField))] :
    ∃ morphism : source ⟶ projectiveLine baseField,
      morphism.IsOver (Spec (.of baseField)) ∧ IsFinite morphism ∧ Flat morphism ∧
        LocallyOfFinitePresentation morphism ∧
          ∀ point : source, IsField (source.presheaf.stalk point) →
            (morphism.stalkMap point).hom.FormallyUnramified := by
  letI : SmoothOfRelativeDimension 1
      (projectiveLine baseField ↘ Spec (.of baseField)) :=
    ProjectiveLine.smoothOfRelativeDimension_toSpec baseField
  letI : IsProper (projectiveLine baseField ↘ Spec (.of baseField)) :=
    ProjectiveLine.isProper_toSpec baseField
  letI : Field source.functionField := inferInstanceAs (Field source.functionField)
  obtain ⟨element, transcendental, nonzero⟩ :=
    exists_separating_functionField_of_isProper (baseField := baseField) (scheme := source)
  have generic_structure : source.fromSpecFunctionField ≫ source ↘ Spec (.of baseField) =
      Spec.map (CommRingCat.ofHom (functionFieldRingHom baseField source)) := by
    apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality]
    ext coefficient
    simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, functionFieldRingHom]
    rfl
  have over_base :
      ProjectiveLine.affinePoint (functionFieldRingHom baseField source) element ≫
          projectiveLineToSpec baseField =
        source.fromSpecFunctionField ≫ source ↘ Spec (.of baseField) := by
    rw [ProjectiveLine.affinePoint_toSpec, generic_structure]
  obtain ⟨morphism, over, finite, _, flat, presentation, agreement⟩ :=
    exists_isFinite_flat_hom_of_functionField (baseField := baseField)
      (source := source) (target := projectiveLine baseField)
      (ProjectiveLine.affinePoint (functionFieldRingHom baseField source) element) over_base
      (ProjectiveLine.not_isClosed_affinePoint (extensionField := source.functionField)
        (functionFieldRingHom baseField source) element transcendental)
  letI : morphism.IsOver (Spec (.of baseField)) := over
  refine ⟨morphism, over, finite, flat, presentation, fun point field ↦ ?_⟩
  have dimension_bound : topologicalKrullDim source ≤ 1 := by
    exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension
      (source ↘ Spec (.of baseField)) 1
  obtain rfl : point = genericPoint source := eq_genericPoint_of_not_isClosed dimension_bound
    fun closed ↦ by
      have dimension := ringKrullDim_stalk_eq_one_of_isClosed
        (source ↘ Spec (.of baseField)) closed
      rw [ringKrullDim_eq_zero_of_isField field] at dimension
      exact zero_ne_one dimension
  exact formallyUnramified_stalkMap_genericPoint_of_affinePoint element nonzero morphism agreement

end Scheme

namespace Curve

/-- A smooth geometrically irreducible curve has integral underlying scheme. -/
instance isIntegral {baseField : Type u} [Field baseField] (curve : Curve baseField) :
    IsIntegral curve.carrier.left := by
  have : IrreducibleSpace curve.carrier.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := curve.carrier.hom)
  letI (point : curve.carrier.left) :
      IsRegularLocalRing (curve.carrier.left.presheaf.stalk point) :=
    SmoothOfRelativeDimension.isRegularLocalRing_stalk curve.carrier.hom 1 point
  have : IsReduced curve.carrier.left := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- A smooth proper geometrically irreducible curve admits a finite flat
morphism over the ground field to the native projective line. It is locally of
finite presentation and formally unramified wherever the source stalk is a field. -/
theorem exists_isFinite_flat_hom_projectiveLine {baseField : Type u} [Field baseField]
    (curve : Curve baseField) :
    ∃ morphism : curve.carrier ⟶ projectiveLineOver baseField,
      IsFinite morphism.left ∧ Flat morphism.left ∧
        LocallyOfFinitePresentation morphism.left ∧
          ∀ point : curve.carrier.left, IsField (curve.carrier.left.presheaf.stalk point) →
            (morphism.left.stalkMap point).hom.FormallyUnramified := by
  letI : curve.carrier.left.Over (Spec (.of baseField)) := ⟨curve.carrier.hom⟩
  letI : SmoothOfRelativeDimension 1
      (curve.carrier.left ↘ Spec (.of baseField)) := curve.smoothOfRelativeDimension
  letI : IsProper (curve.carrier.left ↘ Spec (.of baseField)) := curve.isProper
  obtain ⟨morphism, over, finite, flat, presentation, unramified⟩ :=
    Scheme.exists_isFinite_flat_hom_projectiveLine
      (baseField := baseField) (source := curve.carrier.left)
  letI : morphism.IsOver (Spec (.of baseField)) := over
  exact ⟨Over.homMk morphism (HomIsOver.comp_over (f := morphism) (S := Spec (.of baseField))),
    finite, flat, presentation, unramified⟩

end Curve

end AlgebraicGeometry
