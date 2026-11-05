import Jacobian.AlgebraicGeometry.Curve.FiniteSetRegularFunction
import Jacobian.AlgebraicGeometry.Curve.SeparatingFiniteMap
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affine neighborhoods of finite sets on smooth proper curves

A transcendental rational function defines a finite flat map to the projective
line. If it is regular at a point of the curve, separated valuative uniqueness
puts that point in the inverse image of the standard affine chart. Choosing the
function to be regular on a finite set therefore gives one affine open containing
that set, over an arbitrary ground field and without a rational-point hypothesis.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Scheme

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
variable [source.Over (Spec (.of baseField))] [IsIntegral source]

/-- A specified transcendental rational function gives a finite flat map to the
projective line, retaining the equation for its generic affine coordinate. -/
theorem exists_isFinite_flat_hom_projectiveLine_of_transcendental
    [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
    [IsProper (source ↘ Spec (.of baseField))] (element : source.functionField)
    (transcendental : letI := (functionFieldRingHom baseField source).toAlgebra;
      Transcendental baseField element) :
    ∃ morphism : source ⟶ projectiveLine baseField,
      morphism.IsOver (Spec (.of baseField)) ∧ IsFinite morphism ∧ Surjective morphism ∧
        Flat morphism ∧ LocallyOfFinitePresentation morphism ∧
          source.fromSpecFunctionField ≫ morphism =
            ProjectiveLine.affinePoint (functionFieldRingHom baseField source) element := by
  letI : SmoothOfRelativeDimension 1
      (projectiveLine baseField ↘ Spec (.of baseField)) :=
    ProjectiveLine.smoothOfRelativeDimension_toSpec baseField
  letI : IsProper (projectiveLine baseField ↘ Spec (.of baseField)) :=
    ProjectiveLine.isProper_toSpec baseField
  letI : Field source.functionField := inferInstanceAs (Field source.functionField)
  have over_base :
      ProjectiveLine.affinePoint (functionFieldRingHom baseField source) element ≫
          projectiveLineToSpec baseField =
        source.fromSpecFunctionField ≫ source ↘ Spec (.of baseField) := by
    rw [ProjectiveLine.affinePoint_toSpec]
    change Spec.map ((source ↘ Spec (.of baseField)).structureStalk (genericPoint source)) = _
    exact Hom.Spec_map_structureStalk _ _
  exact exists_isFinite_flat_hom_of_functionField (baseField := baseField)
    (source := source) (target := projectiveLine baseField)
    (ProjectiveLine.affinePoint (functionFieldRingHom baseField source) element) over_base
    (ProjectiveLine.not_isClosed_affinePoint (extensionField := source.functionField)
      (functionFieldRingHom baseField source) element transcendental)

/-- A finite-map coordinate regular at a point forces its image into the standard
affine chart of the projective line. -/
theorem mem_chart_zero_of_mem_range_stalk
    [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
    (element : source.functionField) (morphism : source ⟶ projectiveLine baseField)
    [morphism.IsOver (Spec (.of baseField))]
    (agreement : source.fromSpecFunctionField ≫ morphism =
      ProjectiveLine.affinePoint (functionFieldRingHom baseField source) element)
    {point : source}
    (regular : element ∈ Set.range (algebraMap (source.presheaf.stalk point) source.functionField)) :
    morphism point ∈ ProjectiveLine.chart baseField 0 := by
  obtain ⟨localCoordinate, rfl⟩ := regular
  letI : ValuationRing (source.presheaf.stalk point) :=
    valuationRing_stalk (source ↘ Spec (.of baseField)) point
  let localRing := source.presheaf.stalk point
  let functionField := source.functionField
  let specialization : localRing ⟶ functionField :=
    source.presheaf.stalkSpecializes (genericPoint_specializes point)
  have specialization_eq : Spec.map specialization ≫ source.fromSpecStalk point =
      source.fromSpecFunctionField := SpecMap_stalkSpecializes_fromSpecStalk _
  let localBase : Spec localRing ⟶ Spec (.of baseField) :=
    source.fromSpecStalk point ≫ source ↘ Spec (.of baseField)
  let firstLift : Spec localRing ⟶ projectiveLine baseField :=
    source.fromSpecStalk point ≫ morphism
  let secondLift : Spec localRing ⟶ projectiveLine baseField :=
    ProjectiveLine.affinePoint ((source ↘ Spec (.of baseField)).structureStalk point).hom
      localCoordinate
  have morphism_over : morphism ≫ projectiveLineToSpec baseField =
      source ↘ Spec (.of baseField) :=
    HomIsOver.comp_over (f := morphism) (S := Spec (.of baseField))
  have square : CommSq (source.fromSpecFunctionField ≫ morphism)
      (Spec.map specialization) (projectiveLineToSpec baseField) localBase := ⟨by
    rw [Category.assoc, morphism_over, ← specialization_eq, Category.assoc]⟩
  have first_generic : Spec.map specialization ≫ firstLift =
      source.fromSpecFunctionField ≫ morphism := by
    rw [← specialization_eq, Category.assoc]
  have second_generic : Spec.map specialization ≫ secondLift =
      source.fromSpecFunctionField ≫ morphism := by
    rw [agreement]
    have coefficients_eq : specialization.hom.comp
        ((source ↘ Spec (.of baseField)).structureStalk point).hom =
          functionFieldRingHom baseField source := by
      change (((source ↘ Spec (.of baseField)).structureStalk point) ≫ specialization).hom = _
      rw [Hom.structureStalk_stalkSpecializes]
      rfl
    have coordinate_eq : specialization.hom localCoordinate =
        algebraMap (source.presheaf.stalk point) source.functionField localCoordinate := by
      rfl
    dsimp only [secondLift, functionField, localRing]
    change Spec.map (CommRingCat.ofHom specialization.hom) ≫
        ProjectiveLine.affinePoint
          ((source ↘ Spec (.of baseField)).structureStalk point).hom localCoordinate =
      ProjectiveLine.affinePoint (functionFieldRingHom baseField source)
        (algebraMap (source.presheaf.stalk point) source.functionField localCoordinate)
    rw [← coordinate_eq, ← coefficients_eq]
    exact ProjectiveLine.SpecMap_affinePoint
      ((source ↘ Spec (.of baseField)).structureStalk point).hom specialization.hom localCoordinate
  have uniqueness : ValuativeCriterion.Uniqueness (projectiveLineToSpec baseField) :=
    IsSeparated.valuativeCriterion _
  have first_over : firstLift ≫ projectiveLineToSpec baseField = localBase := by
    change (source.fromSpecStalk point ≫ morphism) ≫ projectiveLineToSpec baseField = _
    rw [Category.assoc, morphism_over]
  have second_over : secondLift ≫ projectiveLineToSpec baseField = localBase := by
    refine (ProjectiveLine.affinePoint_toSpec
      ((source ↘ Spec (.of baseField)).structureStalk point).hom localCoordinate).trans ?_
    simpa only [CommRingCat.ofHom_hom] using
      Hom.Spec_map_structureStalk (source ↘ Spec (.of baseField)) point
  have lifts_eq : firstLift = secondLift := by
    letI : Subsingleton square.LiftStruct :=
      uniqueness ⟨localRing, functionField, source.fromSpecFunctionField ≫ morphism, localBase, square⟩
    let first : square.LiftStruct := ⟨firstLift, first_generic, first_over⟩
    let second : square.LiftStruct := ⟨secondLift, second_generic, second_over⟩
    exact congrArg CommSq.LiftStruct.l (Subsingleton.elim first second)
  have point_image : morphism point = secondLift (IsLocalRing.closedPoint localRing) := by
    rw [← lifts_eq]
    exact congrArg morphism Scheme.fromSpecStalk_closedPoint.symm
  rw [point_image]
  change ProjectiveLine.chartMorphism baseField 0 _ ∈ ProjectiveLine.chart baseField 0
  exact ((ProjectiveLine.chartSpecIso baseField 0).inv _).property

end Scheme

/-- Every finite set on a smooth proper integral curve over a field is contained
in an affine open. The affine neighborhood is the inverse image of a standard
projective-line chart under a finite morphism with a controlled rational coordinate. -/
theorem exists_affineOpens_forall_mem_of_smooth_integral_curve
    {baseField : Type u} [Field baseField] {source : Scheme.{u}}
    (structureMap : source ⟶ Spec (.of baseField)) [IsIntegral source]
    [SmoothOfRelativeDimension 1 structureMap] [IsProper structureMap] (points : Finset source) :
    ∃ neighborhood : source.affineOpens, ∀ point ∈ points, point ∈ neighborhood.1 := by
  letI : source.Over (Spec (.of baseField)) := ⟨structureMap⟩
  letI : SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 structureMap)
  letI : IsProper (source ↘ Spec (.of baseField)) := inferInstanceAs (IsProper structureMap)
  obtain ⟨element, transcendental, regular⟩ := Scheme.exists_transcendental_mem_range_stalk
    (baseField := baseField) (scheme := source) points
  obtain ⟨morphism, over, finite, _, _, _, agreement⟩ :=
    Scheme.exists_isFinite_flat_hom_projectiveLine_of_transcendental
      (baseField := baseField) (source := source) element transcendental
  letI : IsFinite morphism := finite
  letI : morphism.IsOver (Spec (.of baseField)) := over
  have affine_chart : IsAffineOpen (ProjectiveLine.chart baseField 0) :=
    Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X _ _) (by decide)
  exact ⟨⟨morphism ⁻¹ᵁ ProjectiveLine.chart baseField 0, affine_chart.preimage morphism⟩,
    fun point membership ↦ Scheme.mem_chart_zero_of_mem_range_stalk
      element morphism agreement (regular point membership)⟩

end AlgebraicGeometry
