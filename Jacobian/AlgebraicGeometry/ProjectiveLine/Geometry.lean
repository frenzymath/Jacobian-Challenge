import Jacobian.AlgebraicGeometry.Curve.LocalRing
import Jacobian.AlgebraicGeometry.Geometrically.Irreducible
import Jacobian.AlgebraicGeometry.ProjectiveLine.Charts
import Jacobian.RingTheory.RegularLocalRing.Domain
import Jacobian.RingTheory.Smooth.Polynomial
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# Smoothness and geometric irreducibility of the projective line

The standard affine charts show that the projective line is smooth of relative
dimension one. Their nonempty intersection makes the first chart dense, so the
projective line over a field is irreducible. Regular local rings then give its
reducedness and integrality. The polynomial affine charts are geometrically
irreducible; density of a chart then gives geometric irreducibility of the
projective line over every field.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

variable (baseField : Type u) [Field baseField]

/-- The projective line is a scheme over its coefficient field. -/
instance overSpec : (projectiveLine baseField).Over (Spec (.of baseField)) :=
  ⟨projectiveLineToSpec baseField⟩

/-- The projective line is smooth of relative dimension one. -/
instance smoothOfRelativeDimension_toSpec :
    SmoothOfRelativeDimension 1 (projectiveLineToSpec baseField) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top (chart baseField) (iSup_chart_eq_top baseField)
  intro coordinate
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)
    (chartSpecIso baseField coordinate).inv]
  change SmoothOfRelativeDimension 1
    (chartMorphism baseField coordinate ≫ projectiveLineToSpec baseField)
  rw [chartMorphism_toSpec,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  have cardinality : Nat.card {index : Fin 2 // index ≠ coordinate} = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap
    (R := baseField) (S := MvPolynomial {index : Fin 2 // index ≠ coordinate} baseField)
    (n := 1)).2 (by
      rw [← cardinality]
      infer_instance)

/-- The projective line is irreducible: its two irreducible affine charts meet. -/
instance irreducibleSpace : IrreducibleSpace (projectiveLine baseField) := by
  let evaluation : MvPolynomial (Fin 2) baseField →+* Γ(Spec (.of baseField), ⊤) :=
    MvPolynomial.eval₂Hom (Scheme.ΓSpecIso (.of baseField)).inv.hom (fun _ ↦ 1)
  have spans :
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)).toIdeal.map
        evaluation = ⊤ := by
    rw [MvPolynomial.toIdeal_irrelevant_homogeneousSubmodule, Ideal.map_span,
      ← Set.range_comp]
    apply Ideal.eq_top_of_isUnit_mem (x := 1)
    · exact Ideal.subset_span ⟨0, by simp [evaluation]⟩
    · exact isUnit_one
  let intersectionPoint : projectiveLine baseField :=
    Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
      evaluation spans (IsLocalRing.closedPoint baseField)
  have intersection_mem (coordinate : Fin 2) :
      intersectionPoint ∈ chart baseField coordinate := by
    change IsLocalRing.closedPoint baseField ∈
      Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
        evaluation spans ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
            (MvPolynomial.X coordinate)
    rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ (by decide)
      (MvPolynomial.isHomogeneous_X _ _)]
    simp [evaluation, Scheme.basicOpen_of_isUnit _ isUnit_one]
  have irreducible_chart (coordinate : Fin 2) :
      IsIrreducible (chart baseField coordinate : Set (projectiveLine baseField)) := by
    have chart_surjective : Function.Surjective (chartSpecIso baseField coordinate).inv :=
      (chartSpecIso baseField coordinate).inv.homeomorph.surjective
    have range_eq : Set.range (chartMorphism baseField coordinate) =
        (chart baseField coordinate : Set (projectiveLine baseField)) := by
      rw [chartMorphism, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr chart_surjective,
        Set.image_univ, Scheme.Opens.range_ι]
    rw [← range_eq]
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ
        (Spec (.of (MvPolynomial {index : Fin 2 // index ≠ coordinate} baseField)))).image
          _ (chartMorphism baseField coordinate).continuous.continuousOn
  have dense_first : closure (chart baseField 0 : Set (projectiveLine baseField)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro point
    have in_chart : ∃ coordinate, point ∈ chart baseField coordinate := by
      apply TopologicalSpace.Opens.mem_iSup.mp
      rw [iSup_chart_eq_top]
      trivial
    obtain ⟨coordinate, membership⟩ := in_chart
    fin_cases coordinate
    · exact subset_closure membership
    · have included := subset_closure_inter_of_isPreirreducible_of_isOpen
        (irreducible_chart 1).2 (chart baseField 0).isOpen
        ⟨intersectionPoint, intersection_mem 1, intersection_mem 0⟩
      exact (closure_mono Set.inter_subset_right) (included membership)
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (projectiveLine baseField))
  rw [← dense_first]
  exact (irreducible_chart 0).closure

/-- The projective line over a field is integral. -/
instance isIntegral : IsIntegral (projectiveLine baseField) := by
  letI (point : projectiveLine baseField) :
      IsRegularLocalRing ((projectiveLine baseField).presheaf.stalk point) :=
    SmoothOfRelativeDimension.isRegularLocalRing_stalk (projectiveLineToSpec baseField) 1 point
  have : IsReduced (projectiveLine baseField) := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Each standard affine chart is geometrically irreducible over the coefficient field. -/
theorem chart_geometricallyIrreducible (coordinate : Fin 2) :
    GeometricallyIrreducible
      (chartMorphism baseField coordinate ≫ projectiveLineToSpec baseField) := by
  let indices := {index : Fin 2 // index ≠ coordinate}
  let polynomialEquiv : MvPolynomial (ULift.{u} indices) baseField ≃ₐ[baseField]
      MvPolynomial indices baseField := MvPolynomial.renameEquiv baseField Equiv.ulift
  let comparison : Spec (.of (MvPolynomial indices baseField)) ≅
      Spec (.of (MvPolynomial (ULift.{u} indices) baseField)) :=
    Scheme.Spec.mapIso polynomialEquiv.toRingEquiv.toCommRingCatIso.op
  have affineGeometricallyIrreducible : GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom
        (algebraMap baseField (MvPolynomial (ULift.{u} indices) baseField)))) := by
    rw [MvPolynomial.algebraMap_eq,
      ← AffineSpace.SpecIso_inv_over (n := ULift.{u} indices) (CommRingCat.of baseField),
      MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIrreducible)]
    infer_instance
  have comparison_over : comparison.hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap baseField (MvPolynomial (ULift.{u} indices) baseField))) =
      Spec.map (CommRingCat.ofHom (algebraMap baseField (MvPolynomial indices baseField))) := by
    change Spec.map (CommRingCat.ofHom polynomialEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap baseField (MvPolynomial (ULift.{u} indices) baseField))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg
      (fun ringMap : baseField →+* MvPolynomial indices baseField ↦
        Spec.map (CommRingCat.ofHom ringMap))
      (RingHom.ext fun coefficient ↦ polynomialEquiv.commutes coefficient)
  rw [chartMorphism_toSpec, ← comparison_over,
    MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIrreducible)]
  exact affineGeometricallyIrreducible

/-- The projective line is geometrically irreducible over every field. -/
instance geometricallyIrreducible_toSpec :
    GeometricallyIrreducible (projectiveLineToSpec baseField) := by
  letI := chart_geometricallyIrreducible baseField 0
  apply GeometricallyIrreducible.of_dense_open
    (chartMorphism baseField 0) (projectiveLineToSpec baseField)
  exact IsOpenMap.denseRange_of_isPreirreducibleSpace
    (chartMorphism baseField 0) (chartMorphism baseField 0).isOpenMap

end AlgebraicGeometry.ProjectiveLine
