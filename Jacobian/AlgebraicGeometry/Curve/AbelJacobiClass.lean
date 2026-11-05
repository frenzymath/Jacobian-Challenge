import Jacobian.AlgebraicGeometry.Curve.AbelJacobiMap
import Jacobian.AlgebraicGeometry.PointedCurve.Divisor
import Jacobian.AlgebraicGeometry.Hilbert.OrderedDivisors.Picard

/-!
# The divisor class of the Abel–Jacobi family

The diagonal-minus-marked-point family, with the parameter in the second
factor, is the graph-divisor class tensored with the marked point's ideal.
The same formula holds after every change of parameter scheme.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.PointedCurve

open Scheme Hilbert.OrderedDivisors

variable {baseField : Type u} [Field baseField] (curve : PointedCurve baseField)

local instance curveOver : curve.curve.carrier.left.Over (Spec (.of baseField)) :=
  ⟨curve.curve.carrier.hom⟩

local instance curveProper : IsProper (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  curve.curve.isProper

local instance curveSmooth : SmoothOfRelativeDimension 1
    (curve.curve.carrier.left ↘ Spec (.of baseField)) := curve.curve.smoothOfRelativeDimension

local instance curveGeometricallyIrreducible : GeometricallyIrreducible
    (curve.curve.carrier.left ↘ Spec (.of baseField)) := curve.curve.geometricallyIrreducible

private theorem pic_map_toModules {source target : Scheme.{u}}
    (morphism : source ⟶ target) {ideal : target.IdealSheafData}
    {pulledIdeal : source.IdealSheafData}
    (invertible : ideal.IsInvertible) (pulledInvertible : pulledIdeal.IsInvertible)
    (ideal_eq : ideal.comap morphism = pulledIdeal) :
    letI := invertible.isInvertible_toModules
    letI := pulledInvertible.isInvertible_toModules
    Pic.map morphism (Pic.mk ideal.toModules) = Pic.mk pulledIdeal.toModules := by
  letI := invertible.isInvertible_toModules
  letI := pulledInvertible.isInvertible_toModules
  have comapInvertible : (ideal.comap morphism).IsInvertible := by
    rw [ideal_eq]
    exact pulledInvertible
  obtain ⟨comparison⟩ := invertible.nonempty_pullback_toModules_iso morphism comapInvertible
  rw [Pic.map_mk]
  exact (Pic.mk_eq_mk_iff _ _).2
    ⟨comparison ≪≫ eqToIso (congrArg IdealSheafData.toModules ideal_eq)⟩

/-- The marked ideal supplies exactly the negative degree required for tensor translation. -/
theorem degreeHom_pointIdealClass_pow (degree : ℕ) :
    Pic.degreeHom (k := baseField) (curve.pointIdealClass ^ degree) =
      Multiplicative.ofAdd (-(degree : ℤ)) := by
  exact congrArg Multiplicative.ofAdd (curve.degree_pointIdealClass_pow degree)

/-- The Abel–Jacobi family is the universal graph divisor minus the marked point. -/
theorem abelJacobiClass_eq :
    Curve.abelJacobiClass curve.curve curve.point.left (by simpa using Over.w curve.point) =
      abelClass curve.curve.carrier.hom
          (element curve.curve.carrier.hom (fun _ : Fin 1 ↦ 𝟙 curve.curve.carrier)) *
        Pic.map (pullback.fst curve.curve.carrier.hom curve.curve.carrier.hom)
          curve.pointIdealClass := by
  have point_over : curve.point.left ≫ curve.curve.carrier.hom = 𝟙 _ := Over.w curve.point
  let diagonal := Curve.diagonal curve.curve
  let constant := Curve.constantSection curve.curve curve.point.left point_over
  have diagonalInvertible := (Curve.isRelativeEffectiveCartier_diagonal curve.curve).1
  have constantInvertible :=
    (Curve.isRelativeEffectiveCartier_constantSection curve.curve curve.point.left point_over).1
  letI := diagonalInvertible.isInvertible_toModules
  letI := constantInvertible.isInvertible_toModules
  haveI : IsClosedImmersion diagonal :=
    isClosedImmersion_lift_id curve.curve.carrier.hom (𝟙 _)
      (Category.id_comp curve.curve.carrier.hom)
  haveI : IsClosedImmersion (curve.point.left ≫ curve.curve.carrier.hom) := by
    rw [point_over]
    infer_instance
  haveI : IsClosedImmersion curve.point.left :=
    IsClosedImmersion.of_comp curve.point.left curve.curve.carrier.hom
  have diagonalSquare : IsPullback diagonal (𝟙 curve.curve.carrier.left)
      (pullbackSymmetry curve.curve.carrier.hom curve.curve.carrier.hom).inv diagonal := by
    apply IsPullback.of_vert_isIso
    constructor
    simp only [Category.id_comp]
    apply pullback.hom_ext
    · dsimp only [diagonal, Curve.diagonal]
      rw [Category.assoc, pullbackSymmetry_inv_comp_fst, pullback.lift_snd, pullback.lift_fst]
    · dsimp only [diagonal, Curve.diagonal]
      rw [Category.assoc, pullbackSymmetry_inv_comp_snd, pullback.lift_fst, pullback.lift_snd]
  have diagonalKernel : diagonal.ker.comap
      (pullbackSymmetry curve.curve.carrier.hom curve.curve.carrier.hom).inv = diagonal.ker := by
    rw [← IdealSheafData.ker_fst_of_isClosedImmersion diagonal
      (pullbackSymmetry curve.curve.carrier.hom curve.curve.carrier.hom).inv,
      ← Scheme.Hom.ker_comp_of_isIso diagonalSquare.isoPullback.hom,
      diagonalSquare.isoPullback_hom_fst]
  have constantSquare : IsPullback constant curve.curve.carrier.hom
      (pullback.snd curve.curve.carrier.hom curve.curve.carrier.hom) curve.point.left := by
    apply IsPullback.flip
    refine IsPullback.of_bot (h₃₁ := curve.curve.carrier.hom) ?_ ?_
      (IsPullback.of_hasPullback curve.curve.carrier.hom curve.curve.carrier.hom).flip
    · change IsPullback curve.curve.carrier.hom
        (constant ≫ pullback.fst curve.curve.carrier.hom curve.curve.carrier.hom)
        (curve.point.left ≫ curve.curve.carrier.hom) curve.curve.carrier.hom
      rw [show constant ≫ pullback.fst curve.curve.carrier.hom curve.curve.carrier.hom = 𝟙 _ from
        Curve.constantSection_fst curve.curve curve.point.left point_over, point_over]
      exact IsPullback.of_id_snd
    · exact (pullback.lift_snd _ _ _).symm
  have constantKernel : curve.point.left.ker.comap
      (pullback.snd curve.curve.carrier.hom curve.curve.carrier.hom) = constant.ker := by
    rw [← IdealSheafData.ker_fst_of_isClosedImmersion curve.point.left
      (pullback.snd curve.curve.carrier.hom curve.curve.carrier.hom),
      ← Scheme.Hom.ker_comp_of_isIso constantSquare.isoPullback.hom,
      constantSquare.isoPullback_hom_fst]
  have diagonalClass : Pic.map
      (pullbackSymmetry curve.curve.carrier.hom curve.curve.carrier.hom).inv
      (Pic.mk diagonal.ker.toModules) = Pic.mk diagonal.ker.toModules :=
    pic_map_toModules _ diagonalInvertible diagonalInvertible diagonalKernel
  have constantClass : Pic.map (pullback.snd curve.curve.carrier.hom curve.curve.carrier.hom)
      curve.pointIdealClass =
      Pic.mk constant.ker.toModules := by
    exact pic_map_toModules _ curve.isInvertible_pointIdeal constantInvertible constantKernel
  have swappedConstantClass : Pic.map
      (pullbackSymmetry curve.curve.carrier.hom curve.curve.carrier.hom).inv
      (Pic.mk constant.ker.toModules) =
      Pic.map (pullback.fst curve.curve.carrier.hom curve.curve.carrier.hom)
        curve.pointIdealClass := by
    rw [← constantClass, ← Pic.map_comp]
    exact congrArg (fun morphism ↦ Pic.map morphism curve.pointIdealClass)
      (pullbackSymmetry_inv_comp_snd _ _)
  have graphKernel : (element curve.curve.carrier.hom
      (fun _ : Fin 1 ↦ 𝟙 curve.curve.carrier)).val = diagonal.ker := by
    change (∏ _ : Fin 1, graphIdeal curve.curve.carrier.hom (𝟙 curve.curve.carrier)) = diagonal.ker
    rw [Fin.prod_univ_one]
    apply congrArg (fun morphism : curve.curve.carrier.left ⟶
      pullback curve.curve.carrier.hom curve.curve.carrier.hom ↦ morphism.ker)
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (Curve.diagonal_fst curve.curve).symm
    · dsimp only [diagonal, Curve.diagonal]
      rw [pullback.lift_snd, pullback.lift_snd]
  have graphClass : abelClass curve.curve.carrier.hom
      (element curve.curve.carrier.hom (fun _ : Fin 1 ↦ 𝟙 curve.curve.carrier)) =
        (Pic.mk diagonal.ker.toModules)⁻¹ := by
    letI := (element curve.curve.carrier.hom
      (fun _ : Fin 1 ↦ 𝟙 curve.curve.carrier)).2.isInvertible.isInvertible_toModules
    dsimp only [abelClass]
    rw [Pic.mk_dual]
    apply congrArg Inv.inv
    exact (Pic.mk_eq_mk_iff _ _).2
      ⟨eqToIso (congrArg IdealSheafData.toModules graphKernel)⟩
  change Pic.map (pullbackSymmetry curve.curve.carrier.hom curve.curve.carrier.hom).inv
    (Pic.mk (diagonal.ker.toModulesᵛ ⊗ constant.ker.toModules)) =
      abelClass curve.curve.carrier.hom _ * _
  rw [Pic.mk_tensorObj, Pic.map_mul, Pic.mk_dual,
    ← Pic.mapHom_apply (pullbackSymmetry curve.curve.carrier.hom curve.curve.carrier.hom).inv,
    map_inv, Pic.mapHom_apply, diagonalClass, swappedConstantClass, graphClass]

/-- The graph-minus-marked-point formula over an arbitrary, possibly nonreduced, test scheme. -/
theorem abelJacobiClass_map_eq {parameter : Over (Spec (.of baseField))}
    (point : parameter ⟶ curve.curve.carrier) :
    Pic.map (baseChangeMap curve.curve.carrier.hom point)
        (Curve.abelJacobiClass curve.curve curve.point.left (by simpa using Over.w curve.point)) =
      abelClass curve.curve.carrier.hom
          (element curve.curve.carrier.hom (fun _ : Fin 1 ↦ point)) *
        Pic.map (pullback.fst curve.curve.carrier.hom parameter.hom) curve.pointIdealClass := by
  have graphRestriction : (hilbertPresheaf curve.curve.carrier.hom 1).map point.op
      (element curve.curve.carrier.hom (fun _ : Fin 1 ↦ 𝟙 curve.curve.carrier)) =
        element curve.curve.carrier.hom (fun _ : Fin 1 ↦ point) := by
    apply Subtype.ext
    change (ideal curve.curve.carrier.hom (fun _ : Fin 1 ↦ 𝟙 curve.curve.carrier)).comap
      (baseChangeMap curve.curve.carrier.hom point) =
        ideal curve.curve.carrier.hom (fun _ : Fin 1 ↦ point)
    rw [ideal_comap]
    simp only [Category.comp_id]
  have projection_eq : baseChangeMap curve.curve.carrier.hom point ≫
      pullback.fst curve.curve.carrier.hom curve.curve.carrier.hom =
        pullback.fst curve.curve.carrier.hom parameter.hom :=
    pullback.lift_fst _ _ _
  rw [curve.abelJacobiClass_eq, Pic.map_mul, pic_map_abelClass, graphRestriction,
    ← Pic.map_comp, projection_eq]

/-- Every restriction of the represented Abel–Jacobi map has the graph-minus-point class. -/
theorem abelJacobiMap_classifies_graph
    {representing : Over (Spec (.of baseField))}
    (representation : (picardFunctorDegree curve.curve.carrier.hom 0).obj.RepresentableBy
      representing) {parameter : Over (Spec (.of baseField))}
    (point : parameter ⟶ curve.curve.carrier) :
    (picardFunctorDegreeι curve.curve.carrier.hom 0).hom.app (op parameter)
        (representation.homEquiv (point ≫ Curve.abelJacobiMap curve.curve curve.point.left
          (by simpa using Over.w curve.point) representation)) =
      (toPicardFunctor curve.curve.carrier.hom).app (op parameter)
        (abelClass curve.curve.carrier.hom
            (element curve.curve.carrier.hom (fun _ : Fin 1 ↦ point)) *
          Pic.map (pullback.fst curve.curve.carrier.hom parameter.hom) curve.pointIdealClass) := by
  rw [Curve.abelJacobiMap_classifies_pullback, curve.abelJacobiClass_map_eq]

end AlgebraicGeometry.PointedCurve
