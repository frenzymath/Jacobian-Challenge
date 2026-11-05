import Jacobian.AlgebraicGeometry.PointedCurve.Basic
import Jacobian.AlgebraicGeometry.IdealSheaf.SectionDegree
import Jacobian.AlgebraicGeometry.Curve.LineBundleDegree

/-!
# The divisor of the marked point of a curve

The kernel ideal of the marked rational point on a smooth proper curve is
invertible. Its native Picard class has degree minus one, and its natural powers
have degree minus their exponent. The dual line bundle and the degree-one
section-divisor formula supply the sign without choosing a tensor inverse.
-/

noncomputable section

universe u

open CategoryTheory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.PointedCurve

open Scheme

variable {baseField : Type u} [Field baseField] (curve : PointedCurve baseField)

/-- The ideal of the marked rational point is an effective Cartier divisor. -/
theorem isInvertible_pointIdeal : curve.point.left.ker.IsInvertible :=
  (curve.point.left.isRelativeEffectiveCartier_ker_of_section curve.curve.carrier.hom
    (by simpa using Over.w curve.point)).1

/-- The sheaf of ideals of the marked point is an invertible module sheaf. -/
instance isInvertible_pointIdeal_toModules : curve.point.left.ker.toModules.IsInvertible :=
  curve.isInvertible_pointIdeal.isInvertible_toModules

/-- The Picard class of the literal kernel ideal of the marked rational point. -/
def pointIdealClass : curve.curve.carrier.left.Pic :=
  Pic.mk curve.point.left.ker.toModules

/-- The ideal class of the marked rational point has degree minus one. -/
@[simp]
theorem degree_pointIdealClass :
    letI : curve.curve.carrier.left.Over (Spec (.of baseField)) := ⟨curve.curve.carrier.hom⟩
    Pic.degree baseField curve.pointIdealClass = -1 := by
  letI : curve.curve.carrier.left.Over (Spec (.of baseField)) := ⟨curve.curve.carrier.hom⟩
  haveI : IsProper (curve.curve.carrier.left ↘ Spec (.of baseField)) := curve.curve.isProper
  haveI : SmoothOfRelativeDimension 1 (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
    curve.curve.smoothOfRelativeDimension
  haveI : GeometricallyIrreducible (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
    curve.curve.geometricallyIrreducible
  letI : IsIso (curve.point.left.ker.subschemeι ≫ curve.curve.carrier.hom) :=
    curve.point.left.isIso_ker_subschemeι_comp_of_section curve.curve.carrier.hom
      (by simpa using Over.w curve.point)
  have dualDegree : Pic.degree baseField curve.pointIdealClass⁻¹ = 1 := by
    change Pic.degree baseField (Pic.mk curve.point.left.ker.toModules)⁻¹ = 1
    rw [← Pic.mk_dual, Pic.degree_mk]
    exact curve.isInvertible_pointIdeal.degree_dual_toModules_eq_one curve.curve
  rw [Pic.degree_inv (k := baseField) (X := curve.curve.carrier.left)
    curve.pointIdealClass] at dualDegree
  omega

/-- The nth tensor power of the marked point's ideal class has degree minus n. -/
@[simp]
theorem degree_pointIdealClass_pow (exponent : ℕ) :
    letI : curve.curve.carrier.left.Over (Spec (.of baseField)) := ⟨curve.curve.carrier.hom⟩
    Pic.degree baseField (curve.pointIdealClass ^ exponent) = -(exponent : ℤ) := by
  letI : curve.curve.carrier.left.Over (Spec (.of baseField)) := ⟨curve.curve.carrier.hom⟩
  haveI : IsProper (curve.curve.carrier.left ↘ Spec (.of baseField)) := curve.curve.isProper
  haveI : SmoothOfRelativeDimension 1 (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
    curve.curve.smoothOfRelativeDimension
  haveI : GeometricallyIrreducible (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
    curve.curve.geometricallyIrreducible
  induction exponent with
  | zero =>
      have degreeOne := congrArg Multiplicative.toAdd
        (map_one (Pic.degreeHom (k := baseField) (X := curve.curve.carrier.left)))
      change Pic.degree baseField (1 : curve.curve.carrier.left.Pic) = 0 at degreeOne
      simpa only [pow_zero, Nat.cast_zero, neg_zero] using degreeOne
  | succ exponent inductionHypothesis =>
      rw [pow_succ, Pic.degree_mul (k := baseField) (X := curve.curve.carrier.left),
        inductionHypothesis, degree_pointIdealClass curve]
      simp only [Nat.cast_succ]
      omega

end AlgebraicGeometry.PointedCurve
