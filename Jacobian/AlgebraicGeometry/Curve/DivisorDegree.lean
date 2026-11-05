import Jacobian.AlgebraicGeometry.Curve.Cohomology
import Jacobian.AlgebraicGeometry.GlobalSections.Rank
import Jacobian.AlgebraicGeometry.Picard.DegreeCartier

/-!
# Degree of an effective divisor on a curve

The degree of the line bundle associated to a finite effective Cartier divisor
is the length of that divisor. Finite-dimensionality and vanishing of curve
cohomology supply the hypotheses for Euler-characteristic additivity.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
  [source.Over (Spec (.of baseField))]
  [IsProper (source ↘ Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
  [GeometricallyIrreducible (source ↘ Spec (.of baseField))]

/-- The line bundle of a finite effective Cartier divisor has degree equal
to the length of its coordinate algebra. -/
theorem IsInvertible.degree_dual_toModules {divisor : source.IdealSheafData}
    (regular : divisor.IsInvertible)
    [IsFinite (divisor.subschemeι ≫ (source ↘ Spec (.of baseField)))] :
    divisor.toModulesᵛ.degree baseField =
      ((divisor.subschemeι ≫ (source ↘ Spec (.of baseField))).finrankΓ : ℤ) := by
  let curve : Curve baseField :=
    { carrier := Over.mk (source ↘ Spec (.of baseField))
      isProper := inferInstanceAs (IsProper (source ↘ Spec (.of baseField)))
      smoothOfRelativeDimension :=
        inferInstanceAs (SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField)))
      geometricallyIrreducible :=
        inferInstanceAs (GeometricallyIrreducible (source ↘ Spec (.of baseField))) }
  have : (divisor.twist (Modules.unit source)).IsInvertible := regular.isInvertible_twist _
  have (degree : ℕ) : Module.Finite baseField ((Modules.unit source).H degree) :=
    curve.hasFiniteH _ degree
  have (degree : ℕ) :
      Module.Finite baseField ((divisor.twist (Modules.unit source)).H degree) :=
    curve.hasFiniteH _ degree
  have increment := regular.degree_twist_eq_add_finrank (k := baseField)
    (Modules.unit source) 1
    (fun degree larger ↦ curve.subsingleton_H _ larger)
    (fun degree larger ↦ curve.subsingleton_H _ larger)
  rw [Modules.degree_unit] at increment
  change (𝟙_ source.Modules ⊗ divisor.toModulesᵛ).degree baseField =
    0 + ((divisor.subschemeι ≫ (source ↘ Spec (.of baseField))).finrankΓ : ℤ) at increment
  exact (Modules.degree_congr baseField (λ_ divisor.toModulesᵛ)).symm.trans
    (by simpa only [zero_add] using increment)

end AlgebraicGeometry.Scheme.IdealSheafData
