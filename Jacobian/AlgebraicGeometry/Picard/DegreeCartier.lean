import Jacobian.AlgebraicGeometry.Cohomology.Cartier
import Jacobian.AlgebraicGeometry.IdealSheaf.Twist

/-!
# Degree and effective Cartier twists

For a finite effective Cartier divisor, twisting a line bundle increases its
Euler characteristic and cohomological degree by the length of the divisor.
The hypotheses make the finite-dimensionality and boundedness required for
Euler-characteristic additivity explicit.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- An effective Cartier twist increases Euler characteristic by the length of
the divisor, whenever the two line-bundle cohomologies are finite and bounded. -/
theorem IsInvertible.eulerChar_twist_eq_add_finrank {J : X.IdealSheafData}
    (hJ : J.IsInvertible) [IsFinite (J.subschemeι ≫ (X ↘ Spec (.of k)))]
    (M : X.Modules) [M.IsInvertible]
    [∀ degree, Module.Finite k (M.H degree)]
    [∀ degree, Module.Finite k ((J.twist M).H degree)] (bound : ℕ)
    (lineVanishing : ∀ degree, bound < degree → Subsingleton (M.H degree))
    (twistVanishing : ∀ degree, bound < degree → Subsingleton ((J.twist M).H degree)) :
    letI := ((ΓSpecIso (.of k)).inv ≫
      (J.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    (J.twist M).eulerChar k = M.eulerChar k +
      (Module.finrank k Γ(J.subscheme, ⊤) : ℤ) := by
  letI := hJ.isInvertible_twist M
  let comparison := hJ.tensorTwistIso M
  letI (degree : ℕ) : Module.Finite k ((J.toModules ⊗ J.twist M).H degree) :=
    Modules.finite_H_of_iso (p := X ↘ Spec (.of k)) comparison.symm degree inferInstance
  have idealVanishing (degree : ℕ) (larger : bound < degree) :
      Subsingleton ((J.toModules ⊗ J.twist M).H degree) := by
    letI := lineVanishing degree larger
    exact (Modules.H.mapLinearEquiv comparison degree).injective.subsingleton
  have increment := J.eulerChar_eq_tensor_add_finrank (k := k) (J.twist M) bound
    idealVanishing twistVanishing
  rw [Modules.eulerChar_congr k comparison] at increment
  exact increment

/-- The degree increment of a finite effective Cartier twist is its length. -/
theorem IsInvertible.degree_twist_eq_add_finrank {J : X.IdealSheafData}
    (hJ : J.IsInvertible) [IsFinite (J.subschemeι ≫ (X ↘ Spec (.of k)))]
    (M : X.Modules) [M.IsInvertible]
    [∀ degree, Module.Finite k (M.H degree)]
    [∀ degree, Module.Finite k ((J.twist M).H degree)] (bound : ℕ)
    (lineVanishing : ∀ degree, bound < degree → Subsingleton (M.H degree))
    (twistVanishing : ∀ degree, bound < degree → Subsingleton ((J.twist M).H degree)) :
    letI := ((ΓSpecIso (.of k)).inv ≫
      (J.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    (J.twist M).degree k = M.degree k +
      (Module.finrank k Γ(J.subscheme, ⊤) : ℤ) := by
  have increment := hJ.eulerChar_twist_eq_add_finrank (k := k) M bound
    lineVanishing twistVanishing
  simp only [Modules.degree, increment]
  ring

end AlgebraicGeometry.Scheme.IdealSheafData
