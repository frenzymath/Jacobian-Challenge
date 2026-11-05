import Jacobian.AlgebraicGeometry.FiniteOverField
import Jacobian.AlgebraicGeometry.Modules.Discrete
import Jacobian.AlgebraicGeometry.Cohomology.Affine.Vanishing
import Jacobian.AlgebraicGeometry.Curve.Genus

/-!
# Cohomology of line bundles on finite schemes

Every line bundle on a scheme finite over a field is trivial. Its zeroth cohomology therefore
has the dimension of the ring of global functions, and its higher cohomology vanishes.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Positive-degree cohomology of a quasi-coherent module on a finite scheme vanishes. -/
theorem subsingleton_H_succ_of_isFinite [IsFinite (X ↘ Spec (.of k))]
    (M : X.Modules) [M.IsQuasicoherent] (degree : ℕ) :
    Subsingleton (M.H (degree + 1)) := by
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of k))
  exact subsingleton_H_succ_of_isAffine M degree

/-- Only zeroth cohomology contributes to the Euler characteristic of a finite scheme. -/
theorem eulerChar_eq_finrankH_zero_of_isFinite [IsFinite (X ↘ Spec (.of k))]
    (M : X.Modules) [M.IsQuasicoherent] : M.eulerChar k = M.finrankH k 0 := by
  calc
    M.eulerChar k = ∑ q ∈ Finset.range 1, (-1 : ℤ) ^ q * (M.finrankH k q : ℤ) := by
      refine finsum_eq_sum_of_support_subset _ fun q supported ↦ ?_
      by_cases zero : q = 0
      · simp [zero]
      · obtain ⟨degree, rfl⟩ := Nat.exists_eq_succ_of_ne_zero zero
        letI := subsingleton_H_succ_of_isFinite (k := k) M degree
        exact False.elim (supported (by simp [finrankH, Module.finrank_zero_of_subsingleton]))
    _ = M.finrankH k 0 := by simp

/-- Zeroth cohomology of the structure module is the vector space of global functions. -/
def H.unitZeroLinearEquiv :
    letI := (globalSectionsRingHom k (X := X)).toAlgebra
    (unit X).H 0 ≃ₗ[k] Γ(X, ⊤) := by
  letI := (globalSectionsRingHom k (X := X)).toAlgebra
  exact { (H.zeroLinearEquiv (unit X)).toAddEquiv with
      map_smul' scalar cohomologyClass :=
        (H.zeroLinearEquiv (unit X)).map_smul (globalSectionsRingHom k scalar)
          cohomologyClass }

/-- The dimension of zeroth structure-sheaf cohomology is the dimension of global functions. -/
theorem finrankH_unit_zero_eq_finrank_globalSections :
    letI := (globalSectionsRingHom k (X := X)).toAlgebra
    (unit X).finrankH k 0 = Module.finrank k Γ(X, ⊤) := by
  letI := (globalSectionsRingHom k (X := X)).toAlgebra
  exact (H.unitZeroLinearEquiv (k := k) (X := X)).finrank_eq

/-- On a finite scheme, the cohomology dimensions of a line bundle equal those of the unit. -/
theorem finrankH_eq_unit_of_isFinite [IsFinite (X ↘ Spec (.of k))]
    (M : X.Modules) [M.IsInvertible] (degree : ℕ) :
    M.finrankH k degree = (unit X).finrankH k degree := by
  obtain ⟨_, discrete⟩ := finite_and_discreteTopology_of_isFinite (X ↘ Spec (.of k))
  letI := discrete
  obtain ⟨trivialization⟩ := nonempty_iso_unit_of_discrete M
  exact finrankH_congr k trivialization degree

/-- A line bundle on a finite scheme has as many global sections as the structure module. -/
theorem finrankH_zero_eq_finrank_globalSections_of_isFinite
    [IsFinite (X ↘ Spec (.of k))] (M : X.Modules) [M.IsInvertible] :
    letI := (globalSectionsRingHom k (X := X)).toAlgebra
    M.finrankH k 0 = Module.finrank k Γ(X, ⊤) := by
  rw [finrankH_eq_unit_of_isFinite M 0]
  exact finrankH_unit_zero_eq_finrank_globalSections

/-- The Euler characteristic of a line bundle on a finite scheme is its scheme's length. -/
theorem eulerChar_eq_finrank_globalSections_of_isFinite
    [IsFinite (X ↘ Spec (.of k))] (M : X.Modules) [M.IsInvertible] :
    letI := (globalSectionsRingHom k (X := X)).toAlgebra
    M.eulerChar k = (Module.finrank k Γ(X, ⊤) : ℤ) := by
  rw [eulerChar_eq_finrankH_zero_of_isFinite M,
    finrankH_zero_eq_finrank_globalSections_of_isFinite M]

/-- The cohomological degree of every line bundle on a finite scheme is zero. -/
theorem degree_eq_zero_of_isFinite [IsFinite (X ↘ Spec (.of k))]
    (M : X.Modules) [M.IsInvertible] : M.degree k = 0 := by
  obtain ⟨_, discrete⟩ := finite_and_discreteTopology_of_isFinite (X ↘ Spec (.of k))
  letI := discrete
  obtain ⟨trivialization⟩ := nonempty_iso_unit_of_discrete M
  rw [degree_congr k trivialization, degree_unit]

end AlgebraicGeometry.Scheme.Modules
