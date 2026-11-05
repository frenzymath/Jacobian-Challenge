import Jacobian.AlgebraicGeometry.Cohomology.GlobalFunctions
import Jacobian.AlgebraicGeometry.Curve.Genus
import Jacobian.AlgebraicGeometry.Modules.GlobalSection

/-!
# Euler characteristics in cohomological dimension one

When cohomology vanishes above degree one, Euler characteristic is `h⁰ - h¹`.
Positive Euler characteristic then supplies a nonzero global section. For a
proper geometrically integral scheme the structure-sheaf Euler characteristic
is `1 - genus`, giving the elementary Riemann--Roch inequality.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Only zeroth and first cohomology contribute when higher cohomology vanishes. -/
theorem eulerChar_eq_finrankH_zero_sub_finrankH_one (M : X.Modules)
    (vanishing : ∀ degree, 1 < degree → Subsingleton (M.H degree)) :
    M.eulerChar k = (M.finrankH k 0 : ℤ) - M.finrankH k 1 := by
  calc
    M.eulerChar k = ∑ degree ∈ Finset.range 2,
        (-1 : ℤ) ^ degree * (M.finrankH k degree : ℤ) := by
      refine finsum_eq_sum_of_support_subset _ fun degree supported ↦ ?_
      by_cases larger : 1 < degree
      · letI := vanishing degree larger
        exact False.elim (supported (by simp [finrankH, Module.finrank_zero_of_subsingleton]))
      · exact Finset.mem_range.mpr (by omega)
    _ = (M.finrankH k 0 : ℤ) - M.finrankH k 1 := by
      simp [Finset.sum_range_succ, sub_eq_add_neg]

/-- Positive Euler characteristic in cohomological dimension one gives a
nonzero morphism from the structure module. -/
theorem exists_nonzero_section_of_eulerChar_pos (M : X.Modules)
    (vanishing : ∀ degree, 1 < degree → Subsingleton (M.H degree))
    (positive : 0 < M.eulerChar k) : ∃ sectionMap : unit X ⟶ M, sectionMap ≠ 0 := by
  have zeroPositive : 0 < M.finrankH k 0 := by
    rw [eulerChar_eq_finrankH_zero_sub_finrankH_one (k := k) M vanishing] at positive
    omega
  letI : Nontrivial (M.H 0) := Module.nontrivial_of_finrank_pos (R := k) zeroPositive
  obtain ⟨cohomologyClass, nonzero⟩ := exists_ne (0 : M.H 0)
  let sectionValue := H.zeroLinearEquiv M cohomologyClass
  have sectionNonzero : sectionValue ≠ 0 := by
    intro zeroValue
    apply nonzero
    exact (H.zeroLinearEquiv M).injective (zeroValue.trans (map_zero _).symm)
  refine ⟨homOfGlobalSection M sectionValue, fun zeroSection ↦ ?_⟩
  have zeroValue : (homOfGlobalSection M sectionValue).app ⊤ (1 : Γ(X, ⊤)) = 0 := by
    rw [zeroSection]
    rfl
  rw [homOfGlobalSection_app_one] at zeroValue
  exact sectionNonzero (by simpa using zeroValue)

variable [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- The Euler characteristic of the structure sheaf is one minus the genus. -/
theorem eulerChar_unit_eq_one_sub_genus
    (vanishing : ∀ degree, 1 < degree → Subsingleton ((unit X).H degree)) :
    (unit X).eulerChar k = 1 - (arithmeticGenus k X : ℤ) := by
  rw [eulerChar_eq_finrankH_zero_sub_finrankH_one (k := k) (unit X) vanishing,
    finrankH_unit_zero_eq_one (k := k)]
  rfl

/-- The elementary Riemann--Roch inequality follows from nonnegativity of `h¹`. -/
theorem degree_add_one_sub_genus_le_finrankH_zero (M : X.Modules)
    (vanishing : ∀ degree, 1 < degree → Subsingleton (M.H degree))
    (unitVanishing : ∀ degree, 1 < degree → Subsingleton ((unit X).H degree)) :
    M.degree k + 1 - (arithmeticGenus k X : ℤ) ≤ (M.finrankH k 0 : ℤ) := by
  have lineEuler := eulerChar_eq_finrankH_zero_sub_finrankH_one (k := k) M vanishing
  have unitEuler := eulerChar_unit_eq_one_sub_genus (k := k) unitVanishing
  change M.eulerChar k - (unit X).eulerChar k + 1 - (arithmeticGenus k X : ℤ) ≤ _
  rw [lineEuler, unitEuler]
  omega

end AlgebraicGeometry.Scheme.Modules
