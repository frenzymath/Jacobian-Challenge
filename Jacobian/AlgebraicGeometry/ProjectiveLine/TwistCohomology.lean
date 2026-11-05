import Jacobian.AlgebraicGeometry.Cohomology.ProjectiveTwistHomology
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Twisting-sheaf cohomology on the projective line

The monomial complex computes the two possibly nonzero cohomology groups of a
twisting sheaf on the polynomial projective line. Its homogeneous-polynomial
descriptions give the dimension equality used in degree-one duality and a
nonzero trace form on the first cohomology of the twist of degree minus two.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe baseUniverse

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry.ProjectiveLine

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (baseField : Type baseUniverse) [Field baseField]

local notation "𝒪(" twistDegree ")" =>
  Proj.twist (homogeneousSubmodule (Fin 2) baseField) twistDegree

local instance twistCohomologyModule (twistDegree : ℤ) (degree : ℕ) :
    Module baseField ((𝒪(twistDegree)).H degree) :=
  moduleHOfSpec (Proj.projectiveSpaceOverAffineToSpec (Fin 2) baseField)
    (𝒪(twistDegree)) degree

private theorem finiteDimensional_H_twist_of_le_one (twistDegree : ℤ) (degree : ℕ)
    (degreeBound : degree ≤ 1) : FiniteDimensional baseField ((𝒪(twistDegree)).H degree) := by
  obtain ⟨comparison⟩ :=
    Proj.nonempty_H_twist_linearEquiv_homology (Fin 2) baseField twistDegree degree
  have := ProjectiveSpace.finite_monomialCechComplex_homology (n := Fin 2)
    baseField (by decide : Fintype.card (Fin 2) = 1 + 1) twistDegree degreeBound
  exact comparison.symm.finiteDimensional

/-- Degree-zero cohomology of every twist on the projective line is finite-dimensional. -/
theorem finiteDimensional_H_zero_twist (twistDegree : ℤ) :
    FiniteDimensional baseField ((𝒪(twistDegree)).H 0) :=
  finiteDimensional_H_twist_of_le_one baseField twistDegree 0 (by omega)

/-- First cohomology of every twist on the projective line is finite-dimensional. -/
theorem finiteDimensional_H_one_twist (twistDegree : ℤ) :
    FiniteDimensional baseField ((𝒪(twistDegree)).H 1) :=
  finiteDimensional_H_twist_of_le_one baseField twistDegree 1 le_rfl

/-- A negative twist has no global sections on the projective line. -/
theorem subsingleton_H_zero_twist_of_neg (twistDegree : ℤ) (negative : twistDegree < 0) :
    Subsingleton ((𝒪(twistDegree)).H 0) := by
  obtain ⟨comparison⟩ :=
    Proj.nonempty_H_twist_linearEquiv_homology (Fin 2) baseField twistDegree 0
  have := ProjectiveSpace.subsingleton_monomialCechComplex_homology_zero
    (Fin 2) baseField negative
  exact comparison.toEquiv.subsingleton

/-- Twists of degree at least minus one have no first cohomology. -/
theorem subsingleton_H_one_twist (twistDegree : ℤ) (degreeBound : -1 ≤ twistDegree) :
    Subsingleton ((𝒪(twistDegree)).H 1) := by
  obtain ⟨comparison⟩ :=
    Proj.nonempty_H_twist_linearEquiv_homology (Fin 2) baseField twistDegree 1
  have := ProjectiveSpace.subsingleton_monomialCechComplex_homology_top
    (n := Fin 2) (A := baseField) (by decide : Fintype.card (Fin 2) = 1 + 1)
    (by decide : 1 ≠ 0) degreeBound
  exact comparison.toEquiv.subsingleton

/-- The complementary twists have the dimensions predicted by degree-one duality. -/
theorem finrank_H_zero_twist_eq_dual_H_one_twist (twistDegree : ℤ) :
    Module.finrank baseField ((𝒪(-twistDegree - 2)).H 0) =
      Module.finrank baseField (Module.Dual baseField ((𝒪(twistDegree)).H 1)) := by
  have := finiteDimensional_H_one_twist baseField twistDegree
  rw [Subspace.dual_finrank_eq]
  rcases lt_or_ge twistDegree (-1) with negative | nonnegative
  · obtain ⟨topComparison⟩ := Proj.nonempty_H_twist_top_equiv_dual (Fin 2) baseField
      1 (by simp) twistDegree (by omega)
    have := Module.Finite.iff_fg.2
      (MvPolynomial.homogeneousSubmodule_fg (Fin 2) baseField (-twistDegree - 2).toNat)
    rw [topComparison.finrank_eq, Subspace.dual_finrank_eq]
    have polynomialDegree : (-twistDegree - ((1 : ℕ) : ℤ) - 1).toNat =
        (-twistDegree - 2).toNat := by congr 1; omega
    rw [polynomialDegree]
    have complementaryDegree : -twistDegree - 2 = ((-twistDegree - 2).toNat : ℤ) := by omega
    rw [complementaryDegree]
    obtain ⟨zeroComparison⟩ := Proj.nonempty_H_zero_twist_equiv (Fin 2) baseField
      1 (by simp) (-twistDegree - 2).toNat
    exact zeroComparison.finrank_eq
  · have := subsingleton_H_one_twist baseField twistDegree nonnegative
    have := subsingleton_H_zero_twist_of_neg baseField (-twistDegree - 2) (by omega)
    rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]

/-- The dual of the first cohomology of the degree-minus-two twist has dimension one. -/
theorem finrank_dual_H_one_twist_neg_two :
    Module.finrank baseField (Module.Dual baseField ((𝒪(-2)).H 1)) = 1 := by
  rw [← finrank_H_zero_twist_eq_dual_H_one_twist baseField (-2)]
  change Module.finrank baseField ((𝒪(((0 : ℕ) : ℤ))).H 0) = 1
  obtain ⟨comparison⟩ := Proj.nonempty_H_zero_twist_equiv (Fin 2) baseField 1 (by simp) 0
  rw [comparison.finrank_eq,
    Module.finrank_eq_nat_card_basis (ProjectiveSpace.homogeneousSubmoduleBasis _ baseField 0)]
  letI : Unique {exponents : Fin 2 →₀ ℕ | exponents.degree = 0} :=
    ⟨⟨⟨0, by simp⟩⟩, fun exponents ↦
      Subtype.ext ((Finsupp.degree_eq_zero_iff _).1 exponents.2)⟩
  exact Nat.card_unique

/-- A nonzero trace form exists on the first cohomology of the degree-minus-two twist. -/
theorem exists_dual_H_one_twist_neg_two_ne_zero :
    ∃ traceForm : Module.Dual baseField ((𝒪(-2)).H 1), traceForm ≠ 0 := by
  have := finiteDimensional_H_one_twist baseField (-2)
  have := Module.nontrivial_of_finrank_eq_succ (finrank_dual_H_one_twist_neg_two baseField)
  exact exists_ne 0

end AlgebraicGeometry.ProjectiveLine
