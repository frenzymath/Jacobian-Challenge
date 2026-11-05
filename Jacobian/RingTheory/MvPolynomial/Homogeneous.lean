import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The degree-zero ring of multivariate polynomials

For the total-degree grading, the degree-zero ring consists of constants.
The variables generate the polynomial ring as an algebra over this ring;
in finitely many variables, this algebra is of finite type.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (σ : Type*) (R : Type*) [CommRing R]

/-- Constants identify the coefficient ring with the degree-zero ring. -/
noncomputable def homogeneousSubmoduleZeroEquiv : R ≃+* homogeneousSubmodule σ R 0 where
  toFun r := ⟨C r, isHomogeneous_C σ r⟩
  invFun p := coeff 0 (p : MvPolynomial σ R)
  left_inv r := by simp
  right_inv p := Subtype.ext
    (totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous _).mpr p.2)).symm
  map_mul' r s := Subtype.ext (by simp)
  map_add' r s := Subtype.ext (by simp)

@[simp]
lemma coe_homogeneousSubmoduleZeroEquiv (r : R) :
    (homogeneousSubmoduleZeroEquiv σ R r : MvPolynomial σ R) = C r :=
  rfl

/-- The variables generate the polynomial algebra over its degree-zero ring. -/
lemma adjoin_range_X_eq_top :
    Algebra.adjoin (homogeneousSubmodule σ R 0) (Set.range (X : σ → MvPolynomial σ R)) = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C r => exact Subalgebra.algebraMap_mem _ (homogeneousSubmoduleZeroEquiv σ R r)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

/-- In finitely many variables, the polynomial algebra is of finite type over its
degree-zero ring. -/
instance instFiniteTypeHomogeneousSubmoduleZero [Finite σ] :
    Algebra.FiniteType (homogeneousSubmodule σ R 0) (MvPolynomial σ R) := by
  classical
  cases nonempty_fintype σ
  refine ⟨⟨Finset.univ.image (X : σ → MvPolynomial σ R), ?_⟩⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, adjoin_range_X_eq_top]

end MvPolynomial
