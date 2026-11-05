import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Norms of non-zero-divisors

In a finite free algebra over a domain, multiplication by a non-zero-divisor
is injective, so its determinant is nonzero.
-/

namespace Algebra

variable {baseRing extensionRing : Type*} [CommRing baseRing] [CommRing extensionRing]
  [Algebra baseRing extensionRing]

theorem norm_ne_zero_of_mem_nonZeroDivisors [IsDomain baseRing] [Module.Free baseRing extensionRing] [Module.Finite baseRing extensionRing]
    {element : extensionRing} (hh : element ∈ nonZeroDivisors extensionRing) : Algebra.norm baseRing element ≠ 0 := by
  classical
  let basis := Module.Free.chooseBasis baseRing extensionRing
  rw [Algebra.norm_eq_matrix_det basis]
  intro h0
  obtain ⟨vector, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hv' : basis.repr (element * basis.equivFun.symm vector) = 0 := by
    ext index
    rw [← Algebra.leftMulMatrix_mulVec_repr, ← basis.equivFun_apply, basis.equivFun.apply_symm_apply]
    exact congrFun hv index
  rw [LinearEquiv.map_eq_zero_iff, mul_comm, mul_right_mem_nonZeroDivisors_eq_zero_iff hh,
    LinearEquiv.map_eq_zero_iff] at hv'
  exact hv0 hv'

end Algebra
