import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Quasi-finite regular quotients

Quotienting a finite-type algebra of dimension at most one by a non-zerodivisor gives a
zero-dimensional finite-type algebra, hence an algebra finite over the ground field.
-/

open scoped nonZeroDivisors

/-- A finite-type algebra of dimension at most one modulo a regular element is quasi-finite
over its ground field. -/
lemma RingHom.quasiFinite_comp_of_regular_quotient {K B C : Type*} [CommRing K]
    [CommRing B] [CommRing C] (hK : IsField K) (φ : K →+* B) (hφ : φ.FiniteType)
    (hdim : ringKrullDim B ≤ 1) (q : B →+* C) (hq : Function.Surjective q) {f : B}
    (hf : f ∈ nonZeroDivisors B) (hqf : q f = 0) : (q.comp φ).QuasiFinite := by
  let := hK.toField
  let := (q.comp φ).toAlgebra
  have : Algebra.FiniteType K C := (RingHom.FiniteType.of_surjective q hq).comp hφ
  have h := (ringKrullDim_succ_le_of_surjective q hq hf hqf).trans hdim
  have : Ring.KrullDimLE 0 C := by
    rw [Ring.krullDimLE_iff]
    cases hC : ringKrullDim C with
    | bot => exact bot_le
    | coe n =>
      rw [hC] at h
      norm_cast at h ⊢
      cases n with
      | top => simp at h
      | coe m =>
        norm_cast at h ⊢
        omega
  have := (Module.finite_iff_krullDimLE_zero K C).mpr this
  exact (inferInstance : Algebra.QuasiFinite K C)

