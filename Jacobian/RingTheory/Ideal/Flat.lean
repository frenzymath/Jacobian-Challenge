import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.RingHom.Flat

/-!
# Flat extension of intersections of ideals

Extension of ideals along a flat algebra commutes with finite intersections.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

namespace Ideal

/-- Extension of ideals along a flat ring map commutes with binary intersections. The ideal
`I ⊓ J` is the kernel of `R → R ⧸ I × R ⧸ J`, and base change along `S` preserves this
kernel. -/
theorem map_inf_of_flat (I J : Ideal R) :
    (I ⊓ J).map (algebraMap R S) = I.map (algebraMap R S) ⊓ J.map (algebraMap R S) := by
  refine le_antisymm (map_inf_le _) fun x hx ↦ ?_
  let f : R →ₗ[R] (R ⧸ I) × (R ⧸ J) := I.mkQ.prod J.mkQ
  have hker : LinearMap.ker f = I ⊓ J := by
    ext r; simp [f]
  have hvan (K : Ideal R) (y : S) (hy : y ∈ K.map (algebraMap R S)) :
      y ⊗ₜ[R] (Submodule.Quotient.mk 1 : R ⧸ K) = 0 := by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      rw [Algebra.algebraMap_eq_smul_one, smul_tmul, ← Submodule.Quotient.mk_smul, smul_eq_mul,
        mul_one, (Submodule.Quotient.mk_eq_zero K).mpr hk, tmul_zero]
    | zero => simp
    | add y z _ _ hy hz => rw [add_tmul, hy, hz, add_zero]
    | smul a y _ hy => rw [smul_eq_mul, ← smul_eq_mul, ← smul_tmul', hy, smul_zero]
  have h1 : x ⊗ₜ[R] (1 : R) ∈ LinearMap.ker (AlgebraTensorModule.lTensor S S f) := by
    have hf : f 1 = LinearMap.inl R _ _ (Submodule.Quotient.mk 1) +
        LinearMap.inr R _ _ (Submodule.Quotient.mk 1) := by
      simp [f]
    rw [LinearMap.mem_ker, AlgebraTensorModule.lTensor_tmul, hf, tmul_add,
      ← LinearMap.lTensor_tmul, ← LinearMap.lTensor_tmul, hvan I x hx.1, hvan J x hx.2,
      map_zero, map_zero, add_zero]
  rw [Module.Flat.ker_lTensor_eq] at h1
  obtain ⟨u, hu⟩ := h1
  have : x = AlgebraTensorModule.rid R S S (x ⊗ₜ[R] (1 : R)) := by simp
  rw [this, ← hu]
  clear hu this
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul s k =>
    have hk : (k : R) ∈ I ⊓ J := hker ▸ k.2
    simp only [AlgebraTensorModule.lTensor_tmul, Submodule.coe_subtype,
      AlgebraTensorModule.rid_tmul]
    rw [Algebra.smul_def]
    exact mul_mem_right _ _ (mem_map_of_mem _ hk)
  | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb

/-- Extension of ideals along a flat ring map commutes with finite intersections. -/
theorem map_iInf_of_flat {ι : Type*} [Finite ι] (I : ι → Ideal R) :
    (⨅ i, I i).map (algebraMap R S) = ⨅ i, (I i).map (algebraMap R S) := by
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, (s.inf I).map (algebraMap R S) =
      s.inf fun i ↦ (I i).map (algebraMap R S) by
    simpa [Finset.inf_univ_eq_iInf] using H Finset.univ
  intro s
  classical
  induction s using Finset.induction_on with
  | empty => exact map_top _
  | insert i s _ ih => rw [Finset.inf_insert, Finset.inf_insert, map_inf_of_flat, ih]

end Ideal
