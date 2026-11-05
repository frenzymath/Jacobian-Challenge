import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Ideal.Maps

/-!
# Extension of scalars along a quotient map

Tensoring a module killed by the kernel of a surjective algebra map does not
change its underlying additive group.
-/

open TensorProduct

/-- **Tensoring with a quotient ring.** Let `φ : R →+* S` be surjective and `M` an `R`-module
killed by the kernel of `φ`. Then `m ↦ 1 ⊗ m` is a bijection `M ≃ S ⊗[R] M`. -/
lemma TensorProduct.bijective_one_tmul_of_surjective {R S M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M]
    (hφ : Function.Surjective (algebraMap R S))
    (hM : ∀ a ∈ RingHom.ker (algebraMap R S), ∀ m : M, a • m = 0) :
    Function.Bijective (fun m : M ↦ (1 : S) ⊗ₜ[R] m) := by
  let σ := Function.surjInv hφ
  have hσ (s : S) : algebraMap R S (σ s) = s := Function.surjInv_eq hφ s
  have heq {a b : R} (h : algebraMap R S a = algebraMap R S b) (m : M) : a • m = b • m := by
    rw [← sub_eq_zero, ← sub_smul]
    exact hM _ (by rw [RingHom.mem_ker, map_sub, h, sub_self]) m
  let B : S →ₗ[R] M →ₗ[R] M := LinearMap.mk₂ R (fun s m ↦ σ s • m)
    (fun s t m ↦ by rw [← add_smul]; exact heq (by simp [hσ]) m)
    (fun r s m ↦ by rw [smul_smul]; exact heq (by rw [hσ, map_mul, hσ, _root_.Algebra.smul_def]) m)
    (fun s m n ↦ smul_add _ _ _)
    (fun r s m ↦ by rw [smul_comm])
  let L := TensorProduct.lift B
  refine ⟨fun m n h ↦ ?_, fun z ↦ ?_⟩
  · have h1 (m : M) : L ((1 : S) ⊗ₜ[R] m) = m := by
      change σ 1 • m = m
      exact (heq (by simp [hσ]) m).trans (one_smul R m)
    rw [← h1 m, ← h1 n]
    exact congrArg L h
  · induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul s m =>
      refine ⟨σ s • m, ?_⟩
      change (1 : S) ⊗ₜ[R] (σ s • m) = s ⊗ₜ[R] m
      rw [← TensorProduct.smul_tmul]
      congr 1
      rw [_root_.Algebra.smul_def, mul_one, hσ]
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp [TensorProduct.tmul_add]⟩
