import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Uniform powers in finitely generated modules

If each element of a finite module has a power multiple in a submodule, one
power works for the entire module. A finite generating set bounds the exponents.
-/

/-- If every element of a finitely generated module has a multiple by a power of `t` lying in a
submodule `N`, then a single power of `t` works for all elements. -/
theorem Submodule.exists_pow_smul_mem_of_forall {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [Module.Finite R M] (N : Submodule R M) (t : R)
    (h : ∀ m : M, ∃ n : ℕ, t ^ n • m ∈ N) : ∃ n : ℕ, ∀ m : M, t ^ n • m ∈ N := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := M)
  choose n hn using h
  refine ⟨S.sup n, fun m => ?_⟩
  have hm : m ∈ Submodule.span R (S : Set M) := hS ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx =>
    rw [← Nat.sub_add_cancel (Finset.le_sup hx : n x ≤ S.sup n), pow_add, mul_smul]
    exact N.smul_mem _ (hn x)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact N.add_mem hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact N.smul_mem a hx
