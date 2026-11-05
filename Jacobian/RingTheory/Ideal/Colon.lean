import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Tactic.LinearCombination

/-!
# Colon ideals and localization

Colon by a finitely generated ideal commutes with localization. Cancellation of
regular principal ideals computes the colon `(v g) : (v)` as `(g)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- For a non-zerodivisor `v`, the colon ideal `(v g) : (v)` is `(g)`. -/
lemma Ideal.colon_span_singleton_mul {B : Type*} [CommRing B] {v : B} (hv : v ∈ nonZeroDivisors B)
    (g : B) : (Ideal.span {v * g}).colon (Ideal.span {v} : Set B) = Ideal.span {g} := by
  ext c
  rw [Submodule.mem_colon, Ideal.mem_span_singleton']
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (h v (Ideal.mem_span_singleton_self v))
    refine ⟨r, ?_⟩
    have : v * (r * g - c) = 0 := by rw [smul_eq_mul] at hr; linear_combination hr
    exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hv).1 _ this)
  · rintro ⟨r, rfl⟩ s hs
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hs
    exact Ideal.mem_span_singleton'.mpr ⟨r * t, by rw [smul_eq_mul]; ring⟩

/-- Colon by a finitely generated ideal commutes with localization. -/
lemma Ideal.map_colon_of_isLocalization {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (I J : Ideal A) (hJ : J.FG) :
    (I.colon (J : Set A)).map (algebraMap A B) =
      (I.map (algebraMap A B)).colon (J.map (algebraMap A B) : Set B) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Submodule.mem_colon]
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      rw [smul_eq_mul, ← map_mul]
      exact Ideal.mem_map_of_mem _ (Submodule.mem_colon.mp ha j hj)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Ideal.mul_mem_left _ c hx
  · intro b hb
    obtain ⟨t, rfl⟩ := hJ
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M b
    have h (j : A) (hj : j ∈ t) : ∃ m ∈ M, m * (a * j) ∈ I := by
      rw [← IsLocalization.mk'_mem_map_algebraMap_iff M B I (a * j) s,
        IsLocalization.mk'_eq_mul_mk'_one,
        mul_comm a j, map_mul, mul_assoc, ← IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
      exact Submodule.mem_colon.mp hb _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hj))
    choose! m hmM hm using h
    rw [IsLocalization.mk'_mem_map_algebraMap_iff M B]
    refine ⟨∏ j ∈ t, m j, Submonoid.prod_mem M fun j hj ↦ hmM j hj, ?_⟩
    rw [Submodule.mem_colon]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      classical
      have e : (∏ j ∈ t, m j) * a * x = (∏ j ∈ t.erase x, m j) * (m x * (a * x)) := by
        rw [← Finset.mul_prod_erase t m hx]
        ring
      rw [smul_eq_mul, e]
      exact Ideal.mul_mem_left _ _ (hm x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Ideal.mul_mem_left _ c hx
