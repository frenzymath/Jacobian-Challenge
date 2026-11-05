import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.LinearCombination

/-!
# Quotients by products of regular principal ideals

Multiplication by a non-zerodivisor gives the short exact sequence
`0 → B/(v₂) → B/(v₁ v₂) → B/(v₁) → 0`. Over a field this computes the dimension
of the middle term as the sum of the dimensions of the outer terms.
-/

section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Quotient

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (v₁ v₂ : B)

/-- Multiplication by `v₁`, as an `R`-linear map `B ⧸ (v₂) ⟶ B ⧸ (v₁ v₂)`. -/
noncomputable def Ideal.Quotient.mulSpanSingleton :
    B ⧸ Ideal.span {v₂} →ₗ[R] B ⧸ Ideal.span {v₁ * v₂} :=
  (Submodule.mapQ (Ideal.span {v₂}) (Ideal.span {v₁ * v₂}) (LinearMap.mulLeft B v₁) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    exact Ideal.mem_span_singleton'.mpr ⟨c, by simp [mul_comm, mul_left_comm]⟩)).restrictScalars R

/-- The quotient map `B ⧸ (v₁ v₂) ⟶ B ⧸ (v₁)`, as an `R`-linear map. -/
noncomputable def Ideal.Quotient.factorSpanSingleton :
    B ⧸ Ideal.span {v₁ * v₂} →ₗ[R] B ⧸ Ideal.span {v₁} :=
  (Submodule.factor (Ideal.span_singleton_le_span_singleton.mpr
    (dvd_mul_right v₁ v₂))).restrictScalars R

lemma Ideal.Quotient.mulSpanSingleton_mk (b : B) :
    Ideal.Quotient.mulSpanSingleton (R := R) v₁ v₂ (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (v₁ * b) :=
  rfl

lemma Ideal.Quotient.factorSpanSingleton_mk (b : B) :
    Ideal.Quotient.factorSpanSingleton (R := R) v₁ v₂ (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ b :=
  rfl

lemma Ideal.Quotient.injective_mulSpanSingleton (hv : v₁ ∈ nonZeroDivisors B) :
    Function.Injective (Ideal.Quotient.mulSpanSingleton (R := R) v₁ v₂) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.mulSpanSingleton_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton'] at hx
  obtain ⟨c, hc⟩ := hx
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  refine ⟨c, ?_⟩
  have : v₁ * (c * v₂ - b) = 0 := by rw [mul_sub, ← hc]; ring
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hv).1 _ (by linear_combination this))

lemma Ideal.Quotient.surjective_factorSpanSingleton :
    Function.Surjective (Ideal.Quotient.factorSpanSingleton (R := R) v₁ v₂) := by
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ b, rfl⟩

lemma Ideal.Quotient.exact_mulSpanSingleton_factorSpanSingleton :
    Function.Exact (Ideal.Quotient.mulSpanSingleton (R := R) v₁ v₂)
      (Ideal.Quotient.factorSpanSingleton (R := R) v₁ v₂) := by
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.factorSpanSingleton_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Ideal.Quotient.mk _ c, by rw [Ideal.Quotient.mulSpanSingleton_mk, mul_comm v₁ c]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.mulSpanSingleton_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hy
    obtain ⟨d, hd⟩ := hy
    exact ⟨c - d * v₂, by linear_combination (-1 : B) * hd⟩

/-- If `v₁` is a non-zerodivisor and `B ⧸ (v₁)`, `B ⧸ (v₂)` are finite over the field `K`, then
so is `B ⧸ (v₁ v₂)`, of dimension the sum of their dimensions. -/
lemma Ideal.Quotient.finrank_span_singleton_mul {K : Type*} [Field K] [Algebra K B]
    (hv : v₁ ∈ nonZeroDivisors B) [Module.Finite K (B ⧸ Ideal.span {v₁})]
    [Module.Finite K (B ⧸ Ideal.span {v₂})] :
    Module.Finite K (B ⧸ Ideal.span {v₁ * v₂}) ∧
      Module.finrank K (B ⧸ Ideal.span {v₁ * v₂}) =
        Module.finrank K (B ⧸ Ideal.span {v₁}) + Module.finrank K (B ⧸ Ideal.span {v₂}) := by
  set μ := Ideal.Quotient.mulSpanSingleton (R := K) v₁ v₂
  set π := Ideal.Quotient.factorSpanSingleton (R := K) v₁ v₂
  have hker : LinearMap.ker π = LinearMap.range μ :=
    LinearMap.exact_iff.mp (Ideal.Quotient.exact_mulSpanSingleton_factorSpanSingleton v₁ v₂)
  have hfin : Module.Finite K (B ⧸ Ideal.span {v₁ * v₂}) := by
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker π ?_ ?_⟩
    · rw [Submodule.map_top,
        LinearMap.range_eq_top.mpr (Ideal.Quotient.surjective_factorSpanSingleton v₁ v₂)]
      exact Module.Finite.fg_top
    · rw [top_inf_eq, hker, LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map μ
  refine ⟨hfin, ?_⟩
  rw [← LinearMap.finrank_range_add_finrank_ker π, hker, LinearMap.finrank_range_of_inj
    (Ideal.Quotient.injective_mulSpanSingleton v₁ v₂ hv),
    LinearMap.range_eq_top.mpr (Ideal.Quotient.surjective_factorSpanSingleton v₁ v₂),
    finrank_top]

end Quotient
