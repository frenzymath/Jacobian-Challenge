import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Equality of homogeneous fractions

Cross multiplication gives an equality criterion for fractions in a
homogeneous localization away from one element.
-/

namespace HomogeneousLocalization

variable {ι σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → σ) [GradedRing 𝒜] {d : ι} {f : A}

/-- Equal cross products give equal homogeneous fractions with power denominators. -/
lemma Away.mk_eq_mk_of_mul_pow_eq (hf : f ∈ 𝒜 d) {n m : ℕ} {a b : A}
    (ha : a ∈ 𝒜 (n • d)) (hb : b ∈ 𝒜 (m • d)) (h : a * f ^ m = b * f ^ n) :
    Away.mk 𝒜 hf n a ha = Away.mk 𝒜 hf m b hb := by
  apply val_injective
  rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simpa [mul_comm] using h⟩

end HomogeneousLocalization
