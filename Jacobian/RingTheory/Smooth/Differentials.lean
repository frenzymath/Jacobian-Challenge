import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Kähler differentials of standard smooth algebras

## Main results

- `Algebra.IsStandardSmoothOfRelativeDimension.nonempty_linearEquiv_kaehlerDifferential`: if `S`
  is standard smooth of relative dimension `n` over `R`, then `Ω[S⁄R] ≃ₗ[S] (Fin n → S)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Algebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

attribute [local instance] Fintype.ofFinite in
/-- If `S` is standard smooth of relative dimension `n` over `R`, then `Ω[S⁄R]` is free of
rank `n`. -/
theorem IsStandardSmoothOfRelativeDimension.nonempty_linearEquiv_kaehlerDifferential (n : ℕ)
    [IsStandardSmoothOfRelativeDimension n R S] : Nonempty (Ω[S⁄R] ≃ₗ[S] (Fin n → S)) := by
  obtain ⟨ι, σ, _, _, ⟨P, hP⟩⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
  have hcard : Fintype.card ((Set.range P.map)ᶜ : Set ι) = n := by
    rw [Fintype.card_compl_set, ← hP, Presentation.dimension, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Set.card_range_of_injective P.map_inj]
  exact ⟨P.basisKaehler.equivFun ≪≫ₗ
    LinearEquiv.funCongrLeft S S (Fintype.equivFinOfCardEq hcard).symm⟩

end Algebra
