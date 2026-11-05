import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.Flat.Rank

/-!
# Dimension of finite flat algebras of constant rank

A finite flat algebra of constant local rank over a finite algebra over a field
has field dimension equal to that rank times the dimension of the base algebra.
-/

noncomputable section

set_option autoImplicit false

namespace Module

private lemma finrank_quotient_tensorProduct {baseRing moduleCarrier : Type*} [CommRing baseRing]
    [AddCommGroup moduleCarrier] [Module baseRing moduleCarrier] [Module.Finite baseRing moduleCarrier]
    [Module.Flat baseRing moduleCarrier] (maximalIdeal : Ideal baseRing) [maximalIdeal.IsMaximal] :
    Module.finrank (baseRing ⧸ maximalIdeal)
        (TensorProduct baseRing (baseRing ⧸ maximalIdeal) moduleCarrier) =
      Module.rankAtStalk moduleCarrier ⟨maximalIdeal, inferInstance⟩ := by
  let := Ideal.Quotient.field maximalIdeal
  rw [Module.rankAtStalk_eq,
    ← (TensorProduct.AlgebraTensorModule.cancelBaseChange baseRing (baseRing ⧸ maximalIdeal)
      maximalIdeal.ResidueField maximalIdeal.ResidueField moduleCarrier).finrank_eq]
  exact (Module.finrank_baseChange
    (R := maximalIdeal.ResidueField) (S := baseRing ⧸ maximalIdeal)).symm

/-- A finite flat extension of constant local rank multiplies dimensions over a field. -/
theorem finrank_eq_mul_of_rankAtStalk_eq {baseField baseRing extensionRing : Type*}
    [Field baseField] [CommRing baseRing] [CommRing extensionRing]
    [Algebra baseField baseRing] [Algebra baseRing extensionRing]
    [Algebra baseField extensionRing] [IsScalarTower baseField baseRing extensionRing]
    [Module.Finite baseField baseRing] [Module.Finite baseRing extensionRing]
    [Module.Flat baseRing extensionRing] {rank : ℕ}
    (constantRank : ∀ prime, Module.rankAtStalk (R := baseRing) extensionRing prime = rank) :
    Module.finrank baseField extensionRing = rank * Module.finrank baseField baseRing := by
  rcases subsingleton_or_nontrivial baseRing with trivialBase | nontrivialBase
  · have : Subsingleton extensionRing := Module.subsingleton baseRing extensionRing
    simp [Module.finrank_zero_of_subsingleton]
  have : IsArtinianRing baseRing := IsArtinianRing.of_finite baseField baseRing
  obtain ⟨basis⟩ := Module.nonempty_basis_of_flat_of_finrank_eq baseRing extensionRing rank
    fun maximalIdeal ↦ by rw [finrank_quotient_tensorProduct, constantRank]
  have : Module.Free baseRing extensionRing := .of_basis basis
  rw [← Module.finrank_mul_finrank baseField baseRing extensionRing,
    Module.finrank_eq_card_basis basis, Fintype.card_fin, mul_comm]

end Module
