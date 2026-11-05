import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# Locally principal nonzero ideals are invertible
-/

theorem Ideal.invertible_of_forall_isMaximal {ring : Type*} [CommRing ring] [IsDomain ring] (ideal : Ideal ring)
    (compatibility : ∀ maximalPrime : Ideal ring, maximalPrime.IsMaximal → ∃ generator ∈ ideal, generator ≠ 0 ∧ ∃ denominator ∉ maximalPrime, ∀ member ∈ ideal, generator ∣ denominator * member) :
    Module.Invertible ring ideal := by
  let fractionField := FractionRing ring
  have inj := IsFractionRing.injective ring fractionField
  let mappedIdeal : Submodule ring fractionField := Submodule.map (Algebra.linearMap ring fractionField) ideal
  have hle : mappedIdeal * (1 / mappedIdeal) ≤ 1 := by
    rw [mul_comm, ← Submodule.le_div_iff_mul_le]
  have hge : 1 ≤ mappedIdeal * (1 / mappedIdeal) := by
    rw [Submodule.one_le]
    let auxiliaryIdeal : Ideal ring := (mappedIdeal * (1 / mappedIdeal)).comap (Algebra.linearMap ring fractionField)
    suffices auxiliaryIdeal = ⊤ by
      have h1 : (1 : ring) ∈ auxiliaryIdeal := this ▸ Submodule.mem_top
      simpa [auxiliaryIdeal] using h1
    by_contra hL
    obtain ⟨maximalPrime, h𝔮, hL𝔮⟩ := Ideal.exists_le_maximal auxiliaryIdeal hL
    obtain ⟨generator, haI, ha0, denominator, hs𝔮, hs⟩ := compatibility maximalPrime h𝔮
    have ha0' : algebraMap ring fractionField generator ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap ring fractionField)]
      exact inj.ne ha0
    refine hs𝔮 (hL𝔮 ?_)
    have hk : algebraMap ring fractionField denominator / algebraMap ring fractionField generator ∈ 1 / mappedIdeal := by
      rw [Submodule.mem_div_iff_forall_mul_mem]
      rintro _ ⟨member, hb, rfl⟩
      obtain ⟨factor, hc⟩ := hs member hb
      rw [Submodule.mem_one]
      refine ⟨factor, ?_⟩
      rw [Algebra.linearMap_apply, div_mul_eq_mul_div, ← map_mul, hc, map_mul,
        mul_div_cancel_left₀ _ ha0']
    have := Submodule.mul_mem_mul (Submodule.mem_map_of_mem (f := Algebra.linearMap ring fractionField) haI) hk
    rwa [Algebra.linearMap_apply, mul_div_cancel₀ _ ha0'] at this
  have hu : IsUnit mappedIdeal := .of_mul_eq_one (1 / mappedIdeal) (le_antisymm hle hge)
  exact .congr ((LinearEquiv.ofEq _ _ hu.unit_spec).trans
    (Submodule.equivMapOfInjective _ inj ideal).symm)
