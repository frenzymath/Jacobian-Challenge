import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Unique factorization from principal minimal primes and localization
-/

variable {ring : Type*} [CommRing ring] [IsDomain ring]


theorem Prime.of_prime_algebraMap_away {element member : ring} (hx : Prime element) (hb : ¬element ∣ member) (localizedRing : Type*)
    [CommRing localizedRing] [Algebra ring localizedRing] [IsLocalization.Away element localizedRing] (compatibility : Prime (algebraMap ring localizedRing member)) :
    Prime member := by
  have inj : Function.Injective (algebraMap ring localizedRing) :=
    IsLocalization.injective localizedRing (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
  have key (factor : ring) (hc : algebraMap ring localizedRing member ∣ algebraMap ring localizedRing factor) : member ∣ factor := by
    obtain ⟨equivalence, he⟩ := hc
    obtain ⟨⟨generator, ⟨_, rank, rfl⟩⟩, hae⟩ := IsLocalization.surj (Submonoid.powers element) equivalence
    have hca : factor * element ^ rank = member * generator := inj (by
      rw [map_mul, map_mul, he, mul_assoc, ← hae])
    obtain ⟨secondMap, rfl⟩ := hx.pow_dvd_of_dvd_mul_left rank hb ⟨factor, by rw [← hca, mul_comm]⟩
    exact ⟨secondMap, mul_right_cancel₀ (pow_ne_zero rank hx.ne_zero) (by rw [hca]; ring)⟩
  refine ⟨fun h0 ↦ compatibility.ne_zero (by simp [h0]), fun hu ↦ compatibility.not_isUnit (hu.map _), fun factor dimension hcd ↦ ?_⟩
  rcases compatibility.dvd_or_dvd (by simpa using map_dvd (algebraMap ring localizedRing) hcd) with h1 | h1
  · exact .inl (key factor h1)
  · exact .inr (key dimension h1)

namespace UniqueFactorizationMonoid


theorem of_isLocalization_away [WfDvdMonoid ring] {element : ring} (hx : Prime element) (localizedRing : Type*) [CommRing localizedRing]
    [Algebra ring localizedRing] [IsLocalization.Away element localizedRing] [UniqueFactorizationMonoid localizedRing] :
    UniqueFactorizationMonoid ring := by
  have inj : Function.Injective (algebraMap ring localizedRing) :=
    IsLocalization.injective localizedRing (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
  have : IsDomain localizedRing := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers element) localizedRing
    (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
  rw [iff_exists_prime_mem_of_isPrime]
  intro primeIdeal hP0 hP
  by_cases hxP : element ∈ primeIdeal
  · exact ⟨element, hxP, hx⟩
  have hdisj := (Ideal.disjoint_powers_iff_notMem_of_isPrime element).2 hxP
  have hP' := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers element) localizedRing primeIdeal hP hdisj
  have hcomap := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers element) localizedRing hP hdisj
  have hP'0 : primeIdeal.map (algebraMap ring localizedRing) ≠ ⊥ := fun compatibility ↦
    hP0 (hcomap ▸ (compatibility ▸ Ideal.comap_bot_of_injective _ inj))
  obtain ⟨prime, hqP', hq⟩ := hP'.exists_mem_prime_of_ne_bot hP'0
  obtain ⟨⟨generator, ⟨_, rank, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers element) prime
  have hu (bound : ℕ) : IsUnit (algebraMap ring localizedRing (element ^ bound)) :=
    IsLocalization.map_units localizedRing (⟨element ^ bound, bound, rfl⟩ : Submonoid.powers element)
  have haP : generator ∈ primeIdeal := by
    rw [← hcomap, Ideal.under, Ideal.mem_comap, ← ha]
    exact Ideal.mul_mem_right _ _ hqP'
  have ha0 : generator ≠ 0 := by
    rintro rfl
    rw [map_zero, (hu rank).mul_left_eq_zero] at ha
    exact hq.ne_zero ha
  obtain ⟨j, member, hxb, rfl⟩ := WfDvdMonoid.max_power_factor ha0 hx.irreducible
  have hbP : member ∈ primeIdeal := (hP.mem_or_mem haP).resolve_left fun compatibility ↦ hxP (hP.mem_of_pow_mem j compatibility)
  refine ⟨member, hbP, hx.of_prime_algebraMap_away hxb localizedRing ?_⟩
  have : Associated prime (algebraMap ring localizedRing (element ^ j) * algebraMap ring localizedRing member) := by
    rw [← map_mul, ← ha]
    exact associated_mul_unit_right _ _ (hu rank)
  exact (this.trans (associated_unit_mul_left _ _ (hu j))).prime hq


theorem of_forall_isPrincipal_of_mem_minimalPrimes
    (compatibility : ∀ firstMap : ring, firstMap ≠ 0 → ∀ primeIdeal ∈ (Ideal.span {firstMap}).minimalPrimes, primeIdeal.IsPrincipal) :
    UniqueFactorizationMonoid ring := by
  rw [iff_exists_prime_mem_of_isPrime]
  intro complement hQ0 hQ
  obtain ⟨firstMap, hfQ, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
  obtain ⟨primeIdeal, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).2 hfQ)
  obtain ⟨generator, rfl⟩ := (compatibility firstMap hf0 primeIdeal hP).principal
  have ha0 : generator ≠ 0 := by
    rintro rfl
    have := hP.1.2 (Ideal.mem_span_singleton_self firstMap)
    rw [Submodule.span_singleton_eq_bot.2 rfl, Ideal.mem_bot] at this
    exact hf0 this
  exact ⟨generator, hPQ (Submodule.mem_span_singleton_self generator), (Ideal.span_singleton_prime ha0).1 hP.1.1⟩

end UniqueFactorizationMonoid
