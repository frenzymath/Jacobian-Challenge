import Jacobian.RingTheory.Ideal.Invertible
import Jacobian.RingTheory.LocalProperties.StablyFree
import Jacobian.RingTheory.RegularLocalRing.ProjectiveDimension
import Jacobian.RingTheory.RegularLocalRing.Localization
import Jacobian.RingTheory.UniqueFactorizationDomain.Ideal
import Jacobian.RingTheory.UniqueFactorizationDomain.Kaplansky
import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Unique factorization in regular local rings
-/

universe typeUniverse

open IsLocalRing

namespace IsRegularLocalRing


private theorem uniqueFactorizationMonoid_of_spanFinrank_eq (bound : ℕ) :
    ∀ (ring : Type typeUniverse) [CommRing ring] [IsLocalRing ring] [IsRegularRing ring],
      (maximalIdeal ring).spanFinrank = bound → UniqueFactorizationMonoid ring := by
  induction bound using Nat.strong_induction_on with
  | _ bound ih =>
  intro ring _ _ _ hn
  have := IsRegularLocalRing.of_isRegularRing_of_isLocalRing ring
  -- the localizations of `ring` at primes `prime ≠ 𝔪` are UFDs by induction
  have hloc (prime : Ideal ring) [prime.IsPrime] (hq : prime ≠ maximalIdeal ring) :
      UniqueFactorizationMonoid (Localization.AtPrime prime) := by
    refine ih (maximalIdeal (Localization.AtPrime prime)).spanFinrank ?_ (Localization.AtPrime prime) rfl
    have h1 : ((maximalIdeal (Localization.AtPrime prime)).spanFinrank : WithBot ℕ∞) =
        ringKrullDim (Localization.AtPrime prime) :=
      IsRegularLocalRing.spanFinrank_maximalIdeal
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height prime] at h1
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime
      (lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hq)
    have h3 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := ring)
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, hn] at h3
    have h1' : ((maximalIdeal (Localization.AtPrime prime)).spanFinrank : ℕ∞) = prime.height := by
      exact_mod_cast h1
    have h3' : (maximalIdeal ring).height = bound := by exact_mod_cast h3
    rw [← h1', h3'] at h2
    exact_mod_cast (ENat.add_one_le_iff (ENat.natCast_ne_top _)).1 h2
  by_cases hfield : IsField ring
  · let := hfield.toField
    infer_instance
  have hm : maximalIdeal ring ≠ ⊥ := fun compatibility ↦ hfield (isField_iff_maximalIdeal_eq.2 compatibility)
  obtain ⟨element, hxm, hx2⟩ : ∃ element ∈ maximalIdeal ring, element ∉ maximalIdeal ring ^ 2 := by
    by_contra! compatibility
    exact hm (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
      (maximalIdeal ring).fg_of_isNoetherianRing (by rw [smul_eq_mul, ← pow_two]; exact compatibility)
      (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]))
  have hx0 : element ≠ 0 := fun compatibility ↦ hx2 (compatibility ▸ zero_mem _)
  obtain ⟨_, _, -⟩ := IsRegularLocalRing.quotient_span_singleton hxm hx2
  have hx : Prime element := (Ideal.span_singleton_prime hx0).1
    ((Ideal.Quotient.isDomain_iff_prime _).1 inferInstance)
  let localizedRing := Localization.Away element
  have : IsDomain localizedRing :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  suffices UniqueFactorizationMonoid localizedRing from
    UniqueFactorizationMonoid.of_isLocalization_away hx localizedRing
  refine UniqueFactorizationMonoid.of_forall_isPrincipal_of_mem_minimalPrimes fun firstMap hf primeIdeal hP ↦ ?_
  -- `primeIdeal` is locally principal, hence invertible
  have hinv : Module.Invertible localizedRing primeIdeal := by
    refine Ideal.invertible_of_forall_isMaximal primeIdeal fun maximalPrime h𝔮 ↦ ?_
    have : UniqueFactorizationMonoid (Localization.AtPrime maximalPrime) := by
      have hq : maximalPrime.comap (algebraMap ring localizedRing) ≠ maximalIdeal ring := fun compatibility ↦ by
        have : algebraMap ring localizedRing element ∈ maximalPrime := by
          rw [← Ideal.mem_comap, compatibility]
          exact hxm
        exact h𝔮.ne_top (Ideal.eq_top_of_isUnit_mem _ this
          (IsLocalization.Away.algebraMap_isUnit element))
      have := hloc _ hq
      exact MulEquiv.uniqueFactorizationMonoid
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization _ maximalPrime).toMulEquiv this
    obtain ⟨generator, haP, ha0, h'⟩ := Ideal.exists_forall_dvd_mul_of_mem_minimalPrimes hf hP maximalPrime
    obtain ⟨denominator, hs, hs'⟩ := Ideal.exists_notMem_forall_dvd_mul (IsNoetherian.noetherian primeIdeal) h'
    exact ⟨generator, haP, ha0, denominator, hs, hs'⟩
  -- `primeIdeal` is the localization of `primeIdeal ∩ ring`, which has finite projective dimension, so `primeIdeal` is
  -- stably free
  let projection := primeIdeal.comap (algebraMap ring localizedRing)
  have hP' : Submodule.localized' localizedRing (Submonoid.powers element) (Algebra.linearMap ring localizedRing) projection = primeIdeal := by
    rw [Ideal.localized'_eq_map]
    exact IsLocalization.map_under (Submonoid.powers element) localizedRing primeIdeal
  have : Module.Invertible localizedRing
      (Submodule.localized' localizedRing (Submonoid.powers element) (Algebra.linearMap ring localizedRing) projection) :=
    .congr (LinearEquiv.ofEq _ _ hP'.symm)
  obtain ⟨dimension, hd⟩ := IsRegularLocalRing.exists_hasProjectiveDimensionLE (ModuleCat.of ring projection)
  have : Module.IsStablyFree localizedRing
      (Submodule.localized' localizedRing (Submonoid.powers element) (Algebra.linearMap ring localizedRing) projection) :=
    Module.isStablyFree_of_isLocalizedModule_of_hasProjectiveDimensionLE (Submonoid.powers element) dimension projection
      hd _ (projection.toLocalized' localizedRing (Submonoid.powers element) (Algebra.linearMap ring localizedRing))
  have := Module.free_of_isStablyFree_of_invertible localizedRing
    (Submodule.localized' localizedRing (Submonoid.powers element) (Algebra.linearMap ring localizedRing) projection)
  obtain ⟨equivalence⟩ := Module.Invertible.free_iff_linearEquiv.1 this
  rw [← hP']
  exact ⟨_, Submodule.eq_span_singleton_of_surjective equivalence.symm.surjective⟩


@[stacks 0AG0 "Under the extra assumption that `ring` is generator regular ring."]
theorem uniqueFactorizationMonoid (ring : Type typeUniverse) [CommRing ring] [IsRegularLocalRing ring]
    [IsRegularRing ring] : UniqueFactorizationMonoid ring :=
  uniqueFactorizationMonoid_of_spanFinrank_eq _ ring rfl

end IsRegularLocalRing
