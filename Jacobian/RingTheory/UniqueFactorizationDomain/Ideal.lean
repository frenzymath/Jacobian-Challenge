import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal

/-!
# Principal ideals and minimal primes in unique factorization domains
-/

theorem Ideal.exists_ne_zero_finsetInf_eq_span_singleton {ring : Type*} [CommRing ring] [IsDomain ring]
    (denominator : Finset (Ideal ring)) (hs : ∀ prime ∈ denominator, ∃ presentationMap : ring, Prime presentationMap ∧ prime = Ideal.span {presentationMap}) :
    ∃ firstMap : ring, firstMap ≠ 0 ∧ denominator.inf id = Ideal.span {firstMap} := by
  classical
  induction denominator using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert prime denominator hqs ih =>
    obtain ⟨firstMap, hf0, hf⟩ := ih fun prime hq ↦ hs prime (Finset.mem_insert_of_mem hq)
    obtain ⟨presentationMap, hπ, rfl⟩ := hs prime (Finset.mem_insert_self prime denominator)
    have hπf : ¬presentationMap ∣ firstMap := by
      intro hdvd
      have hle : denominator.inf id ≤ Ideal.span {presentationMap} := by
        rw [hf, Ideal.span_singleton_le_span_singleton]
        exact hdvd
      obtain ⟨q', hq's, hq'le⟩ :=
        ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).inf_le'.mp hle
      obtain ⟨π', hπ', rfl⟩ := hs q' (Finset.mem_insert_of_mem hq's)
      rw [id, Ideal.span_singleton_le_span_singleton] at hq'le
      have := (Ideal.span_singleton_eq_span_singleton.mpr (hπ.associated_of_dvd hπ' hq'le))
      exact hqs (this ▸ hq's)
    refine ⟨presentationMap * firstMap, mul_ne_zero hπ.ne_zero hf0, ?_⟩
    rw [Finset.inf_insert, hf, id]
    ext element
    simp only [Ideal.mem_inf, Ideal.mem_span_singleton]
    refine ⟨fun ⟨hπx, member, hy⟩ ↦ ?_, fun compatibility ↦ ⟨(dvd_mul_right presentationMap firstMap).trans compatibility,
      (dvd_mul_left firstMap presentationMap).trans compatibility⟩⟩
    subst hy
    obtain ⟨point, rfl⟩ := (hπ.dvd_or_dvd hπx).resolve_left hπf
    exact ⟨point, by ring⟩


theorem Ideal.IsRadical.exists_ne_zero_eq_span_singleton {ring : Type*} [CommRing ring] [IsDomain ring]
    [IsNoetherianRing ring] {ideal : Ideal ring} (hI : ideal.IsRadical)
    (compatibility : ∀ prime ∈ ideal.minimalPrimes, ∃ presentationMap : ring, Prime presentationMap ∧ prime = Ideal.span {presentationMap}) :
    ∃ firstMap : ring, firstMap ≠ 0 ∧ ideal = Ideal.span {firstMap} := by
  have hfin := ideal.finite_minimalPrimes_of_isNoetherianRing
  obtain ⟨firstMap, hf0, hf⟩ := Ideal.exists_ne_zero_finsetInf_eq_span_singleton hfin.toFinset
    fun prime hq ↦ compatibility prime (hfin.mem_toFinset.mp hq)
  refine ⟨firstMap, hf0, ?_⟩
  rw [← hf, Finset.inf_id_eq_sInf, hfin.coe_toFinset, Ideal.sInf_minimalPrimes, hI.radical]


theorem Ideal.exists_forall_dvd_mul_of_mem_minimalPrimes {ring : Type*} [CommRing ring] [IsDomain ring]
    {firstMap : ring} (hf : firstMap ≠ 0) {primeIdeal : Ideal ring} (hP : primeIdeal ∈ (Ideal.span {firstMap}).minimalPrimes) (maximalPrime : Ideal ring)
    [maximalPrime.IsPrime] [UniqueFactorizationMonoid (Localization.AtPrime maximalPrime)] :
    ∃ generator ∈ primeIdeal, generator ≠ 0 ∧ ∀ member ∈ primeIdeal, ∃ denominator ∉ maximalPrime, generator ∣ denominator * member := by
  classical
  by_cases hP𝔮 : primeIdeal ≤ maximalPrime
  swap
  · obtain ⟨generator, haP, ha𝔮⟩ := SetLike.not_le_iff_exists.1 hP𝔮
    exact ⟨generator, haP, fun compatibility ↦ ha𝔮 (compatibility ▸ zero_mem _), fun member _ ↦ ⟨generator, ha𝔮, dvd_mul_right generator member⟩⟩
  let auxiliaryIdeal := Localization.AtPrime maximalPrime
  have hPprime : primeIdeal.IsPrime := hP.1.1
  have hdisj : Disjoint (maximalPrime.primeCompl : Set ring) primeIdeal :=
    Set.disjoint_left.2 fun _ hx hxP ↦ hx (hP𝔮 hxP)
  have hPL := IsLocalization.isPrime_of_isPrime_disjoint maximalPrime.primeCompl auxiliaryIdeal primeIdeal hPprime hdisj
  have hcomap := IsLocalization.under_map_of_isPrime_disjoint maximalPrime.primeCompl auxiliaryIdeal hPprime hdisj
  have inj : Function.Injective (algebraMap ring auxiliaryIdeal) :=
    IsLocalization.injective auxiliaryIdeal maximalPrime.primeCompl_le_nonZeroDivisors
  have hf0 : algebraMap ring auxiliaryIdeal firstMap ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap ring auxiliaryIdeal)]
    exact inj.ne hf
  obtain ⟨projection, hpf, hp, hpP⟩ : ∃ projection, projection ∣ algebraMap ring auxiliaryIdeal firstMap ∧ Prime projection ∧
      projection ∈ primeIdeal.map (algebraMap ring auxiliaryIdeal) := by
    have hmem : (UniqueFactorizationMonoid.factors (algebraMap ring auxiliaryIdeal firstMap)).prod ∈
        primeIdeal.map (algebraMap ring auxiliaryIdeal) :=
      Ideal.mem_of_dvd _ (UniqueFactorizationMonoid.factors_prod hf0).symm.dvd
        (Ideal.mem_map_of_mem _ (hP.1.2 (Ideal.mem_span_singleton_self firstMap)))
    obtain ⟨projection, hp, hpP⟩ := (hPL.multiset_prod_mem_iff_exists_mem _).1 hmem
    exact ⟨projection, UniqueFactorizationMonoid.dvd_of_mem_factors hp,
      UniqueFactorizationMonoid.prime_of_factor projection hp, hpP⟩
  let complement := (Ideal.span {projection}).comap (algebraMap ring auxiliaryIdeal)
  have : (Ideal.span {projection}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  have hQP : complement ≤ primeIdeal := by
    rw [← hcomap]
    exact Ideal.comap_mono ((Ideal.span_singleton_le_iff_mem _).2 hpP)
  have hfQ : Ideal.span {firstMap} ≤ complement :=
    (Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 hpf))
  have hPQ : primeIdeal = complement := le_antisymm (hP.2 ⟨Ideal.comap_isPrime _ _, hfQ⟩ hQP) hQP
  have hmap : primeIdeal.map (algebraMap ring auxiliaryIdeal) = Ideal.span {projection} := by
    rw [hPQ]
    exact IsLocalization.map_under maximalPrime.primeCompl auxiliaryIdeal _
  obtain ⟨⟨generator, witness⟩, hat⟩ := IsLocalization.surj maximalPrime.primeCompl projection
  have haP : generator ∈ primeIdeal := by
    rw [hPQ, Ideal.mem_comap, ← hat]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self projection)
  have ha0 : generator ≠ 0 := by
    rintro rfl
    rw [map_zero, (IsLocalization.map_units auxiliaryIdeal witness).mul_left_eq_zero] at hat
    exact hp.ne_zero hat
  refine ⟨generator, haP, ha0, fun member hb ↦ ?_⟩
  have hbL : algebraMap ring auxiliaryIdeal member ∈ Ideal.span {projection} := hmap ▸ Ideal.mem_map_of_mem _ hb
  obtain ⟨factor, hc⟩ := Ideal.mem_span_singleton'.1 hbL
  obtain ⟨⟨dimension, typeUniverse⟩, hdu⟩ := IsLocalization.surj maximalPrime.primeCompl factor
  refine ⟨witness * typeUniverse, (maximalPrime.primeCompl.mul_mem witness.2 typeUniverse.2 :), dimension, inj ?_⟩
  simp only at hat hdu
  rw [map_mul, map_mul, map_mul, ← hc, ← hat, ← hdu]
  ring


theorem Ideal.exists_notMem_forall_dvd_mul {ring : Type*} [CommRing ring] {ideal maximalPrime : Ideal ring} [maximalPrime.IsPrime]
    (hI : ideal.FG) {generator : ring} (compatibility : ∀ member ∈ ideal, ∃ denominator ∉ maximalPrime, generator ∣ denominator * member) : ∃ denominator ∉ maximalPrime, ∀ member ∈ ideal, generator ∣ denominator * member := by
  suffices ∀ J : Ideal ring, J.FG → J ≤ ideal → ∃ denominator ∉ maximalPrime, ∀ member ∈ J, generator ∣ denominator * member from this ideal hI le_rfl
  intro J hJ
  induction J, hJ using Submodule.fg_induction with
  | singleton member =>
    intro hyI
    obtain ⟨denominator, hs, hsy⟩ := compatibility member (hyI (Submodule.mem_span_singleton_self member))
    refine ⟨denominator, hs, fun member hb ↦ ?_⟩
    obtain ⟨factor, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    rw [mul_left_comm]
    exact hsy.mul_left factor
  | sup J₁ J₂ _ _ ih₁ ih₂ =>
    intro hJI
    obtain ⟨s₁, hs₁, h₁⟩ := ih₁ (le_sup_left.trans hJI)
    obtain ⟨s₂, hs₂, h₂⟩ := ih₂ (le_sup_right.trans hJI)
    refine ⟨s₁ * s₂, fun hs ↦ (Ideal.IsPrime.mem_or_mem ‹_› hs).elim hs₁ hs₂, fun member hb ↦ ?_⟩
    obtain ⟨member, hy, point, hz, rfl⟩ := Submodule.mem_sup.1 hb
    have equivalence : s₁ * s₂ * (member + point) = s₂ * (s₁ * member) + s₁ * (s₂ * point) := by ring
    rw [equivalence]
    exact dvd_add ((h₁ member hy).mul_left _) ((h₂ point hz).mul_left _)
