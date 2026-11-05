import Jacobian.RingTheory.Localization.Free
import Jacobian.RingTheory.Localization.Principal
import Jacobian.RingTheory.Norm.NonZeroDivisors
import Jacobian.RingTheory.Norm.Prime
import Jacobian.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.LocalRing.Module

/-!
# Local equations in finite algebras
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory

theorem Ideal.exists_mem_mul_mem_span_singleton_of_map_eq {ring localizedRing : Type*} [CommRing ring]
    [CommRing localizedRing] [Algebra ring localizedRing] (module : Submonoid ring) [IsLocalization module localizedRing] {ideal : Ideal ring}
    (hI : ideal.FG) {morphism : localizedRing} (hf : ideal.map (algebraMap ring localizedRing) = Ideal.span {morphism}) :
    ∃ power ∈ module, ∃ denominator ∈ ideal, ideal.map (algebraMap ring localizedRing) = Ideal.span {algebraMap ring localizedRing denominator} ∧
      ∀ index ∈ ideal, power * index ∈ Ideal.span {denominator} := by
  classical
  have hfI : morphism ∈ ideal.map (algebraMap ring localizedRing) := hf ▸ Ideal.mem_span_singleton_self morphism
  obtain ⟨⟨⟨denominator, hbI⟩, localSection⟩, hbm⟩ := (IsLocalization.mem_map_algebraMap_iff module localizedRing).mp hfI
  have hspan : ideal.map (algebraMap ring localizedRing) = Ideal.span {algebraMap ring localizedRing denominator} := by
    rw [hf, ← hbm, Ideal.span_singleton_mul_right_unit (IsLocalization.map_units localizedRing localSection)]
  have hmem (index : ring) (hi : index ∈ ideal) : ∃ power ∈ module, power * index ∈ Ideal.span {denominator} := by
    have : algebraMap ring localizedRing index ∈ (Ideal.span {denominator}).map (algebraMap ring localizedRing) := by
      rw [Ideal.map_span, Set.image_singleton, ← hspan]
      exact Ideal.mem_map_of_mem _ hi
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff module localizedRing _ _).mp this
  obtain ⟨witness, ht⟩ := hI
  choose! power hm hmi using hmem
  refine ⟨∏ index ∈ witness, power index, module.prod_mem fun index hi ↦ hm index (ht ▸ Ideal.subset_span hi), denominator, hbI, hspan,
    fun index hi ↦ ?_⟩
  have key : Ideal.span (witness : Set ring) ≤ (Ideal.span {denominator}).colon {∏ index ∈ witness, power index} := by
    refine Ideal.span_le.mpr fun secondIndex hj ↦ ?_
    rw [SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul,
      mul_comm, ← Finset.prod_erase_mul witness power hj, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hmi secondIndex (ht ▸ Ideal.subset_span hj))
  rw [← ht] at hi
  rw [mul_comm, ← smul_eq_mul, ← Submodule.mem_colon_singleton]
  exact key hi

theorem Ideal.exists_mem_forall_exists_notMem_mul_mem_span_singleton {ring : Type*} [CommRing ring]
    (lyingPrime : Finset (Ideal ring)) (hQ : ∀ localPrime ∈ lyingPrime, localPrime.IsPrime)
    (hQinc : ∀ localPrime ∈ lyingPrime, ∀ q' ∈ lyingPrime, q' ≤ localPrime → q' = localPrime) (ideal : Ideal ring)
    (hI : ∀ localPrime ∈ lyingPrime, ∃ witness ∉ localPrime, ∃ point ∈ ideal, ∀ index ∈ ideal, witness * index ∈ Ideal.span {point}) :
    ∃ compatibility ∈ ideal, ∀ localPrime ∈ lyingPrime, ∃ schemeUniverse ∉ localPrime, ∀ index ∈ ideal, schemeUniverse * index ∈ Ideal.span {compatibility} := by
  classical
  have hsep (localPrime : Ideal ring) (hq : localPrime ∈ lyingPrime) (q' : Ideal ring) (hq' : q' ∈ lyingPrime) (hne : q' ≠ localPrime) :
      ∃ factor ∈ q', factor ∉ localPrime := by
    by_contra! H
    exact hne (hQinc localPrime hq q' hq' H)
  choose! factor hcq' hcq using hsep
  choose! witness ht point hxI hx using hI
  set equivalence : Ideal ring → ring := fun localPrime ↦ ∏ q' ∈ lyingPrime.erase localPrime, factor localPrime q' with he_def
  have he (localPrime : Ideal ring) (hq : localPrime ∈ lyingPrime) : equivalence localPrime ∉ localPrime := by
    have := hQ localPrime hq
    rw [he_def, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨q', hq', hmem⟩
    exact hcq localPrime hq q' (Finset.mem_of_mem_erase hq') (Finset.ne_of_mem_erase hq') hmem
  have he' (localPrime q' : Ideal ring) (hq : localPrime ∈ lyingPrime) (hq' : q' ∈ lyingPrime) (hne : localPrime ≠ q') : equivalence q' ∈ localPrime := by
    simp only [he_def]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne, hq⟩)]
    exact Ideal.mul_mem_right _ _ (hcq' q' hq' localPrime hq hne)
  refine ⟨∑ localPrime ∈ lyingPrime, equivalence localPrime * point localPrime, Ideal.sum_mem _ fun localPrime hq ↦ ideal.mul_mem_left _ (hxI localPrime hq),
    fun localPrime hq ↦ ?_⟩
  have hy (q' : Ideal ring) (hq' : q' ∈ lyingPrime) : ∃ targetPoint, targetPoint * point localPrime = witness localPrime * point q' :=
    Ideal.mem_span_singleton'.mp (hx localPrime hq _ (hxI q' hq'))
  choose! targetPoint hy using hy
  set member := equivalence localPrime * witness localPrime + ∑ q' ∈ lyingPrime.erase localPrime, equivalence q' * targetPoint q'
  have hw : member ∉ localPrime := by
    have := hQ localPrime hq
    rw [Ideal.add_mem_iff_left _ (Ideal.sum_mem _ fun q' hq' ↦ Ideal.mul_mem_right _ _
      (he' localPrime q' hq (Finset.mem_of_mem_erase hq') (Finset.ne_of_mem_erase hq').symm))]
    exact fun hmem ↦ (this.mem_or_mem hmem).elim (he localPrime hq) (ht localPrime hq)
  have hth : witness localPrime * ∑ q' ∈ lyingPrime, equivalence q' * point q' = member * point localPrime := by
    rw [← Finset.add_sum_erase lyingPrime _ hq, mul_add, Finset.mul_sum, add_mul, Finset.sum_mul]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun q' hq' ↦ ?_
      linear_combination -(equivalence q') * hy q' (Finset.mem_of_mem_erase hq')
  refine ⟨witness localPrime * member, fun hmem ↦ ((hQ localPrime hq).mem_or_mem hmem).elim (ht localPrime hq) hw, fun index hi ↦ ?_⟩
  obtain ⟨sourcePoint, hz⟩ := Ideal.mem_span_singleton'.mp (hx localPrime hq index hi)
  refine Ideal.mem_span_singleton'.mpr ⟨sourcePoint * witness localPrime, ?_⟩
  linear_combination sourcePoint * hth + member * hz

theorem Ideal.exists_notMem_mul_mem_span_singleton_of_isIntegral {baseRing extensionRing : Type*} [CommRing baseRing]
    [CommRing extensionRing] [Algebra baseRing extensionRing] [Algebra.IsIntegral baseRing extensionRing] [Algebra.QuasiFinite baseRing extensionRing]
    (prime : Ideal baseRing) [prime.IsPrime] (ideal : Ideal extensionRing)
    (hI : ∀ localPrime : Ideal extensionRing, localPrime.IsPrime → localPrime.comap (algebraMap baseRing extensionRing) = prime →
      ∃ witness ∉ localPrime, ∃ point ∈ ideal, ∀ index ∈ ideal, witness * index ∈ Ideal.span {point}) :
    ∃ generator ∉ prime, ∃ compatibility ∈ ideal, ∀ index ∈ ideal, algebraMap baseRing extensionRing generator * index ∈ Ideal.span {compatibility} := by
  classical
  have hfin := Algebra.QuasiFinite.finite_primesOver (S := extensionRing) prime
  have hmem (localPrime : Ideal extensionRing) :
      localPrime ∈ hfin.toFinset ↔ localPrime.IsPrime ∧ localPrime.comap (algebraMap baseRing extensionRing) = prime := by
    rw [Set.Finite.mem_toFinset, Ideal.primesOver, Set.mem_ofPred_eq, Ideal.liesOver_iff,
      Ideal.under_def, eq_comm]
  obtain ⟨compatibility, hhI, hh⟩ := Ideal.exists_mem_forall_exists_notMem_mul_mem_span_singleton
    hfin.toFinset (fun localPrime hq ↦ ((hmem localPrime).mp hq).1) (fun localPrime hq q' hq' hle ↦ by
      obtain ⟨hqp, hq⟩ := (hmem localPrime).mp hq
      obtain ⟨hq'p, hq'⟩ := (hmem q').mp hq'
      by_contra hne
      exact (Ideal.IsIntegral.comap_lt_comap (R := baseRing) (lt_of_le_of_ne hle hne)).ne
        (hq'.trans hq.symm)) ideal
    fun localPrime hq ↦ hI localPrime ((hmem localPrime).mp hq).1 ((hmem localPrime).mp hq).2
  have hle : ¬((Ideal.span {compatibility}).colon (ideal : Set extensionRing)).comap (algebraMap baseRing extensionRing) ≤ prime := by
    intro hle
    obtain ⟨lyingPrime, hQ, hQp, hQ'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral prime _ hle
    obtain ⟨schemeUniverse, hu, hui⟩ := hh lyingPrime ((hmem lyingPrime).mpr ⟨hQp, hQ'⟩)
    exact hu (hQ (Submodule.mem_colon.mpr fun index hi ↦ hui index hi))
  obtain ⟨generator, hg, hgp⟩ := SetLike.not_le_iff_exists.mp hle
  exact ⟨generator, hgp, compatibility, hhI, fun index hi ↦ Submodule.mem_colon.mp hg index hi⟩

theorem Ideal.exists_pow_mul_eq_zero_of_mul_eq_zero {ring : Type*} [CommRing ring] {ideal : Ideal ring}
    {generator compatibility : ring} (hgh : ∀ index ∈ ideal, generator * index ∈ Ideal.span {compatibility})
    (hI : ∀ lyingPrime : Ideal ring, lyingPrime.IsPrime → generator ∉ lyingPrime → ∃ witness ∉ lyingPrime, ∃ point ∈ ideal,
      ∀ denominator, point * denominator = 0 → ∃ exponent : ℕ, witness ^ exponent * denominator = 0) {denominator : ring} (hb : compatibility * denominator = 0) :
    ∃ exponent : ℕ, generator ^ exponent * denominator = 0 := by
  have hrad : generator ∈ ((⊥ : Ideal ring).colon {denominator}).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro lyingPrime ⟨hle, hQ⟩
    by_contra hgQ
    obtain ⟨witness, ht, point, hxI, hx⟩ := hI lyingPrime hQ hgQ
    obtain ⟨rank, hd⟩ := Ideal.mem_span_singleton'.mp (hgh point hxI)
    obtain ⟨exponent, hn⟩ := hx (generator * denominator) (by linear_combination -denominator * hd + rank * hb)
    have : witness ^ exponent * generator ∈ lyingPrime := hle (Submodule.mem_colon_singleton.mpr (by
      rw [smul_eq_mul, mul_assoc, hn, Submodule.mem_bot]))
    exact (hQ.mem_or_mem this).elim (fun compatibility ↦ ht (hQ.mem_of_pow_mem exponent compatibility)) hgQ
  obtain ⟨exponent, hn⟩ := hrad
  exact ⟨exponent, by simpa using Submodule.mem_colon_singleton.mp hn⟩

theorem Ideal.exists_ne_zero_mem_iff_exists_le {baseRing extensionRing : Type*} [CommRing baseRing] [IsDomain baseRing]
    [CommRing extensionRing] [Algebra baseRing extensionRing] [Module.Finite baseRing extensionRing] [Module.Flat baseRing extensionRing]
    [Module.FinitePresentation baseRing extensionRing] (ideal : Ideal extensionRing)
    (hI : ∀ localPrime : Ideal extensionRing, localPrime.IsPrime → ∃ witness ∉ localPrime, ∃ point ∈ ideal,
      (∀ index ∈ ideal, witness * index ∈ Ideal.span {point}) ∧ ∀ denominator, point * denominator = 0 → ∃ exponent : ℕ, witness ^ exponent * denominator = 0)
    (prime : Ideal baseRing) [prime.IsPrime] :
    ∃ localSection ∉ prime, ∃ numerator : baseRing, numerator ≠ 0 ∧ ∀ primeIdeal : Ideal baseRing, primeIdeal.IsPrime → localSection ∉ primeIdeal →
      (numerator ∈ primeIdeal ↔ ∃ localPrime : Ideal extensionRing, localPrime.IsPrime ∧ localPrime.comap (algebraMap baseRing extensionRing) = primeIdeal ∧ ideal ≤ localPrime) := by
  classical
  have : Module.Free (Localization.AtPrime prime) (LocalizedModule prime.primeCompl extensionRing) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨localizer, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    prime.primeCompl (LocalizedModule.mkLinearMap prime.primeCompl extensionRing) (Localization.AtPrime prime)
  obtain ⟨generator, hg, compatibility, hhI, hgh⟩ := Ideal.exists_notMem_mul_mem_span_singleton_of_isIntegral prime ideal
    fun localPrime hq _ ↦ by
      obtain ⟨witness, ht, point, hx, hxI, -⟩ := hI localPrime hq
      exact ⟨witness, ht, point, hx, hxI⟩
  have hs : localizer * generator ∉ prime := fun compatibility ↦ (‹prime.IsPrime›.mem_or_mem compatibility).elim hr hg
  let Aₛ := Localization.Away (localizer * generator)
  let Bₛ := Localization (Algebra.algebraMapSubmonoid extensionRing (Submonoid.powers (localizer * generator)))
  have : Module.Free Aₛ Bₛ := Module.free_of_isLocalizedModule_away_of_dvd
    (dvd_mul_right localizer generator) Aₛ (IsScalarTower.toAlgHom baseRing extensionRing Bₛ).toLinearMap
  have : Module.Finite Aₛ Bₛ :=
    .of_isLocalizedModule (.powers (localizer * generator)) (IsScalarTower.toAlgHom baseRing extensionRing Bₛ).toLinearMap
  have : IsDomain Aₛ := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors fun compatibility ↦ hs (compatibility ▸ prime.zero_mem))
  have hreg : algebraMap extensionRing Bₛ compatibility ∈ nonZeroDivisors Bₛ := by
    have key (denominator : extensionRing) (hb : compatibility * denominator = 0) : algebraMap extensionRing Bₛ denominator = 0 := by
      obtain ⟨exponent, hn⟩ := Ideal.exists_pow_mul_eq_zero_of_mul_eq_zero (ideal := ideal)
        (generator := algebraMap baseRing extensionRing (localizer * generator)) (fun index hi ↦ by
          rw [map_mul, mul_assoc]
          exact Ideal.mul_mem_left _ _ (hgh index hi))
        (fun lyingPrime hQ _ ↦ by
          obtain ⟨witness, ht, point, hx, -, hx'⟩ := hI lyingPrime hQ
          exact ⟨witness, ht, point, hx, hx'⟩) hb
      refine (IsLocalization.map_eq_zero_iff
        (Algebra.algebraMapSubmonoid extensionRing (Submonoid.powers (localizer * generator))) Bₛ denominator).mpr
        ⟨⟨_, Submonoid.mem_map.mpr ⟨_, ⟨exponent, rfl⟩, map_pow _ _ _⟩⟩, hn⟩
    refine mem_nonZeroDivisors_iff_right.mpr fun targetPoint hy ↦ ?_
    obtain ⟨⟨denominator, power⟩, hbm⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid extensionRing (Submonoid.powers (localizer * generator))) targetPoint
    have hbh : algebraMap extensionRing Bₛ (denominator * compatibility) = 0 := by
      rw [map_mul, ← hbm, mul_right_comm, hy, zero_mul]
    obtain ⟨factor, hc⟩ := (IsLocalization.map_eq_zero_iff
      (Algebra.algebraMapSubmonoid extensionRing (Submonoid.powers (localizer * generator))) Bₛ _).mp hbh
    have hcb := key (factor * denominator) (by linear_combination hc)
    rw [map_mul, (IsLocalization.map_units Bₛ factor).mul_right_eq_zero] at hcb
    exact (IsLocalization.map_units Bₛ power).mul_left_eq_zero.mp (hbm.trans hcb)
  obtain ⟨⟨numerator, power⟩, ha⟩ := IsLocalization.surj (Submonoid.powers (localizer * generator))
    (Algebra.norm Aₛ (algebraMap extensionRing Bₛ compatibility))
  refine ⟨localizer * generator, hs, numerator, ?_, fun primeIdeal hP hsP ↦ ?_⟩
  · rintro rfl
    rw [map_zero, (IsLocalization.map_units Aₛ power).mul_left_eq_zero] at ha
    exact Algebra.norm_ne_zero_of_mem_nonZeroDivisors hreg ha
  have hdisj : Disjoint (Submonoid.powers (localizer * generator) : Set baseRing) primeIdeal := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨exponent, rfl⟩ hx
    exact hsP (hP.mem_of_pow_mem exponent hx)
  let otherPrime := primeIdeal.map (algebraMap baseRing Aₛ)
  have hP' : otherPrime.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Aₛ primeIdeal hP hdisj
  have hP'P : otherPrime.comap (algebraMap baseRing Aₛ) = primeIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint _ Aₛ hP hdisj
  calc numerator ∈ primeIdeal ↔ Algebra.norm Aₛ (algebraMap extensionRing Bₛ compatibility) ∈ otherPrime := by
        rw [← Ideal.mul_unit_mem_iff_mem otherPrime (IsLocalization.map_units Aₛ power), ha,
          ← Ideal.mem_comap, hP'P]
    _ ↔ ∃ lyingPrime : Ideal Bₛ, lyingPrime.IsPrime ∧ lyingPrime.comap (algebraMap Aₛ Bₛ) = otherPrime ∧
        algebraMap extensionRing Bₛ compatibility ∈ lyingPrime := Algebra.norm_mem_iff_exists_isPrime otherPrime _
    _ ↔ ∃ localPrime : Ideal extensionRing, localPrime.IsPrime ∧ localPrime.comap (algebraMap baseRing extensionRing) = primeIdeal ∧ compatibility ∈ localPrime := by
      constructor
      · rintro ⟨lyingPrime, hQ, hQP, hhQ⟩
        refine ⟨lyingPrime.comap (algebraMap extensionRing Bₛ), Ideal.comap_isPrime _ _, ?_, hhQ⟩
        rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
          IsScalarTower.algebraMap_eq baseRing Aₛ Bₛ, ← Ideal.comap_comap, hQP, hP'P]
      · rintro ⟨localPrime, hq, hqP, hhq⟩
        have hdisj' : Disjoint
            (Algebra.algebraMapSubmonoid extensionRing (.powers (localizer * generator)) : Set extensionRing) localPrime := by
          refine Set.disjoint_left.mpr ?_
          rintro _ ⟨point, hx, rfl⟩ hxq
          exact Set.disjoint_left.mp hdisj hx (hqP ▸ Ideal.mem_comap.mpr hxq)
        have hqq : (localPrime.map (algebraMap extensionRing Bₛ)).comap (algebraMap extensionRing Bₛ) = localPrime :=
          IsLocalization.under_map_of_isPrime_disjoint _ Bₛ hq hdisj'
        refine ⟨localPrime.map (algebraMap extensionRing Bₛ),
          IsLocalization.isPrime_of_isPrime_disjoint _ Bₛ localPrime hq hdisj', ?_,
          Ideal.mem_map_of_mem _ hhq⟩
        rw [← IsLocalization.map_under (.powers (localizer * generator)) Aₛ ((localPrime.map _).comap _),
          Ideal.under_def, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
          IsScalarTower.algebraMap_eq baseRing extensionRing Bₛ, ← Ideal.comap_comap,
          hqq, hqP]
    _ ↔ _ := by
      refine exists_congr fun localPrime ↦ and_congr_right fun hq ↦ and_congr_right fun hqP ↦
        ⟨fun hhq index hi ↦ ?_, fun hIq ↦ hIq hhI⟩
      have hgq : algebraMap baseRing extensionRing generator ∉ localPrime := fun hgq ↦ by
        have : generator ∈ primeIdeal := hqP ▸ Ideal.mem_comap.mpr hgq
        exact hsP (primeIdeal.mul_mem_left localizer this)
      exact (hq.mem_or_mem ((Ideal.span_singleton_le_iff_mem _).mpr hhq (hgh index hi))).resolve_left
        hgq

theorem Ideal.exists_ne_zero_radical_span_singleton_eq_span_singleton {ring : Type*} [CommRing ring]
    [IsDomain ring] [IsNoetherianRing ring] [UniqueFactorizationMonoid ring] {numerator : ring} (ha : numerator ≠ 0) :
    ∃ morphism : ring, morphism ≠ 0 ∧ (Ideal.span {numerator}).radical = Ideal.span {morphism} := by
  refine (Ideal.radical_isRadical _).exists_ne_zero_eq_span_singleton fun localPrime hq ↦ ?_
  rw [Ideal.radical_minimalPrimes] at hq
  have hqp := hq.1.1
  have hprod : (UniqueFactorizationMonoid.factors numerator).prod ∈ localPrime := by
    obtain ⟨schemeUniverse, hu⟩ := UniqueFactorizationMonoid.factors_prod ha
    rw [← mul_one (UniqueFactorizationMonoid.factors numerator).prod, ← schemeUniverse.mul_inv, ← mul_assoc, hu]
    exact localPrime.mul_mem_right _ (hq.1.2 (Ideal.mem_span_singleton_self numerator))
  obtain ⟨primeElement, hπ, hπq⟩ := (hqp.multiset_prod_mem_iff_exists_mem _).mp hprod
  have hπp := UniqueFactorizationMonoid.prime_of_factor primeElement hπ
  refine ⟨primeElement, hπp, le_antisymm (hq.2 ⟨(Ideal.span_singleton_prime hπp.ne_zero).mpr hπp, ?_⟩ ?_) ?_⟩
  · exact Ideal.span_singleton_le_span_singleton.mpr
      (UniqueFactorizationMonoid.dvd_of_mem_factors hπ)
  · exact (Ideal.span_singleton_le_iff_mem localPrime).mpr hπq
  · exact (Ideal.span_singleton_le_iff_mem localPrime).mpr hπq

theorem Ideal.exists_notMem_mul_mem_span_radical_span_singleton {baseRing : Type*} [CommRing baseRing]
    [IsDomain baseRing] [IsNoetherianRing baseRing] (prime : Ideal baseRing) [prime.IsPrime] (localizedRing : Type*) [CommRing localizedRing]
    [Algebra baseRing localizedRing] [IsLocalization.AtPrime localizedRing prime] [UniqueFactorizationMonoid localizedRing] {numerator : baseRing}
    (ha : numerator ≠ 0) :
    ∃ generator ∉ prime, ∃ denominator ∈ (Ideal.span {numerator}).radical, denominator ≠ 0 ∧
      ∀ index ∈ (Ideal.span {numerator}).radical, generator * index ∈ Ideal.span {denominator} := by
  have : IsDomain localizedRing := IsLocalization.isDomain_of_atPrime localizedRing prime
  have : IsNoetherianRing localizedRing := IsLocalization.isNoetherianRing prime.primeCompl localizedRing inferInstance
  have hinj : Function.Injective (algebraMap baseRing localizedRing) :=
    IsLocalization.injective localizedRing prime.primeCompl_le_nonZeroDivisors
  obtain ⟨morphism, hf0, hf⟩ := Ideal.exists_ne_zero_radical_span_singleton_eq_span_singleton
    ((map_ne_zero_iff _ hinj).mpr ha)
  have hf' : (Ideal.span {numerator}).radical.map (algebraMap baseRing localizedRing) = Ideal.span {morphism} := by
    rw [IsLocalization.map_radical prime.primeCompl, Ideal.map_span, Set.image_singleton, hf]
  obtain ⟨generator, hg, denominator, hb, hspan, hgb⟩ :=
    Ideal.exists_notMem_mul_mem_span_singleton_of_map_eq prime _ morphism hf'
  refine ⟨generator, hg, denominator, hb, ?_, hgb⟩
  rintro rfl
  exact hf0 (Ideal.span_singleton_eq_bot.mp (hf'.symm.trans (hspan.trans (by simp))))
