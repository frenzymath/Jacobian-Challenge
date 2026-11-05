import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Principal generators near a prime

An ideal that is principal at a prime has a single generator after inverting
one element outside the prime.
-/

theorem Ideal.exists_notMem_mul_mem_span_singleton_of_map_eq {ring localizedRing : Type*} [CommRing ring]
    [CommRing localizedRing] [Algebra ring localizedRing] [IsNoetherianRing ring] (prime : Ideal ring) [prime.IsPrime]
    [IsLocalization.AtPrime localizedRing prime] (ideal : Ideal ring) (morphism : localizedRing)
    (hf : ideal.map (algebraMap ring localizedRing) = Ideal.span {morphism}) :
    ∃ generator ∉ prime, ∃ denominator ∈ ideal, ideal.map (algebraMap ring localizedRing) = Ideal.span {algebraMap ring localizedRing denominator} ∧
      ∀ index ∈ ideal, generator * index ∈ Ideal.span {denominator} := by
  classical
  have hfI : morphism ∈ ideal.map (algebraMap ring localizedRing) := hf ▸ Ideal.mem_span_singleton_self morphism
  obtain ⟨⟨⟨denominator, hbI⟩, localSection⟩, hbm⟩ :=
    (IsLocalization.mem_map_algebraMap_iff prime.primeCompl localizedRing).mp hfI
  have hspan : ideal.map (algebraMap ring localizedRing) = Ideal.span {algebraMap ring localizedRing denominator} := by
    rw [hf, ← hbm, Ideal.span_singleton_mul_right_unit (IsLocalization.map_units localizedRing localSection)]
  have hmem (index : ring) (hi : index ∈ ideal) : ∃ power ∈ prime.primeCompl, power * index ∈ Ideal.span {denominator} := by
    have : algebraMap ring localizedRing index ∈ (Ideal.span {denominator}).map (algebraMap ring localizedRing) := by
      rw [Ideal.map_span, Set.image_singleton, ← hspan]
      exact Ideal.mem_map_of_mem _ hi
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff prime.primeCompl localizedRing _ _).mp this
  obtain ⟨witness, ht⟩ := (IsNoetherian.noetherian ideal : ideal.FG)
  choose! power hm hmi using hmem
  refine ⟨∏ index ∈ witness, power index, ?_, denominator, hbI, hspan, ?_⟩
  · exact prime.primeCompl.prod_mem fun index hi ↦ hm index (ht ▸ Ideal.subset_span hi)
  · intro index hi
    have key : Ideal.span (witness : Set ring) ≤ (Ideal.span {denominator}).colon {∏ index ∈ witness, power index} := by
      refine Ideal.span_le.mpr fun secondIndex hj ↦ ?_
      rw [SetLike.mem_coe, Submodule.mem_colon_singleton, smul_eq_mul,
        mul_comm, ← Finset.prod_erase_mul witness power hj, mul_assoc]
      exact Ideal.mul_mem_left _ _ (hmi secondIndex (ht ▸ Ideal.subset_span hj))
    rw [← ht] at hi
    rw [mul_comm, ← smul_eq_mul, ← Submodule.mem_colon_singleton]
    exact key hi

theorem Ideal.map_eq_span_singleton_of_mul_mem_span_singleton {ring localizedRing : Type*} [CommRing ring]
    [CommRing localizedRing] [Algebra ring localizedRing] (generator : ring) [IsLocalization.Away generator localizedRing] {ideal : Ideal ring} {denominator : ring}
    (hb : denominator ∈ ideal) (compatibility : ∀ index ∈ ideal, generator * index ∈ Ideal.span {denominator}) :
    ideal.map (algebraMap ring localizedRing) = Ideal.span {algebraMap ring localizedRing denominator} := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun index hi ↦ ?_)
    ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hb))
  rw [Ideal.mem_comap, Ideal.mem_span_singleton]
  obtain ⟨factor, hc⟩ := Ideal.mem_span_singleton.mp (compatibility index hi)
  refine ((IsLocalization.Away.algebraMap_isUnit generator).dvd_mul_left).mp ⟨algebraMap ring localizedRing factor, ?_⟩
  rw [← map_mul, hc, map_mul]
