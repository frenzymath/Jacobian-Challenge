import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Minimal primes and basic open neighbourhoods

A minimal prime is a generic point of an irreducible component. Localization at
such a prime gives basic open neighbourhoods disjoint from any prescribed
quasi-compact open not containing the point.
-/

namespace PrimeSpectrum

variable {ring : Type*} [CommSemiring ring]

/-- A point of `Spec ring` is the generic point of an irreducible component if and only if the
corresponding prime ideal is a minimal prime of `ring`. -/
@[stacks 00ES]
theorem mem_genericPoints_iff {prime : PrimeSpectrum ring} :
    prime ∈ genericPoints (PrimeSpectrum ring) ↔ prime.asIdeal ∈ minimalPrimes ring := by
  change closure ({prime} : Set (PrimeSpectrum ring)) ∈ irreducibleComponents (PrimeSpectrum ring) ↔ _
  rw [closure_singleton, zeroLocus_ideal_mem_irreducibleComponents, prime.2.radical]

end PrimeSpectrum

variable {ring : Type*} [CommRing ring]

/-- If `prime` is a minimal prime of `ring` and `point ∈ prime`, there are `otherPoint ∉ prime` and `exponent` with `otherPoint * point ^ exponent = 0`:
the localization `R_p` is zero-dimensional and local, so the image of `point` in `R_p` is nilpotent. -/
theorem Ideal.exists_notMem_mul_pow_eq_zero_of_mem_minimalPrimes {prime : Ideal ring}
    (hp : prime ∈ minimalPrimes ring) {point : ring} (hx : point ∈ prime) : ∃ otherPoint ∉ prime, ∃ exponent : ℕ, otherPoint * point ^ exponent = 0 := by
  have : prime.IsPrime := hp.1.1
  have : Ring.KrullDimLE 0 (Localization.AtPrime prime) := Ring.KrullDimLE.of_isLocalization prime hp _
  obtain ⟨exponent, hn⟩ : IsNilpotent (algebraMap ring (Localization.AtPrime prime) point) :=
    Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ prime point).mpr hx)
  rw [← map_pow] at hn
  obtain ⟨otherPoint, hy⟩ := (IsLocalization.map_eq_zero_iff prime.primeCompl _ _).mp hn
  exact ⟨otherPoint, otherPoint.2, exponent, hy⟩

namespace PrimeSpectrum

/-- A minimal prime `prime` of `ring` is separated from any quasi-compact open `excludedOpen` of `Spec ring` not
containing it by a basic open: there is `localSection ∉ prime` with `D(localSection) ∩ excludedOpen = ∅`. -/
@[stacks 00EV]
theorem exists_notMem_and_disjoint_basicOpen_of_mem_minimalPrimes {prime : PrimeSpectrum ring}
    (hp : prime.asIdeal ∈ minimalPrimes ring) {excludedOpen : Set (PrimeSpectrum ring)} (hW : IsOpen excludedOpen)
    (hW' : IsCompact excludedOpen) (hpW : prime ∉ excludedOpen) :
    ∃ localSection : ring, localSection ∉ prime.asIdeal ∧ Disjoint (basicOpen localSection : Set (PrimeSpectrum ring)) excludedOpen := by
  classical
  obtain ⟨remainingPoints, rfl⟩ := isCompact_isOpen_iff.mp ⟨hW', hW⟩
  rw [Set.notMem_compl_iff, mem_zeroLocus] at hpW
  choose points hs exponent hn using fun generator : {point // point ∈ remainingPoints} =>
    Ideal.exists_notMem_mul_pow_eq_zero_of_mem_minimalPrimes hp (hpW generator.2)
  refine ⟨∏ generator ∈ remainingPoints.attach, points generator, Submonoid.prod_mem prime.asIdeal.primeCompl fun generator _ ↦ hs generator, ?_⟩
  rw [Set.disjoint_compl_right_iff_subset]
  intro otherPrime hq
  rw [mem_zeroLocus]
  intro generator hg
  have hsg : points ⟨generator, hg⟩ ∉ otherPrime.asIdeal := fun witness ↦
    hq (otherPrime.asIdeal.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_attach _ ⟨generator, hg⟩)) witness)
  exact otherPrime.2.mem_of_pow_mem (exponent ⟨generator, hg⟩)
    ((otherPrime.2.mem_or_mem (hn ⟨generator, hg⟩ ▸ otherPrime.asIdeal.zero_mem)).resolve_left hsg)

end PrimeSpectrum
