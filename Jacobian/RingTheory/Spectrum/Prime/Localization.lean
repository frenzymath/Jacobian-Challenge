import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.Ideal

/-!
# Prime spectra and localization

Vanishing ideals extend under localization, and a prime with zero ideal belongs
to every nonempty open subset of the spectrum.
-/

namespace PrimeSpectrum

theorem vanishingIdeal_preimage_comap_of_isLocalization {ring localizedRing : Type*}
    [CommRing ring] [CommRing localizedRing] [Algebra ring localizedRing] (module : Submonoid ring) [IsLocalization module localizedRing]
    {Z : Set (PrimeSpectrum ring)} (hZ : IsClosed Z) :
    vanishingIdeal (comap (algebraMap ring localizedRing) ⁻¹' Z) = (vanishingIdeal Z).map (algebraMap ring localizedRing) := by
  obtain ⟨ideal, rfl⟩ := (isClosed_iff_zeroLocus_ideal Z).mp hZ
  rw [preimage_comap_zeroLocus, ← zeroLocus_span, ← Ideal.map,
    vanishingIdeal_zeroLocus_eq_radical, vanishingIdeal_zeroLocus_eq_radical,
    IsLocalization.map_radical module]

theorem mem_of_isOpen_of_asIdeal_eq_bot {ring : Type*} [CommRing ring]
    {affineOpen : Set (PrimeSpectrum ring)} (hW : IsOpen affineOpen) (hne : affineOpen.Nonempty) {primeIdeal : PrimeSpectrum ring}
    (hP : primeIdeal.asIdeal = ⊥) : primeIdeal ∈ affineOpen := by
  obtain ⟨member, hw⟩ := hne
  refine ((le_iff_specializes primeIdeal member).mp ?_).mem_open hW hw
  rw [← asIdeal_le_asIdeal, hP]
  exact bot_le

end PrimeSpectrum
