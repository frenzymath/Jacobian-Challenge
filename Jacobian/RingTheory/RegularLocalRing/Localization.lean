import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Localizations of regular rings

Localizing a regular ring preserves regularity.
-/

instance IsRegularRing.localization {R : Type*} [CommRing R] [IsRegularRing R] (M : Submonoid R) :
    IsRegularRing (Localization M) := by
  rw [isRegularRing_iff]
  intro p _
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M p).toRingEquiv
