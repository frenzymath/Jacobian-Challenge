import Jacobian.RingTheory.RegularLocalRing.Etale
import Jacobian.RingTheory.RegularLocalRing.Domain
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# Regularity of smooth algebras over a field

A smooth algebra is locally étale over a polynomial algebra. Regularity of
polynomial algebras over fields and preservation under étale maps therefore
give regular local rings at every prime.
-/

noncomputable section

namespace Algebra

/-- The local rings of a smooth algebra over a field are regular. -/
theorem Smooth.isRegularLocalRing_localization (baseField algebra : Type*)
    [Field baseField] [CommRing algebra] [Algebra baseField algebra]
    [Smooth baseField algebra] (prime : Ideal algebra) [prime.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime prime) := by
  obtain ⟨generators, spanning, standardSmooth⟩ :=
    Smooth.exists_span_eq_top_isStandardSmooth baseField algebra
  obtain ⟨element, membership, outside⟩ : ∃ element ∈ generators, element ∉ prime := by
    by_contra! contained
    exact Ideal.IsPrime.ne_top inferInstance
      (top_le_iff.mp (spanning ▸ Ideal.span_le.mpr contained :))
  obtain ⟨variableCount, etaleMap, _, etale⟩ :=
    (RingHom.isStandardSmooth_algebraMap.mpr (standardSmooth element membership)).exists_etale_mvPolynomial
  algebraize [etaleMap]
  have disjoint : Disjoint (Submonoid.powers element : Set algebra) prime := by
    rw [Set.disjoint_left]
    rintro _ ⟨exponent, rfl⟩ powerMembership
    exact outside (Ideal.IsPrime.mem_of_pow_mem inferInstance exponent powerMembership)
  let localizedPrime := prime.map (algebraMap algebra (Localization.Away element))
  have : localizedPrime.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers element) _ prime
      inferInstance disjoint
  have primeCondition : localizedPrime.comap (algebraMap algebra (Localization.Away element)) =
      prime :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers element)
      (Localization.Away element) inferInstance disjoint
  have := IsRegularLocalRing.localization_of_etale
    (baseRing := MvPolynomial (Fin variableCount) baseField) localizedPrime
  clear_value localizedPrime
  subst primeCondition
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Submonoid.powers element) localizedPrime).toRingEquiv.symm

/-- A smooth algebra over a field is a regular ring. -/
theorem Smooth.isRegularRing (baseField algebra : Type*) [Field baseField] [CommRing algebra]
    [Algebra baseField algebra] [Smooth baseField algebra] : IsRegularRing algebra := by
  have := Algebra.FiniteType.isNoetherianRing baseField algebra
  rw [isRegularRing_iff]
  intro prime _
  exact Smooth.isRegularLocalRing_localization baseField algebra prime

/-- A smooth algebra over a field is reduced. -/
theorem Smooth.isReduced_of_field (baseField algebra : Type*) [Field baseField]
    [CommRing algebra] [Algebra baseField algebra] [Smooth baseField algebra] :
    IsReduced algebra := by
  apply isReduced_ofLocalizationMaximal
  intro maximal maximalProperty
  have := Smooth.isRegularLocalRing_localization baseField algebra maximal
  infer_instance

end Algebra
