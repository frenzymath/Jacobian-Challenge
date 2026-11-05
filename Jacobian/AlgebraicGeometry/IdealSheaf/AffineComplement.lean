import Jacobian.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import Jacobian.AlgebraicGeometry.IdealSheaf.Twist
import Jacobian.RingTheory.Ideal.RegularPrincipal
import Jacobian.RingTheory.UniqueFactorizationDomain.Ideal
import Jacobian.RingTheory.Spectrum.Prime.MinimalPrimes
import Jacobian.RingTheory.Spectrum.Prime.Localization
import Jacobian.RingTheory.Localization.Principal
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal

/-!
# Cartier divisors with affine complement

On a noetherian separated integral scheme with factorial local rings, the
complement of a nonempty affine open is the support of an effective Cartier divisor.
-/

set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3



section
universe schemeUniverse

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

theorem Scheme.eq_top_of_isAffineOpen_of_not_le_basicOpen {source : Scheme.{schemeUniverse}} [IsAffine source]
    [IsIntegral source] [UniqueFactorizationMonoid Γ(source, ⊤)] {affineOpen : source.Opens} (hW : IsAffineOpen affineOpen)
    [Nonempty affineOpen] (compatibility : ∀ primeElement : Γ(source, ⊤), Prime primeElement → ¬affineOpen ≤ source.basicOpen primeElement) : affineOpen = ⊤ := by
  have : Nonempty (⊤ : source.Opens) := ⟨⟨(Nonempty.some ‹Nonempty affineOpen›).1, trivial⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen source ⊤ (isAffineOpen_top source)
  let restriction := source.presheaf.map (homOfLE le_top : affineOpen ⟶ ⊤).op
  have hρ : Function.Bijective restriction := by
    refine ⟨map_injective_of_isIntegral source _, fun localSection ↦ ?_⟩
    obtain ⟨numerator, denominator, hab, hs⟩ :=
      IsFractionRing.exists_reduced_fraction Γ(source, ⊤) (source.germToFunctionField affineOpen localSection)
    by_cases hb : IsUnit (denominator : Γ(source, ⊤))
    · refine ⟨numerator * ↑hb.unit⁻¹, source.germToFunctionField_injective affineOpen ?_⟩
      rw [← hs, source.presheaf.germ_res_apply, eq_comm, IsLocalization.mk'_eq_iff_eq_mul]
      calc algebraMap Γ(source, ⊤) source.functionField numerator
          = algebraMap Γ(source, ⊤) source.functionField (numerator * ↑hb.unit⁻¹ * denominator) := by
            rw [mul_assoc, hb.val_inv_mul, mul_one]
        _ = _ := map_mul _ _ _
    · exfalso
      obtain ⟨primeElement, hπirr, hπb⟩ :=
        WfDvdMonoid.exists_irreducible_factor hb (nonZeroDivisors.ne_zero denominator.2)
      have hπ := hπirr.prime
      obtain ⟨targetPoint, hyW, hyπ⟩ := Set.not_subset.mp (compatibility primeElement hπ)
      let := TopCat.Presheaf.algebra_section_stalk source.presheaf (⟨targetPoint, trivial⟩ : (⊤ : source.Opens))
      have := (isAffineOpen_top source).isLocalization_stalk ⟨targetPoint, trivial⟩
      obtain ⟨⟨factor, rank⟩, hcd⟩ := IsLocalization.mk'_surjective
        ((isAffineOpen_top source).primeIdealOf ⟨targetPoint, trivial⟩).asIdeal.primeCompl
        (source.presheaf.germ affineOpen targetPoint hyW localSection)
      have equivalence (localizer : Γ(source, ⊤)) :
          algebraMap Γ(source, ⊤) (source.presheaf.stalk targetPoint) localizer = source.presheaf.germ ⊤ targetPoint trivial localizer := rfl
      have e' (localizer : Γ(source, ⊤)) :
          source.germToFunctionField ⊤ localizer = algebraMap Γ(source, ⊤) source.functionField localizer := rfl
      have hπd : ¬primeElement ∣ (rank : Γ(source, ⊤)) := by
        refine fun hπd ↦ hyπ ((source.mem_basicOpen primeElement targetPoint trivial).mpr (isUnit_of_dvd_unit
          (map_dvd (source.presheaf.germ ⊤ targetPoint trivial).hom hπd) ?_))
        rw [← equivalence]
        exact IsLocalization.map_units _ rank
      have h1 := congrArg (algebraMap (source.presheaf.stalk targetPoint) source.functionField)
        (IsLocalization.mk'_spec (source.presheaf.stalk targetPoint) factor rank)
      dsimp only at hcd
      rw [hcd, equivalence, equivalence, map_mul, Scheme.algebraMap_germ_eq_germToFunctionField,
        Scheme.algebraMap_germ_eq_germToFunctionField,
        Scheme.algebraMap_germ_eq_germToFunctionField, ← hs, e', e'] at h1
      have h2 : numerator * rank = denominator * factor := IsFractionRing.injective Γ(source, ⊤) source.functionField (by
        rw [map_mul, map_mul, ← IsLocalization.mk'_spec source.functionField numerator denominator, ← h1]
        ring)
      obtain hπa | hπd' := hπ.dvd_or_dvd (h2 ▸ hπb.mul_right factor)
      · exact hπ.not_isUnit (hab hπa hπb)
      · exact hπd hπd'
  have : IsIso restriction := (ConcreteCategory.isIso_iff_bijective restriction).mpr hρ
  refine eq_top_iff.mpr fun point _ ↦ ?_
  obtain ⟨sourcePoint, hz⟩ : point ∈ Set.range (isAffineOpen_top source).fromSpec := by
    rw [IsAffineOpen.range_fromSpec]
    trivial
  obtain ⟨z', rfl⟩ := (ConcreteCategory.bijective_of_isIso (Spec.map restriction).base).2 sourcePoint
  rw [← SetLike.mem_coe, ← hW.range_fromSpec, ← hz]
  exact ⟨z', by rw [← Scheme.Hom.comp_apply, IsAffineOpen.map_fromSpec]⟩

theorem exists_prime_le_basicOpen_of_isAffineOpen (extensionRing : CommRingCat.{schemeUniverse}) [IsDomain extensionRing]
    [UniqueFactorizationMonoid extensionRing] {affineOpen : (Spec extensionRing).Opens} (hW : IsAffineOpen affineOpen)
    (hne : (affineOpen : Set (Spec extensionRing)).Nonempty) (hW' : affineOpen ≠ ⊤) :
    ∃ primeElement : extensionRing, Prime primeElement ∧ affineOpen ≤ PrimeSpectrum.basicOpen primeElement := by
  by_contra! H
  have : Nonempty affineOpen := hne.to_subtype
  have : UniqueFactorizationMonoid Γ(Spec extensionRing, ⊤) :=
    (Scheme.ΓSpecIso extensionRing).commRingCatIsoToRingEquiv.toMulEquiv.symm.uniqueFactorizationMonoid
      inferInstance
  refine hW' (Scheme.eq_top_of_isAffineOpen_of_not_le_basicOpen hW fun primeElement hπ hle ↦
    H ((Scheme.ΓSpecIso extensionRing).hom primeElement) ?_ ?_)
  · exact (MulEquiv.prime_iff
      (Scheme.ΓSpecIso extensionRing).commRingCatIsoToRingEquiv.toMulEquiv).mpr hπ
  · rwa [← basicOpen_eq_of_affine, Iso.hom_inv_id_apply]

theorem exists_prime_eq_span_of_mem_minimalPrimes (extensionRing : CommRingCat.{schemeUniverse}) [IsDomain extensionRing]
    [UniqueFactorizationMonoid extensionRing] {affineOpen : (Spec extensionRing).Opens} (hW : IsAffineOpen affineOpen)
    (hne : (affineOpen : Set (Spec extensionRing)).Nonempty) {localPrime : Ideal extensionRing}
    (hq : localPrime ∈ (PrimeSpectrum.vanishingIdeal (affineOpen : Set (Spec extensionRing))ᶜ).minimalPrimes) :
    ∃ primeElement : extensionRing, Prime primeElement ∧ localPrime = Ideal.span {primeElement} := by
  set ideal := PrimeSpectrum.vanishingIdeal (affineOpen : Set (Spec extensionRing))ᶜ
  have hqp : localPrime.IsPrime := hq.1.1
  have hmem (primeIdeal : PrimeSpectrum extensionRing) : ideal ≤ primeIdeal.asIdeal ↔ primeIdeal ∉ (affineOpen : Set (Spec extensionRing)) := by
    have := PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure (affineOpen : Set (Spec extensionRing))ᶜ
    rw [affineOpen.isOpen.isClosed_compl.closure_eq] at this
    exact (PrimeSpectrum.mem_zeroLocus primeIdeal ideal).symm.trans (Set.ext_iff.mp this primeIdeal)
  have hbot (primeIdeal : PrimeSpectrum extensionRing) (hP : primeIdeal.asIdeal = ⊥) : primeIdeal ∈ (affineOpen : Set (Spec extensionRing)) :=
    PrimeSpectrum.mem_of_isOpen_of_asIdeal_eq_bot affineOpen.isOpen hne hP
  have hq0 : localPrime ≠ ⊥ := fun compatibility ↦ (hmem ⟨localPrime, hqp⟩).mp hq.1.2 (hbot _ compatibility)
  obtain ⟨primeElement, hπq, hπ⟩ := hqp.exists_mem_prime_of_ne_bot hq0
  refine ⟨primeElement, hπ, ?_⟩
  let B' := CommRingCat.of (Localization.AtPrime localPrime)
  let ringMap : extensionRing ⟶ B' := CommRingCat.ofHom (algebraMap extensionRing (Localization.AtPrime localPrime))
  have hinj : Function.Injective (algebraMap extensionRing (Localization.AtPrime localPrime)) :=
    IsLocalization.injective _ localPrime.primeCompl_le_nonZeroDivisors
  have hφ (primeIdeal : Spec B') : (Spec.map ringMap primeIdeal).asIdeal = primeIdeal.asIdeal.under extensionRing := rfl
  have hmax : (IsLocalRing.closedPoint B').asIdeal.under extensionRing = localPrime :=
    Localization.AtPrime.under_maximalIdeal
  obtain ⟨π', hπ', hle⟩ := exists_prime_le_basicOpen_of_isAffineOpen B'
    (hW.preimage (Spec.map ringMap))
    ⟨⟨⊥, Ideal.isPrime_bot⟩, hbot _ (Ideal.comap_bot_of_injective _ hinj)⟩
    fun compatibility ↦ (hmem (Spec.map ringMap (IsLocalRing.closedPoint B'))).mp
      (le_of_le_of_eq hq.1.2 hmax.symm)
      (compatibility.symm ▸ trivial : IsLocalRing.closedPoint B' ∈ Spec.map ringMap ⁻¹ᵁ affineOpen)
  let otherPrime : PrimeSpectrum B' := ⟨_, (Ideal.span_singleton_prime hπ'.ne_zero).mpr hπ'⟩
  have hP' : otherPrime ∉ Spec.map ringMap ⁻¹ᵁ affineOpen := fun compatibility ↦ hle compatibility (Ideal.mem_span_singleton_self π')
  have hqP' : localPrime ≤ otherPrime.asIdeal.under extensionRing := by
    refine hq.2 ⟨(Spec.map ringMap otherPrime).isPrime, (hmem (Spec.map ringMap otherPrime)).mpr hP'⟩ ?_
    exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal otherPrime.2.ne_top)).trans hmax.le
  have hdisj : Disjoint (localPrime.primeCompl : Set extensionRing) (Ideal.span {primeElement}) := by
    refine Set.disjoint_left.mpr fun point hx hx' ↦ hx ?_
    exact (Ideal.span_singleton_le_iff_mem localPrime).mpr hπq hx'
  have hspan : (Ideal.span {primeElement}).map (algebraMap extensionRing (Localization.AtPrime localPrime)) =
      Ideal.span {algebraMap extensionRing _ primeElement} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hprime : Prime (algebraMap extensionRing (Localization.AtPrime localPrime) primeElement) := by
    refine (Ideal.span_singleton_prime ((map_ne_zero_iff _ hinj).mpr hπ.ne_zero)).mp ?_
    rw [← hspan]
    exact IsLocalization.isPrime_of_isPrime_disjoint localPrime.primeCompl _ _
      ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ) hdisj
  have hdvd : π' ∣ algebraMap extensionRing _ primeElement := Ideal.mem_span_singleton.mp (hqP' hπq)
  have hP'eq : otherPrime.asIdeal = Ideal.span {algebraMap extensionRing _ primeElement} :=
    Ideal.span_singleton_eq_span_singleton.mpr (hπ'.associated_of_dvd hprime hdvd)
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem localPrime).mpr hπq)
  rwa [hP'eq, ← hspan, IsLocalization.under_map_of_isPrime_disjoint localPrime.primeCompl _
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ) hdisj] at hqP'

theorem exists_vanishingIdeal_compl_eq_span (extensionRing : CommRingCat.{schemeUniverse}) [IsDomain extensionRing]
    [IsNoetherianRing extensionRing] [UniqueFactorizationMonoid extensionRing] {affineOpen : (Spec extensionRing).Opens}
    (hW : IsAffineOpen affineOpen) (hne : (affineOpen : Set (Spec extensionRing)).Nonempty) :
    ∃ morphism : extensionRing, morphism ≠ 0 ∧ PrimeSpectrum.vanishingIdeal (affineOpen : Set (Spec extensionRing))ᶜ = Ideal.span {morphism} :=
  (PrimeSpectrum.isRadical_vanishingIdeal _).exists_ne_zero_eq_span_singleton
    fun _ hq ↦ exists_prime_eq_span_of_mem_minimalPrimes extensionRing hW hne hq

theorem exists_notMem_mul_mem_span_vanishingIdeal_compl (baseRing : CommRingCat.{schemeUniverse}) [IsDomain baseRing]
    [IsNoetherianRing baseRing] {affineOpen : (Spec baseRing).Opens} (hW : IsAffineOpen affineOpen)
    (hne : (affineOpen : Set (Spec baseRing)).Nonempty) (prime : Ideal baseRing) [prime.IsPrime] (localizedRing : Type schemeUniverse) [CommRing localizedRing]
    [Algebra baseRing localizedRing] [IsLocalization.AtPrime localizedRing prime] [UniqueFactorizationMonoid localizedRing] :
    ∃ generator ∉ prime, ∃ denominator ∈ PrimeSpectrum.vanishingIdeal (affineOpen : Set (Spec baseRing))ᶜ, denominator ≠ 0 ∧
      ∀ index ∈ PrimeSpectrum.vanishingIdeal (affineOpen : Set (Spec baseRing))ᶜ, generator * index ∈ Ideal.span {denominator} := by
  have : IsDomain localizedRing := IsLocalization.isDomain_of_atPrime localizedRing prime
  have : IsNoetherianRing localizedRing := IsLocalization.isNoetherianRing prime.primeCompl localizedRing inferInstance
  let ringMap : baseRing ⟶ CommRingCat.of localizedRing := CommRingCat.ofHom (algebraMap baseRing localizedRing)
  have hinj : Function.Injective (algebraMap baseRing localizedRing) :=
    IsLocalization.injective localizedRing prime.primeCompl_le_nonZeroDivisors
  obtain ⟨morphism, hf0, hf⟩ := exists_vanishingIdeal_compl_eq_span (CommRingCat.of localizedRing)
    (hW.preimage (Spec.map ringMap)) ⟨⟨⊥, Ideal.isPrime_bot⟩,
      PrimeSpectrum.mem_of_isOpen_of_asIdeal_eq_bot affineOpen.isOpen hne
        (Ideal.comap_bot_of_injective _ hinj)⟩
  have hf' : (PrimeSpectrum.vanishingIdeal (affineOpen : Set (Spec baseRing))ᶜ).map (algebraMap baseRing localizedRing) =
      Ideal.span {morphism} :=
    (PrimeSpectrum.vanishingIdeal_preimage_comap_of_isLocalization prime.primeCompl
      affineOpen.isOpen.isClosed_compl).symm.trans hf
  obtain ⟨generator, hg, denominator, hb, hspan, hgb⟩ :=
    Ideal.exists_notMem_mul_mem_span_singleton_of_map_eq prime _ morphism hf'
  refine ⟨generator, hg, denominator, hb, ?_, hgb⟩
  rintro rfl
  exact hf0 (Ideal.span_singleton_eq_bot.mp (hf'.symm.trans (hspan.trans (by simp))))

@[stacks 0BCW]
theorem Scheme.exists_isInvertible_support_eq_compl (source : Scheme.{schemeUniverse}) [IsNoetherian source]
    [source.IsSeparated] [IsIntegral source]
    (hX : ∀ point : source, UniqueFactorizationMonoid (source.presheaf.stalk point))
    {openSubset : source.Opens} (hU : IsAffineOpen openSubset) (hne : (openSubset : Set source).Nonempty) :
    ∃ cartierIdeal : source.IdealSheafData, cartierIdeal.IsInvertible ∧ (cartierIdeal.support : Set source) = (openSubset : Set source)ᶜ := by
  refine ⟨IdealSheafData.vanishingIdeal ⟨(openSubset : Set source)ᶜ, openSubset.isOpen.isClosed_compl⟩,
    fun point ↦ ?_, IdealSheafData.coe_support_vanishingIdeal _⟩
  obtain ⟨targetOpen, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := point) (U := ⊤) trivial
  have : Nonempty targetOpen := ⟨⟨point, hxV⟩⟩
  have : IsAffineHom hV.fromSpec := IsAffineHom.of_comp hV.fromSpec (Limits.terminal.from source)
  have hWne : (hV.fromSpec ⁻¹ᵁ openSubset : Set (Spec Γ(source, targetOpen))).Nonempty := by
    obtain ⟨sourcePoint, hzU, hzV⟩ := nonempty_preirreducible_inter openSubset.isOpen targetOpen.isOpen hne ⟨point, hxV⟩
    obtain ⟨z', rfl⟩ : sourcePoint ∈ Set.range hV.fromSpec := hV.range_fromSpec ▸ hzV
    exact ⟨z', hzU⟩
  have := IsLocallyNoetherian.component_noetherian ⟨targetOpen, hV⟩
  let := TopCat.Presheaf.algebra_section_stalk source.presheaf ⟨point, hxV⟩
  have := hV.isLocalization_stalk ⟨point, hxV⟩
  have := hX point
  obtain ⟨generator, hg, denominator, hb, hb0, hgb⟩ := exists_notMem_mul_mem_span_vanishingIdeal_compl Γ(source, targetOpen)
    (hU.preimage hV.fromSpec) hWne (hV.primeIdealOf ⟨point, hxV⟩).asIdeal (source.presheaf.stalk point)
  have hx : point ∈ source.basicOpen generator :=
    (source.mem_basicOpen generator point hxV).mpr (IsLocalization.map_units (source.presheaf.stalk point)
      (M := (hV.primeIdealOf ⟨point, hxV⟩).asIdeal.primeCompl) ⟨generator, hg⟩)
  have : Nonempty (source.basicOpen generator) := ⟨⟨point, hx⟩⟩
  refine ⟨source.affineBasicOpen (U := ⟨targetOpen, hV⟩) generator, hx, ?_⟩
  let := (source.presheaf.map (homOfLE (source.basicOpen_le generator)).op).hom.toAlgebra
  have := hV.isLocalization_basicOpen generator
  have key : (IdealSheafData.vanishingIdeal ⟨(openSubset : Set source)ᶜ, openSubset.isOpen.isClosed_compl⟩).ideal
      (source.affineBasicOpen (U := ⟨targetOpen, hV⟩) generator) =
        Ideal.span {algebraMap Γ(source, targetOpen) Γ(source, source.basicOpen generator) denominator} := by
    rw [← IdealSheafData.map_ideal_basicOpen]
    exact Ideal.map_eq_span_singleton_of_mul_mem_span_singleton generator hb hgb
  rw [key]
  exact Ideal.isRegularPrincipal_span_singleton
    (mem_nonZeroDivisors_of_ne_zero (M₀ := Γ(source, source.basicOpen generator))
      ((map_ne_zero_iff _ (map_injective_of_isIntegral source _)).mpr hb0))

end AlgebraicGeometry
