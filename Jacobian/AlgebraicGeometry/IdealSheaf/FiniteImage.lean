import Jacobian.AlgebraicGeometry.IdealSheaf.Image
import Jacobian.AlgebraicGeometry.IdealSheaf.AffineComplement
import Jacobian.RingTheory.Ideal.LocalPrincipal
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Images of effective Cartier divisors

For a finite flat morphism locally of finite presentation to an integral locally
noetherian scheme with factorial local rings, the image of an effective Cartier
divisor is the support of an effective Cartier divisor. Locally its equation is
the norm of an equation of the original divisor.
-/

set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3



section
universe schemeUniverse

open CategoryTheory TopologicalSpace


namespace AlgebraicGeometry

variable {source target : Scheme.{schemeUniverse}}

lemma Scheme.IdealSheafData.IsInvertible.exists_notMem_mul_mem_span_singleton
    {cartierIdeal : source.IdealSheafData} (hJ : cartierIdeal.IsInvertible) (openSubset : source.affineOpens) (hU : (cartierIdeal.ideal openSubset).FG)
    (localPrime : Ideal Γ(source, openSubset)) [localPrime.IsPrime] :
    ∃ witness ∉ localPrime, ∃ point ∈ cartierIdeal.ideal openSubset, (∀ index ∈ cartierIdeal.ideal openSubset, witness * index ∈ Ideal.span {point}) ∧
      ∀ denominator, point * denominator = 0 → ∃ exponent : ℕ, witness ^ exponent * denominator = 0 := by
  have hzU : openSubset.2.fromSpec ⟨localPrime, inferInstance⟩ ∈ openSubset.1 := openSubset.2.range_fromSpec.le ⟨_, rfl⟩
  obtain ⟨affineOpen, hzW, σ, hσ, hWσ⟩ := hJ (openSubset.2.fromSpec ⟨localPrime, inferInstance⟩)
  obtain ⟨witness, t', htt', hzt⟩ := exists_basicOpen_le_affine_inter openSubset.2 affineOpen.2 _ ⟨hzU, hzW⟩
  have htq : witness ∉ localPrime := by
    have : (⟨localPrime, inferInstance⟩ : PrimeSpectrum Γ(source, openSubset)) ∈ openSubset.2.fromSpec ⁻¹ᵁ source.basicOpen witness := hzt
    rwa [openSubset.2.fromSpec_preimage_basicOpen] at this
  have hle : source.basicOpen witness ≤ affineOpen.1 := htt' ▸ source.basicOpen_le t'
  have hρσ : (source.presheaf.map (homOfLE hle).op).hom σ ∈ nonZeroDivisors Γ(source, source.basicOpen witness) := by
    let := (source.presheaf.map (homOfLE hle).op).hom.toAlgebra
    have := affineOpen.2.isLocalization_of_eq_basicOpen t' (homOfLE hle) htt'
    exact IsLocalization.map_nonZeroDivisors_le (Submonoid.powers t') _
      (Submonoid.mem_map_of_mem _ hσ)
  let := (source.presheaf.map (homOfLE (source.basicOpen_le witness)).op).hom.toAlgebra
  have := openSubset.2.isLocalization_basicOpen witness
  have h1 : (cartierIdeal.ideal openSubset).map (algebraMap Γ(source, openSubset) Γ(source, source.basicOpen witness)) =
      Ideal.span {(source.presheaf.map (homOfLE hle).op).hom σ} := by
    rw [RingHom.algebraMap_toAlgebra, cartierIdeal.map_ideal_basicOpen,
      ← cartierIdeal.map_ideal (U := source.affineBasicOpen witness) (V := affineOpen) hle, hWσ, Ideal.map_span,
      Set.image_singleton]
    rfl
  obtain ⟨_, ⟨indexBound, rfl⟩, point, hxI, hxspan, hxm⟩ :=
    Ideal.exists_mem_mul_mem_span_singleton_of_map_eq (.powers witness) hU h1
  have hx : algebraMap Γ(source, openSubset) Γ(source, source.basicOpen witness) point ∈ nonZeroDivisors _ := by
    have : (source.presheaf.map (homOfLE hle).op).hom σ ∈
        Ideal.span {algebraMap Γ(source, openSubset) Γ(source, source.basicOpen witness) point} := by
      rw [← hxspan, h1]
      exact Ideal.mem_span_singleton_self _
    obtain ⟨rank, hd⟩ := Ideal.mem_span_singleton'.mp this
    refine mem_nonZeroDivisors_iff_right.mpr fun targetPoint hy ↦
      mem_nonZeroDivisors_iff_right.mp hρσ targetPoint ?_
    rw [← hd, mul_left_comm, hy, mul_zero]
  refine ⟨witness ^ (indexBound + 1), fun compatibility ↦ htq (‹localPrime.IsPrime›.mem_of_pow_mem _ compatibility), point, hxI, fun index hi ↦ ?_,
    fun denominator hb ↦ ?_⟩
  · rw [pow_succ', mul_assoc]
    exact Ideal.mul_mem_left _ _ (hxm index hi)
  · have : algebraMap Γ(source, openSubset) Γ(source, source.basicOpen witness) denominator = 0 :=
      mem_nonZeroDivisors_iff_right.mp hx _ (by rw [mul_comm, ← map_mul, hb, map_zero])
    obtain ⟨⟨_, exponent, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (.powers witness) _ denominator).mp this
    have hn' : witness ^ exponent * denominator = 0 := hn
    exact ⟨exponent, by rw [← pow_mul, mul_comm (indexBound + 1) exponent, pow_mul, pow_succ, mul_assoc, hn', mul_zero]⟩

theorem Scheme.isInvertible_vanishingIdeal_of_forall_eq_compl_basicOpen (target : Scheme.{schemeUniverse})
    [IsLocallyNoetherian target] [IsIntegral target]
    (hY : ∀ targetPoint : target, UniqueFactorizationMonoid (target.presheaf.stalk targetPoint)) {Z : Set target}
    (hZ : IsClosed Z) (compatibility : ∀ targetPoint : target, ∃ targetOpen : target.affineOpens, targetPoint ∈ targetOpen.1 ∧ ∃ numerator : Γ(target, targetOpen), numerator ≠ 0 ∧
      Z ∩ (targetOpen.1 : Set target) = (target.basicOpen numerator : Set target)ᶜ ∩ targetOpen.1) :
    (IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).IsInvertible := by
  intro targetPoint
  obtain ⟨⟨targetOpen, hV⟩, hyV, numerator, ha, hZV⟩ := compatibility targetPoint
  have : Nonempty targetOpen := ⟨⟨targetPoint, hyV⟩⟩
  have := IsLocallyNoetherian.component_noetherian ⟨targetOpen, hV⟩
  have hI : (IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).ideal ⟨targetOpen, hV⟩ =
      (Ideal.span {numerator}).radical := by
    rw [IdealSheafData.vanishingIdeal_ideal, ← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
      PrimeSpectrum.zeroLocus_span]
    congr 1
    ext primeIdeal
    have hPV : hV.fromSpec primeIdeal ∈ targetOpen := hV.range_fromSpec.le ⟨primeIdeal, rfl⟩
    have hmem : hV.fromSpec primeIdeal ∈ Z ↔ hV.fromSpec primeIdeal ∉ target.basicOpen numerator := by
      simpa [hPV] using congr(hV.fromSpec primeIdeal ∈ $hZV)
    have hbo : hV.fromSpec primeIdeal ∈ target.basicOpen numerator ↔ primeIdeal ∈ PrimeSpectrum.basicOpen numerator := by
      rw [← hV.fromSpec_preimage_basicOpen]
      rfl
    rw [Set.mem_preimage, Closeds.coe_mk, hmem, hbo, PrimeSpectrum.mem_basicOpen, not_not,
      PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
  let := TopCat.Presheaf.algebra_section_stalk target.presheaf ⟨targetPoint, hyV⟩
  have := hV.isLocalization_stalk ⟨targetPoint, hyV⟩
  have := hY targetPoint
  obtain ⟨generator, hg, denominator, hb, hb0, hgb⟩ := Ideal.exists_notMem_mul_mem_span_radical_span_singleton
    (hV.primeIdealOf ⟨targetPoint, hyV⟩).asIdeal (target.presheaf.stalk targetPoint) ha
  have hx : targetPoint ∈ target.basicOpen generator :=
    (target.mem_basicOpen generator targetPoint hyV).mpr (IsLocalization.map_units (target.presheaf.stalk targetPoint)
      (M := (hV.primeIdealOf ⟨targetPoint, hyV⟩).asIdeal.primeCompl) ⟨generator, hg⟩)
  have : Nonempty (target.basicOpen generator) := ⟨⟨targetPoint, hx⟩⟩
  refine ⟨target.affineBasicOpen (U := ⟨targetOpen, hV⟩) generator, hx, ?_⟩
  let := (target.presheaf.map (homOfLE (target.basicOpen_le generator)).op).hom.toAlgebra
  have := hV.isLocalization_basicOpen generator
  have key : (IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).ideal (target.affineBasicOpen (U := ⟨targetOpen, hV⟩) generator) =
      Ideal.span {algebraMap Γ(target, targetOpen) Γ(target, target.basicOpen generator) denominator} := by
    rw [← IdealSheafData.map_ideal_basicOpen, hI]
    exact Ideal.map_eq_span_singleton_of_mul_mem_span_singleton generator hb hgb
  rw [key]
  exact Ideal.isRegularPrincipal_span_singleton
    (mem_nonZeroDivisors_of_ne_zero (M₀ := Γ(target, target.basicOpen generator))
      ((map_ne_zero_iff _ (map_injective_of_isIntegral target _)).mpr hb0))

theorem Scheme.exists_isInvertible_support_eq_of_forall_eq_compl_basicOpen (target : Scheme.{schemeUniverse})
    [IsLocallyNoetherian target] [IsIntegral target]
    (hY : ∀ targetPoint : target, UniqueFactorizationMonoid (target.presheaf.stalk targetPoint)) {Z : Set target}
    (hZ : IsClosed Z) (compatibility : ∀ targetPoint : target, ∃ targetOpen : target.affineOpens, targetPoint ∈ targetOpen.1 ∧ ∃ numerator : Γ(target, targetOpen), numerator ≠ 0 ∧
      Z ∩ (targetOpen.1 : Set target) = (target.basicOpen numerator : Set target)ᶜ ∩ targetOpen.1) :
    ∃ imageIdeal : target.IdealSheafData, imageIdeal.IsInvertible ∧ (imageIdeal.support : Set target) = Z :=
  ⟨_, target.isInvertible_vanishingIdeal_of_forall_eq_compl_basicOpen hY hZ compatibility,
    IdealSheafData.coe_support_vanishingIdeal _⟩

lemma IsAffineOpen.fromSpec_mem_basicOpen_iff {openSubset : source.Opens} (hU : IsAffineOpen openSubset)
    (primeIdeal : PrimeSpectrum Γ(source, openSubset)) (localizer : Γ(source, openSubset)) :
    hU.fromSpec primeIdeal ∈ source.basicOpen localizer ↔ localizer ∉ primeIdeal.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← hU.fromSpec_preimage_basicOpen]
  rfl

lemma Scheme.IdealSheafData.fromSpec_mem_support_iff (cartierIdeal : source.IdealSheafData)
    (openSubset : source.affineOpens) (primeIdeal : PrimeSpectrum Γ(source, openSubset)) :
    openSubset.2.fromSpec primeIdeal ∈ cartierIdeal.support ↔ cartierIdeal.ideal openSubset ≤ primeIdeal.asIdeal := by
  rw [mem_support_iff_of_mem (openSubset.2.range_fromSpec.le ⟨primeIdeal, rfl⟩), Scheme.mem_zeroLocus_iff]
  refine forall₂_congr fun index _ ↦ ?_
  rw [openSubset.2.fromSpec_mem_basicOpen_iff, not_not]

lemma Scheme.IdealSheafData.fromSpec_mem_image_support_iff (morphism : source ⟶ target) {targetOpen : target.Opens}
    (hV : IsAffineOpen targetOpen) (hU : IsAffineOpen (morphism ⁻¹ᵁ targetOpen)) (cartierIdeal : source.IdealSheafData)
    (primeIdeal : PrimeSpectrum Γ(target, targetOpen)) :
    hV.fromSpec primeIdeal ∈ morphism.base '' (cartierIdeal.support : Set source) ↔ ∃ localPrime : Ideal Γ(source, morphism ⁻¹ᵁ targetOpen), localPrime.IsPrime ∧
      localPrime.comap (morphism.appLE targetOpen (morphism ⁻¹ᵁ targetOpen) le_rfl).hom = primeIdeal.asIdeal ∧ cartierIdeal.ideal ⟨_, hU⟩ ≤ localPrime := by
  have key (lyingPrime : PrimeSpectrum Γ(source, morphism ⁻¹ᵁ targetOpen)) :
      morphism (hU.fromSpec lyingPrime) = hV.fromSpec (Spec.map (morphism.appLE targetOpen (morphism ⁻¹ᵁ targetOpen) le_rfl) lyingPrime) := by
    rw [← Scheme.Hom.comp_apply, ← IsAffineOpen.SpecMap_appLE_fromSpec morphism hV hU le_rfl,
      Scheme.Hom.comp_apply]
  constructor
  · rintro ⟨point, hx, hxP⟩
    have hxU : point ∈ morphism ⁻¹ᵁ targetOpen := by
      rw [Scheme.Hom.mem_preimage, hxP]
      exact hV.range_fromSpec.le ⟨primeIdeal, rfl⟩
    obtain ⟨lyingPrime, rfl⟩ : point ∈ Set.range hU.fromSpec := hU.range_fromSpec ▸ hxU
    refine ⟨lyingPrime.asIdeal, lyingPrime.2, ?_, (cartierIdeal.fromSpec_mem_support_iff ⟨_, hU⟩ lyingPrime).mp hx⟩
    rw [key] at hxP
    exact congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective hxP)
  · rintro ⟨localPrime, hq, hqP, hJq⟩
    refine ⟨hU.fromSpec ⟨localPrime, hq⟩, (cartierIdeal.fromSpec_mem_support_iff ⟨_, hU⟩ ⟨localPrime, hq⟩).mpr hJq, ?_⟩
    rw [key]
    congr 1
    exact PrimeSpectrum.ext hqP

theorem Scheme.Hom.exists_isInvertible_support_eq_image {source target : Scheme.{schemeUniverse}} (morphism : source ⟶ target)
    [IsFinite morphism] [Flat morphism] [LocallyOfFinitePresentation morphism] [IsLocallyNoetherian target]
    [IsIntegral target] (hY : ∀ targetPoint : target, UniqueFactorizationMonoid (target.presheaf.stalk targetPoint))
    {cartierIdeal : source.IdealSheafData} (hJ : cartierIdeal.IsInvertible) :
    ∃ imageIdeal : target.IdealSheafData, imageIdeal.IsInvertible ∧
      (imageIdeal.support : Set target) = morphism.base '' (cartierIdeal.support : Set source) := by
  have hZ : IsClosed (morphism.base '' (cartierIdeal.support : Set source)) := morphism.isClosedMap _ cartierIdeal.support.isClosed
  refine target.exists_isInvertible_support_eq_of_forall_eq_compl_basicOpen hY hZ fun targetPoint ↦ ?_
  obtain ⟨targetOpen, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (x := targetPoint) (U := ⊤) trivial
  have hU : IsAffineOpen (morphism ⁻¹ᵁ targetOpen) := hV.preimage morphism
  have := IsLocallyNoetherian.component_noetherian ⟨targetOpen, hV⟩
  have : Nonempty targetOpen := ⟨⟨targetPoint, hyV⟩⟩
  let := (morphism.appLE targetOpen (morphism ⁻¹ᵁ targetOpen) le_rfl).hom.toAlgebra
  have : Module.Finite Γ(target, targetOpen) Γ(source, morphism ⁻¹ᵁ targetOpen) := by
    have := morphism.finite_app targetOpen hV
    rwa [← morphism.appLE_eq_app] at this
  have : Module.Flat Γ(target, targetOpen) Γ(source, morphism ⁻¹ᵁ targetOpen) := morphism.flat_appLE hV hU le_rfl
  have : Algebra.FinitePresentation Γ(target, targetOpen) Γ(source, morphism ⁻¹ᵁ targetOpen) :=
    HasRingHomProperty.appLE @LocallyOfFinitePresentation morphism ‹_› ⟨targetOpen, hV⟩ ⟨_, hU⟩ le_rfl
  have : Module.FinitePresentation Γ(target, targetOpen) Γ(source, morphism ⁻¹ᵁ targetOpen) :=
    .of_finite_of_finitePresentation _ _
  have : IsNoetherianRing Γ(source, morphism ⁻¹ᵁ targetOpen) := isNoetherian_of_tower Γ(target, targetOpen) inferInstance
  obtain ⟨primeIdeal, rfl⟩ : targetPoint ∈ Set.range hV.fromSpec := hV.range_fromSpec ▸ hyV
  obtain ⟨localSection, hs, numerator, ha, hiff⟩ := Ideal.exists_ne_zero_mem_iff_exists_le (cartierIdeal.ideal ⟨_, hU⟩)
    (fun localPrime _ ↦ hJ.exists_notMem_mul_mem_span_singleton ⟨_, hU⟩ (IsNoetherian.noetherian _) localPrime)
    primeIdeal.asIdeal
  have hys : hV.fromSpec primeIdeal ∈ target.basicOpen localSection := (hV.fromSpec_mem_basicOpen_iff primeIdeal localSection).mpr hs
  have : Nonempty (target.basicOpen localSection) := ⟨⟨_, hys⟩⟩
  refine ⟨target.affineBasicOpen (U := ⟨targetOpen, hV⟩) localSection, hys,
    target.presheaf.map (homOfLE (target.basicOpen_le localSection)).op numerator,
    (map_ne_zero_iff _ (map_injective_of_isIntegral target _)).mpr ha, ?_⟩
  have hres : target.basicOpen (target.presheaf.map (homOfLE (target.basicOpen_le localSection)).op numerator) =
      target.basicOpen localSection ⊓ target.basicOpen numerator := target.basicOpen_res _ _
  ext y'
  rw [hres, Set.mem_inter_iff, Set.mem_inter_iff,
    Set.mem_compl_iff]
  refine and_congr_left fun hy' ↦ ?_
  obtain ⟨otherPrime, rfl⟩ : y' ∈ Set.range hV.fromSpec :=
    hV.range_fromSpec ▸ target.basicOpen_le localSection hy'
  have hsP' : localSection ∉ otherPrime.asIdeal := (hV.fromSpec_mem_basicOpen_iff otherPrime localSection).mp hy'
  rw [IdealSheafData.fromSpec_mem_image_support_iff morphism hV hU, Opens.coe_inf, Set.mem_inter_iff]
  refine (hiff otherPrime.asIdeal otherPrime.2 hsP').symm.trans
    ⟨fun compatibility ⟨_, hB⟩ ↦ (hV.fromSpec_mem_basicOpen_iff otherPrime numerator).mp hB compatibility, fun compatibility ↦ ?_⟩
  by_contra ha
  exact compatibility ⟨hy', (hV.fromSpec_mem_basicOpen_iff otherPrime numerator).mpr ha⟩
end AlgebraicGeometry
