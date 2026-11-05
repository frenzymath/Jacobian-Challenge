import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# Invertible modules and localization

Invertibility can be checked on a principal-open cover. An invertible module whose
localization is a unique factorization domain is trivial after inverting one denominator.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open TensorProduct in
/-- **Invertibility is a local property.** A finitely presented `R`-module `M` such that for each
`r` in a family `s` generating the unit ideal the localization `M_r` is free of rank one over
`R_r` is invertible. -/
theorem Module.Invertible.of_isLocalized_span {baseRing moduleType : Type*} [CommRing baseRing] [AddCommGroup moduleType]
    [Module baseRing moduleType] [Module.FinitePresentation baseRing moduleType] (localizer : Set baseRing) (spn : Ideal.span localizer = ⊤)
    (Rₚ : localizer → Type*) [∀ element, CommRing (Rₚ element)] [∀ element, Algebra baseRing (Rₚ element)]
    [∀ element, IsLocalization.Away element.1 (Rₚ element)]
    (Mₚ : localizer → Type*) [∀ element, AddCommGroup (Mₚ element)] [∀ element, Module baseRing (Mₚ element)]
    [∀ element, Module (Rₚ element) (Mₚ element)] [∀ element, IsScalarTower baseRing (Rₚ element) (Mₚ element)]
    (localizationMap : ∀ element, moduleType →ₗ[baseRing] Mₚ element) [∀ element, IsLocalizedModule.Away element.1 (localizationMap element)]
    (bijectiveLocalization : ∀ element, Nonempty (Mₚ element ≃ₗ[Rₚ element] Rₚ element)) : Module.Invertible baseRing moduleType := by
  let dl (element : localizer) : Module.Dual baseRing moduleType →ₗ[baseRing] Module.Dual (Rₚ element) (Mₚ element) :=
    IsLocalizedModule.mapExtendScalars (.powers element.1) (localizationMap element) (Algebra.linearMap baseRing (Rₚ element)) (Rₚ element)
  let trivialization (element : localizer) := IsLocalization.moduleTensorEquiv (.powers element.1) (Rₚ element)
    (Module.Dual (Rₚ element) (Mₚ element)) (Mₚ element)
  refine ⟨bijective_of_isLocalized_span localizer spn
    (fun element ↦ Module.Dual (Rₚ element) (Mₚ element) ⊗[baseRing] Mₚ element) (fun element ↦ map (dl element) (localizationMap element))
    Rₚ (fun element ↦ Algebra.linearMap baseRing (Rₚ element)) _ fun element ↦ ?_⟩
  have : Module.Invertible (Rₚ element) (Mₚ element) := .congr (bijectiveLocalization element).some.symm
  have hmap : IsLocalizedModule.map (.powers element.1) (map (dl element) (localizationMap element))
      (Algebra.linearMap baseRing (Rₚ element)) (contractLeft baseRing moduleType) =
      ((contractLeft (Rₚ element) (Mₚ element)).restrictScalars baseRing) ∘ₗ
        ((trivialization element).symm.restrictScalars baseRing).toLinearMap := by
    refine IsLocalizedModule.linearMap_ext (.powers element.1) (map (dl element) (localizationMap element))
      (Algebra.linearMap baseRing (Rₚ element)) ?_
    rw [IsLocalizedModule.map_comp]
    ext functional generator
    exact (IsLocalizedModule.map_apply (.powers element.1) (localizationMap element)
      (Algebra.linearMap baseRing (Rₚ element)) functional generator).symm
  rw [hmap]
  exact (Module.Invertible.bijective (R := Rₚ element) (M := Mₚ element)).comp (trivialization element).symm.bijective

/-- The localization of the map `r ↦ r • m` is the map `a ↦ a • f m`. -/
theorem IsLocalizedModule.map_toSpanSingleton {baseRing moduleType : Type*} [CommRing baseRing] [AddCommGroup moduleType]
    [Module baseRing moduleType] (denominators : Submonoid baseRing) (Rₛ : Type*) [CommRing Rₛ] [Algebra baseRing Rₛ] [IsLocalization denominators Rₛ]
    {Mₛ : Type*} [AddCommGroup Mₛ] [Module baseRing Mₛ] [Module Rₛ Mₛ] [IsScalarTower baseRing Rₛ Mₛ]
    (localizationMap : moduleType →ₗ[baseRing] Mₛ) [IsLocalizedModule denominators localizationMap] (generator : moduleType) :
    IsLocalizedModule.map denominators (Algebra.linearMap baseRing Rₛ) localizationMap (LinearMap.toSpanSingleton baseRing moduleType generator) =
      (LinearMap.toSpanSingleton Rₛ Mₛ (localizationMap generator)).restrictScalars baseRing := by
  refine IsLocalizedModule.linearMap_ext denominators (Algebra.linearMap baseRing Rₛ) localizationMap ?_
  rw [IsLocalizedModule.map_comp]
  ext
  simp

/-- **Spreading out the triviality of an invertible module.** Let `S` be a submonoid of `R` such
that the localization `R_S` is a unique factorization domain, so that every invertible
`R_S`-module is free (Stacks 0BCH). Then an invertible `R`-module `M` becomes free of rank one
after inverting a single element `s ∈ S`: there is `m ∈ M` such that `r ↦ r • m` is a bijection
`R_s ≃ M_s`, for any localizations `R_s` of `R` and `M_s` of `M` at the powers of `s`. -/
theorem Module.Invertible.exists_mem_bijective_smul {baseRing moduleType : Type*} [CommRing baseRing] [AddCommGroup moduleType]
    [Module baseRing moduleType] [Module.Invertible baseRing moduleType] (denominators : Submonoid baseRing) [IsDomain (Localization denominators)]
    [UniqueFactorizationMonoid (Localization denominators)] :
    ∃ localizer ∈ denominators, ∃ generator : moduleType, ∀ (Rₛ : Type*) [CommRing Rₛ] [Algebra baseRing Rₛ] [IsLocalization.Away localizer Rₛ]
      (Mₛ : Type*) [AddCommGroup Mₛ] [Module baseRing Mₛ] [Module Rₛ Mₛ] [IsScalarTower baseRing Rₛ Mₛ]
      (localizationMap : moduleType →ₗ[baseRing] Mₛ) [IsLocalizedModule.Away localizer localizationMap], Function.Bijective fun element : Rₛ ↦ element • localizationMap generator := by
  have : IsGCDMonoid (Localization denominators) := ⟨UniqueFactorizationMonoid.toGCDMonoid _⟩
  have := Module.finitePresentation_of_projective baseRing moduleType
  obtain ⟨trivialization⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free (Localization denominators) (LocalizedModule denominators moduleType))
  obtain ⟨generator, denominator, hx⟩ : ∃ generator denominator, LocalizedModule.mk generator denominator = trivialization.symm 1 := by
    induction trivialization.symm 1 using LocalizedModule.induction_on with
    | h generator denominator => exact ⟨generator, denominator, rfl⟩
  have hsurj : Function.Surjective
      (LinearMap.toSpanSingleton (Localization denominators) _ (LocalizedModule.mk generator (1 : denominators))) := by
    intro localizedElement
    refine ⟨trivialization localizedElement * Localization.mk 1 denominator, ?_⟩
    rw [LinearMap.toSpanSingleton_apply, mul_smul, LocalizedModule.mk_smul_mk, one_smul, mul_one,
      hx, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  obtain ⟨localizer, hs, bijectiveLocalization⟩ := exists_bijective_map_powers denominators (Algebra.linearMap baseRing (Localization denominators))
    (LocalizedModule.mkLinearMap denominators moduleType) (LinearMap.toSpanSingleton baseRing moduleType generator) (by
      rw [IsLocalizedModule.map_toSpanSingleton]
      exact Module.Invertible.bijective_of_surjective (R := Localization denominators) hsurj)
  refine ⟨localizer, hs, generator, fun Rₛ _ _ _ Mₛ _ _ _ _ localizationMap _ ↦ ?_⟩
  have := (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (Algebra.linearMap baseRing Rₛ) localizationMap).mpr (bijectiveLocalization localizer dvd_rfl)
  rwa [IsLocalizedModule.map_toSpanSingleton] at this
