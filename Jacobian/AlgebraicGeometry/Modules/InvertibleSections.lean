import Jacobian.RingTheory.PicardGroup.Localization
import Jacobian.AlgebraicGeometry.Modules.LocallyFreeAffine
import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Local

/-!
# Affine sections of line bundles

Sections of a line bundle on an affine open form an invertible module. A factorial
localization therefore supplies a trivialization on a principal neighborhood.
-/

set_option backward.isDefEq.respectTransparency false

section
universe schemeUniverse

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{schemeUniverse}}

/-- **Sections of an invertible module over an affine open are an invertible module.** For an
invertible `𝒪_X`-module `M` and an affine open `U`, `Γ(M, U)` is finitely presented and free of
rank one locally on `Spec Γ(X, U)` (on the basic opens trivializing `M`), hence invertible. -/
theorem invertible_sections_of_isAffineOpen (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible] {openSubset : scheme.Opens}
    (hU : IsAffineOpen openSubset) : Module.Invertible Γ(scheme, openSubset) Γ(moduleSheaf, openSubset) := by
  have := (finitePresentation_projective_sections moduleSheaf hU).1
  let localizers : Set Γ(scheme, openSubset) := {localizer | ∃ trivializingOpen : scheme.Opens, scheme.basicOpen localizer ≤ trivializingOpen ∧
    Nonempty (moduleSheaf.over trivializingOpen ≅ SheafOfModules.unit (scheme.ringCatSheaf.over trivializingOpen))}
  have hs : Ideal.span localizers = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro point hx
    obtain ⟨trivializingOpen, hxY, ⟨generator⟩⟩ := exists_mem_over_iso_unit moduleSheaf point
    obtain ⟨localizer, hgY, hxg⟩ := hU.exists_basicOpen_le ⟨point, hxY⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨localizer, trivializingOpen, hgY, ⟨generator⟩⟩, hxg⟩
  let _ (scalar : localizers) : Module Γ(scheme, openSubset) Γ(moduleSheaf, scheme.basicOpen scalar.1) :=
    Module.compHom _ (algebraMap Γ(scheme, openSubset) Γ(scheme, scheme.basicOpen scalar.1))
  have _ (scalar : localizers) := isLocalizedModule_basicOpen moduleSheaf hU scalar.1
  have _ (scalar : localizers) := hU.isLocalization_basicOpen scalar.1
  have _ (scalar : localizers) : IsScalarTower Γ(scheme, openSubset) Γ(scheme, scheme.basicOpen scalar.1) Γ(moduleSheaf, scheme.basicOpen scalar.1) :=
    ⟨fun coefficient inverseCoefficient sectionValue ↦ mul_smul _ _ _⟩
  refine Module.Invertible.of_isLocalized_span localizers hs (fun scalar ↦ Γ(scheme, scheme.basicOpen scalar.1))
    (fun scalar ↦ Γ(moduleSheaf, scheme.basicOpen scalar.1)) (fun scalar ↦
      { toFun := moduleSheaf.presheaf.map (homOfLE (scheme.basicOpen_le scalar.1)).op
        map_add' := map_add _
        map_smul' := map_smul moduleSheaf _ }) fun scalar ↦ ?_
  obtain ⟨trivializingOpen, hY, ⟨generator⟩⟩ := scalar.2
  exact ⟨sectionsLinearEquivOfOverIsoUnit generator hY⟩

/-- Let `M` be quasi-coherent, `U` an affine open and `e ∈ Γ(M, U)` such that `r ↦ r • e` is a
bijection `Γ(X, U) ≃ Γ(M, U)`. Then for every `g ∈ Γ(X, U)`, `r ↦ r • e|_{D(g)}` is a bijection
`Γ(X, D(g)) ≃ Γ(M, D(g))`, being the localization at `g` of the former bijection. -/
lemma bijective_smul_map_basicOpen (moduleSheaf : scheme.Modules)
    [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) moduleSheaf] {openSubset : scheme.Opens} (hU : IsAffineOpen openSubset)
    {generator : Γ(moduleSheaf, openSubset)} (he : Function.Bijective fun scalar : Γ(scheme, openSubset) ↦ scalar • generator) (localizer : Γ(scheme, openSubset)) :
    Function.Bijective fun scalar : Γ(scheme, scheme.basicOpen localizer) ↦
      scalar • moduleSheaf.presheaf.map (homOfLE (scheme.basicOpen_le localizer)).op generator := by
  let : Module Γ(scheme, openSubset) Γ(moduleSheaf, scheme.basicOpen localizer) :=
    Module.compHom _ (algebraMap Γ(scheme, openSubset) Γ(scheme, scheme.basicOpen localizer))
  have := isLocalizedModule_basicOpen moduleSheaf hU localizer
  have := hU.isLocalization_basicOpen localizer
  let ψ : Γ(scheme, scheme.basicOpen localizer) →ₗ[Γ(scheme, openSubset)] Γ(moduleSheaf, scheme.basicOpen localizer) :=
    { toFun scalar := scalar • moduleSheaf.presheaf.map (homOfLE (scheme.basicOpen_le localizer)).op generator
      map_add' coefficient inverseCoefficient := add_smul coefficient inverseCoefficient _
      map_smul' coefficient scalar := mul_smul _ _ _ }
  let res : Γ(moduleSheaf, openSubset) →ₗ[Γ(scheme, openSubset)] Γ(moduleSheaf, scheme.basicOpen localizer) :=
    { toFun := moduleSheaf.presheaf.map (homOfLE (scheme.basicOpen_le localizer)).op
      map_add' := map_add _
      map_smul' := map_smul moduleSheaf _ }
  have hψ : ψ = IsLocalizedModule.map (.powers localizer) (Algebra.linearMap _ _) res
      (LinearMap.toSpanSingleton _ _ generator) := by
    refine IsLocalizedModule.ext (.powers localizer) (Algebra.linearMap _ _)
      (IsLocalizedModule.map_units (S := .powers localizer) res) ?_
    rw [IsLocalizedModule.map_comp]
    ext
    simp [ψ, res]
  have hb : Function.Bijective ψ := by
    rw [hψ]
    exact ⟨IsLocalizedModule.map_injective _ _ _ _ he.1,
      IsLocalizedModule.map_surjective _ _ _ _ he.2⟩
  exact hb

/-- If `f` is a free generator of `M` on `U` and `e` is a section over `U` such that `r ↦ r • e`
is a bijection `Γ(X, U) ≃ Γ(M, U)`, then `e` is a unit multiple of `f`, hence a free
generator. -/
lemma IsFreeGenerator.of_bijective_smul {moduleSheaf : scheme.Modules} {openSubset : scheme.Opens} {generator localizationMap : Γ(moduleSheaf, openSubset)}
    (hf : IsFreeGenerator localizationMap) (he : Function.Bijective fun scalar : Γ(scheme, openSubset) ↦ scalar • generator) :
    IsFreeGenerator generator := by
  obtain ⟨coefficient, rfl⟩ := hf.exists_smul_eq generator
  obtain ⟨inverseCoefficient, hb⟩ := he.2 localizationMap
  dsimp only at hb
  have hba : inverseCoefficient * coefficient = 1 := hf.smul_left_injective (by simp only [mul_smul, one_smul, hb])
  exact hf.units_smul ⟨coefficient, inverseCoefficient, by rw [mul_comm, hba], hba⟩

/-- **A free generator from a basis of the sections over an affine open.** Let `M` be an
invertible `𝒪_X`-module and `e` a section of `M` over an affine open `U` such that `r ↦ r • e`
is a bijection `Γ(X, U) ≃ Γ(M, U)`. Then `e` is a free generator of `M` on `U`: on every basic
open `D(g) ⊆ U` the sections of `𝒪_X` and of `M` are the localizations at `g`. -/
theorem isFreeGenerator_of_bijective_smul (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible] {openSubset : scheme.Opens}
    (hU : IsAffineOpen openSubset) {generator : Γ(moduleSheaf, openSubset)} (he : Function.Bijective fun scalar : Γ(scheme, openSubset) ↦ scalar • generator) :
    IsFreeGenerator generator := by
  let denominators : Sieve openSubset :=
    { arrows smallerOpen _ := ∃ localizer : Γ(scheme, openSubset), smallerOpen ≤ scheme.basicOpen localizer ∧
        ∃ generatorOpen : scheme.Opens, scheme.basicOpen localizer ≤ generatorOpen ∧ ∃ localizationMap : Γ(moduleSheaf, generatorOpen), IsFreeGenerator localizationMap
      downward_closed := by
        rintro smallerOpen V' inclusion ⟨localizer, hg, h⟩ furtherInclusion
        exact ⟨localizer, (leOfHom furtherInclusion).trans hg, h⟩ }
  refine isFreeGenerator_of_mem generator (coveringSieve := denominators) ?_ ?_
  · intro point hx
    obtain ⟨generatorOpen, hxW, hWU, localizationMap, hf⟩ := exists_isFreeGenerator moduleSheaf hx
    obtain ⟨localizer, hgW, hxg⟩ := hU.exists_basicOpen_le ⟨point, hxW⟩ hx
    exact ⟨_, homOfLE (scheme.basicOpen_le localizer), ⟨localizer, le_rfl, generatorOpen.1, hgW, localizationMap, hf⟩, hxg⟩
  · rintro smallerOpen inclusion ⟨localizer, hVg, generatorOpen, hgW, localizationMap, hf⟩
    have hg := (hf.map hgW).of_bijective_smul (bijective_smul_map_basicOpen moduleSheaf hU he localizer)
    have := hg.map hVg
    rwa [presheaf_map_map_apply] at this

/-- **Triviality near a UFD localization.** Let `M` be an invertible `𝒪_X`-module, `U` an affine
open and `S` a submonoid of `Γ(X, U)` whose localization is a unique factorization domain. Then
`M` is trivial on a basic open `D(s) ⊆ U` for some `s ∈ S`. -/
theorem exists_mem_isFreeGenerator_basicOpen (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible] {openSubset : scheme.Opens}
    (hU : IsAffineOpen openSubset) (denominators : Submonoid Γ(scheme, openSubset)) [IsDomain (Localization denominators)]
    [UniqueFactorizationMonoid (Localization denominators)] :
    ∃ localizers ∈ denominators, ∃ generator : Γ(moduleSheaf, scheme.basicOpen localizers), IsFreeGenerator generator := by
  have := invertible_sections_of_isAffineOpen moduleSheaf hU
  obtain ⟨localizers, hs, sectionValue, localizedBasis⟩ := Module.Invertible.exists_mem_bijective_smul (moduleType := Γ(moduleSheaf, openSubset)) denominators
  let : Module Γ(scheme, openSubset) Γ(moduleSheaf, scheme.basicOpen localizers) :=
    Module.compHom _ (algebraMap Γ(scheme, openSubset) Γ(scheme, scheme.basicOpen localizers))
  have := isLocalizedModule_basicOpen moduleSheaf hU localizers
  have := hU.isLocalization_basicOpen localizers
  have : IsScalarTower Γ(scheme, openSubset) Γ(scheme, scheme.basicOpen localizers) Γ(moduleSheaf, scheme.basicOpen localizers) :=
    ⟨fun coefficient inverseCoefficient sectionValue ↦ mul_smul _ _ _⟩
  exact ⟨localizers, hs, _, isFreeGenerator_of_bijective_smul moduleSheaf (hU.basicOpen localizers)
    (localizedBasis Γ(scheme, scheme.basicOpen localizers) Γ(moduleSheaf, scheme.basicOpen localizers)
      { toFun := moduleSheaf.presheaf.map (homOfLE (scheme.basicOpen_le localizers)).op
        map_add' := map_add _
        map_smul' := map_smul moduleSheaf _ })⟩

end AlgebraicGeometry.Scheme.Modules
