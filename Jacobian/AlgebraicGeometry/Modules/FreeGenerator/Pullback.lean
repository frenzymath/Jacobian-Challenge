import Jacobian.AlgebraicGeometry.Modules.FreeGenerator
import Jacobian.AlgebraicGeometry.Modules.HomSection
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Canonical pullback of a free generator

The adjunction unit sends a free generator to a free generator. Restriction to an open
subscheme reduces the assertion to pulling back a trivialization by a global section.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {sourceScheme targetScheme : Scheme.{schemeUniverse}}

private lemma isIso_homOfGlobalSection {moduleSheaf : targetScheme.Modules}
    {generator : Γ(moduleSheaf, ⊤)} (freeGenerator : IsFreeGenerator generator) :
    IsIso (homOfGlobalSection moduleSheaf generator) := by
  rw [Hom.isIso_iff_isIso_app]
  intro openSubset
  rw [ConcreteCategory.isIso_iff_bijective]
  have sectionEquation : (fun scalar : Γ(targetScheme, openSubset) ↦
      (homOfGlobalSection moduleSheaf generator).app openSubset scalar) =
      fun scalar : Γ(targetScheme, openSubset) ↦ scalar •
        moduleSheaf.presheaf.map (homOfLE le_top).op generator :=
    funext (homOfGlobalSection_app moduleSheaf generator openSubset)
  have bijective := freeGenerator openSubset le_top
  rw [← sectionEquation] at bijective
  exact bijective

private lemma IsFreeGenerator.pullbackSection_top (morphism : sourceScheme ⟶ targetScheme)
    {moduleSheaf : targetScheme.Modules} {generator : Γ(moduleSheaf, ⊤)}
    (freeGenerator : IsFreeGenerator generator) :
    IsFreeGenerator (pullbackSection morphism generator) := by
  have := isIso_homOfGlobalSection freeGenerator
  let trivialization : Modules.unit sourceScheme ≅ (pullback morphism).obj moduleSheaf :=
    (pullbackObjUnitIso morphism).symm ≪≫
      (pullback morphism).mapIso (asIso (homOfGlobalSection moduleSheaf generator))
  have sectionEquation : pullbackSection morphism generator =
      trivialization.hom.app (morphism ⁻¹ᵁ ⊤) (1 : Γ(sourceScheme, morphism ⁻¹ᵁ ⊤)) := by
    simpa only [trivialization, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      asIso_hom, homOfGlobalSection_app_one, presheaf_map_id_apply] using
      (pullbackSection_app_one morphism (homOfGlobalSection moduleSheaf generator))
  rw [sectionEquation]
  exact (isFreeGenerator_one (morphism ⁻¹ᵁ ⊤)).app_hom trivialization

/-- A section of the restriction of `M` along an open immersion `f` over `U` is a free generator
if and only if it is one as a section of `M` over `f ''ᵁ U`. -/
private lemma isFreeGenerator_restrict_iff (openImmersion : sourceScheme ⟶ targetScheme) [IsOpenImmersion openImmersion] (moduleSheaf : targetScheme.Modules)
    {openSubset : sourceScheme.Opens} (sectionValue : Γ(moduleSheaf, openImmersion ''ᵁ openSubset)) :
    IsFreeGenerator (M := moduleSheaf.restrict openImmersion) (U := openSubset) sectionValue ↔ IsFreeGenerator (M := moduleSheaf) (U := openImmersion ''ᵁ openSubset) sectionValue := by
  have key (smallerOpen : sourceScheme.Opens) (inclusion : smallerOpen ≤ openSubset) :
      (fun scalar : Γ(sourceScheme, smallerOpen) ↦ scalar • (moduleSheaf.restrict openImmersion).presheaf.map (homOfLE inclusion).op sectionValue) =
        (fun scalar : Γ(targetScheme, openImmersion ''ᵁ smallerOpen) ↦ scalar • moduleSheaf.presheaf.map (homOfLE (openImmersion.image_mono inclusion)).op sectionValue) ∘
          (openImmersion.appIso smallerOpen).inv :=
    rfl
  refine ⟨fun hx smallerOpen hW ↦ ?_, fun hx smallerOpen hW ↦ ?_⟩
  · obtain ⟨smallerOpen, rfl⟩ : ∃ W', openImmersion ''ᵁ W' = smallerOpen :=
      ⟨openImmersion ⁻¹ᵁ smallerOpen, by rw [openImmersion.image_preimage_eq_opensRange_inf, inf_eq_right.mpr
        (hW.trans (openImmersion.image_le_opensRange openSubset))]⟩
    have hW' : smallerOpen ≤ openSubset := (openImmersion.image_le_image_iff smallerOpen openSubset).mp hW
    have := (hx smallerOpen hW').comp (ConcreteCategory.bijective_of_isIso (openImmersion.appIso smallerOpen).hom)
    rw [key smallerOpen hW', Function.comp_assoc] at this
    have generator : (fun scalar : Γ(targetScheme, openImmersion ''ᵁ smallerOpen) ↦ scalar • moduleSheaf.presheaf.map (homOfLE (openImmersion.image_mono hW')).op sectionValue) ∘
        (openImmersion.appIso smallerOpen).inv ∘ (openImmersion.appIso smallerOpen).hom =
          fun scalar : Γ(targetScheme, openImmersion ''ᵁ smallerOpen) ↦ scalar • moduleSheaf.presheaf.map (homOfLE hW).op sectionValue := by
      funext scalar
      simp
    rw [generator] at this
    exact this
  · rw [key smallerOpen hW]
    exact (hx _ (openImmersion.image_mono hW)).comp (ConcreteCategory.bijective_of_isIso (openImmersion.appIso smallerOpen).inv)

/-- A section whose restriction to an open with the same underlying set is a free generator is
a free generator. -/
private lemma IsFreeGenerator.of_presheaf_map {moduleSheaf : sourceScheme.Modules} {openSubset targetOpen : sourceScheme.Opens} (inclusion : targetOpen ≤ openSubset) (h' : openSubset ≤ targetOpen)
    {generator : Γ(moduleSheaf, openSubset)} (he : IsFreeGenerator (moduleSheaf.presheaf.map (homOfLE inclusion).op generator)) :
    IsFreeGenerator generator := by
  intro smallerOpen hW
  have := he smallerOpen (hW.trans h')
  simp only [presheaf_map_map_apply] at this
  exact this

/-- **The unit of the adjunction `g^* ⊣ g_*` maps free generators to free generators.** If `e` is
a free generator of `N` on `V`, then `η e` is a free generator of `g^* N` on `g ⁻¹ᵁ V`.

We compare the two left adjoints `(g^* -)|_{g ⁻¹ᵁ V}` and `(g ∣_ V)^* (- |_V)` of the isomorphic
functors `g_* ∘ (g ⁻¹ᵁ V).ι_*` and `V.ι_* ∘ (g ∣_ V)_*`; the isomorphism between them is
compatible with the units. On `V`, `e` is a global free generator of `N|_V`, which is mapped to
a free generator by the unit of `(g ∣_ V)^* ⊣ (g ∣_ V)_*`. -/
lemma IsFreeGenerator.pullbackSection (morphism : sourceScheme ⟶ targetScheme) {moduleSheaf : targetScheme.Modules} {targetOpen : targetScheme.Opens} {generator : Γ(moduleSheaf, targetOpen)}
    (he : IsFreeGenerator generator) :
    IsFreeGenerator (M := (pullback morphism).obj moduleSheaf) (U := morphism ⁻¹ᵁ targetOpen)
      (pullbackSection morphism generator) := by
  change IsFreeGenerator (M := (pullback morphism).obj moduleSheaf)
    (U := morphism ⁻¹ᵁ targetOpen)
    (((pullbackPushforwardAdjunction morphism).unit.app moduleSheaf).app
      targetOpen generator)
  let A1 := (pullbackPushforwardAdjunction morphism).comp (restrictAdjunction (morphism ⁻¹ᵁ targetOpen).ι)
  let A2 := (restrictAdjunction targetOpen.ι).comp (pullbackPushforwardAdjunction (morphism ∣_ targetOpen))
  let ρ : pushforward (morphism ⁻¹ᵁ targetOpen).ι ⋙ pushforward morphism ≅ pushforward (morphism ∣_ targetOpen) ⋙ pushforward targetOpen.ι :=
    pushforwardComp _ _ ≪≫ pushforwardCongr (morphismRestrict_ι morphism targetOpen).symm ≪≫
      (pushforwardComp _ _).symm
  have hu := unit_conjugateEquiv_symm A1 A2 ρ.hom moduleSheaf
  have hiso : IsIso ((conjugateEquiv A1 A2).symm ρ.hom) := inferInstance
  generalize (conjugateEquiv A1 A2).symm ρ.hom = Φ at hu hiso
  have inclusion := congrArg (fun φ ↦ Hom.app φ targetOpen generator) hu
  simp only [A1, A2, Adjunction.comp_unit_app, Hom.comp_app, ConcreteCategory.comp_apply, ρ,
    Iso.trans_hom, NatTrans.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app,
    Iso.symm_hom, pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app, Functor.comp_map] at inclusion
  let e₁ : Γ(moduleSheaf.restrict targetOpen.ι, targetOpen.ι ⁻¹ᵁ targetOpen) :=
    moduleSheaf.presheaf.map (homOfLE (targetOpen.ι.image_preimage_le targetOpen)).op generator
  have he₁ : IsFreeGenerator (M := moduleSheaf.restrict targetOpen.ι) e₁ :=
    (isFreeGenerator_restrict_iff _ _ _).2 (he.map _)
  have htop : (⊤ : targetOpen.toScheme.Opens) ≤ targetOpen.ι ⁻¹ᵁ targetOpen := targetOpen.ι_preimage_self.ge
  have h₂ := (he₁.map htop).pullbackSection_top (morphism ∣_ targetOpen)
  dsimp only [AlgebraicGeometry.Scheme.Modules.pullbackSection,
    AlgebraicGeometry.Scheme.Modules.pullbackUnit] at h₂
  erw [Hom.app_presheaf_map ((pullbackPushforwardAdjunction (morphism ∣_ targetOpen)).unit.app (moduleSheaf.restrict targetOpen.ι))
    (homOfLE htop) e₁] at h₂
  have h₃ := IsFreeGenerator.of_presheaf_map (moduleSheaf := (pullback (morphism ∣_ targetOpen)).obj (moduleSheaf.restrict targetOpen.ι))
    (generator := ((pullbackPushforwardAdjunction (morphism ∣_ targetOpen)).unit.app (moduleSheaf.restrict targetOpen.ι)).app _ e₁)
    (Scheme.Hom.preimage_mono _ htop) (by simp [targetOpen.ι_preimage_self]) h₂
  have h₄ := h₃.app_hom (asIso (Φ.app moduleSheaf))
  rw [asIso_hom] at h₄
  erw [← inclusion] at h₄
  have t₁ : (morphism ⁻¹ᵁ targetOpen).ι ⁻¹ᵁ morphism ⁻¹ᵁ targetOpen = ⊤ := Scheme.Opens.ι_preimage_self _
  have t₂ : (morphism ∣_ targetOpen) ⁻¹ᵁ targetOpen.ι ⁻¹ᵁ targetOpen = ⊤ := by
    rw [Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
  have h₅ := IsFreeGenerator.of_presheaf_map (moduleSheaf := ((pullback morphism).obj moduleSheaf).restrict (morphism ⁻¹ᵁ targetOpen).ι)
    (openSubset := (morphism ⁻¹ᵁ targetOpen).ι ⁻¹ᵁ morphism ⁻¹ᵁ targetOpen)
    (targetOpen := (morphism ∣_ targetOpen) ⁻¹ᵁ targetOpen.ι ⁻¹ᵁ targetOpen)
    (generator := ((pullback morphism).obj moduleSheaf).presheaf.map (homOfLE ((morphism ⁻¹ᵁ targetOpen).ι.image_preimage_le _)).op
      (((pullbackPushforwardAdjunction morphism).unit.app moduleSheaf).app targetOpen generator))
    (t₂.le.trans t₁.ge) (t₁.le.trans t₂.ge) h₄
  rw [isFreeGenerator_restrict_iff] at h₅
  refine IsFreeGenerator.of_presheaf_map _ ?_ h₅
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_idem]
end AlgebraicGeometry.Scheme.Modules
