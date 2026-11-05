import Jacobian.AlgebraicGeometry.Modules.FaithfullyFlatDescent

/-!
# Morphisms between quasi-coherent modules on affine schemes

Global sections determine morphisms out of a quasi-coherent module on an affine
scheme. Linear maps between the sections of quasi-coherent modules lift to
morphisms of sheaves, independently of a chosen presentation of the affine scheme.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem isQuasicoherent_pushforward_of_isIso
    {source target : Scheme.{schemeUniverse}} (morphism : source ⟶ target)
    [IsIso morphism] (moduleSheaf : source.Modules) [moduleSheaf.IsQuasicoherent] :
    ((pushforward morphism).obj moduleSheaf).IsQuasicoherent := by
  let directImage := (pushforward morphism).obj moduleSheaf
  let comparison : directImage ≅ moduleSheaf.restrict (inv morphism) :=
    (restrictFunctorId.app directImage).symm ≪≫
      (restrictFunctorCongr (IsIso.inv_hom_id morphism)).symm.app directImage ≪≫
      (restrictFunctorComp (inv morphism) morphism).app directImage ≪≫
      (restrictFunctor (inv morphism)).mapIso
        ((restrictFunctorAdjCounitIso morphism).app moduleSheaf)
  exact (SheafOfModules.isQuasicoherent target.ringCatSheaf).prop_of_iso
    comparison.symm inferInstance

/-- On an affine scheme, global sections detect morphisms out of a quasi-coherent module. -/
theorem hom_ext_of_isQuasicoherent_of_isAffine
    {scheme : Scheme.{schemeUniverse}} [IsAffine scheme]
    {sourceModule targetModule : scheme.Modules} [sourceModule.IsQuasicoherent]
    {firstMap secondMap : sourceModule ⟶ targetModule}
    (sectionsEqual : ∀ sectionValue : Γ(sourceModule, ⊤),
      firstMap.app ⊤ sectionValue = secondMap.app ⊤ sectionValue) :
    firstMap = secondMap := by
  letI := isQuasicoherent_pushforward_of_isIso scheme.toSpecΓ sourceModule
  apply (pushforward scheme.toSpecΓ).map_injective
  apply hom_ext_of_isQuasicoherent_Spec
  exact sectionsEqual

/-- A linear map of sections of quasi-coherent modules on an affine scheme comes from a
morphism of sheaves. -/
theorem exists_hom_app_top_eq_of_isAffine
    {scheme : Scheme.{schemeUniverse}} [IsAffine scheme]
    {sourceModule targetModule : scheme.Modules}
    [sourceModule.IsQuasicoherent] [targetModule.IsQuasicoherent]
    (sectionsMap : Γ(sourceModule, ⊤) →ₗ[Γ(scheme, ⊤)] Γ(targetModule, ⊤)) :
    ∃ coefficientMap : sourceModule ⟶ targetModule,
      ∀ sectionValue : Γ(sourceModule, ⊤),
        coefficientMap.app ⊤ sectionValue = sectionsMap sectionValue := by
  letI := isQuasicoherent_pushforward_of_isIso scheme.toSpecΓ sourceModule
  letI := isQuasicoherent_pushforward_of_isIso scheme.toSpecΓ targetModule
  obtain ⟨spectrumMap, spectrumMapSections⟩ :=
    exists_hom_app_top_eq'
      (M := (pushforward scheme.toSpecΓ).obj sourceModule)
      (N := (pushforward scheme.toSpecΓ).obj targetModule)
      sectionsMap.toAddMonoidHom (fun scalar sectionValue ↦ by
        have scalarAction (moduleSheaf : scheme.Modules)
            (moduleElement : Γ((pushforward scheme.toSpecΓ).obj moduleSheaf, ⊤)) :
            ((ΓSpecIso Γ(scheme, ⊤)).inv ≫
              (Spec Γ(scheme, ⊤)).presheaf.map
                (homOfLE (le_top : (⊤ : (Spec Γ(scheme, ⊤)).Opens) ≤ ⊤)).op).hom
              scalar • moduleElement =
                (scalar • (show Γ(moduleSheaf, ⊤) from moduleElement) :
                  Γ(moduleSheaf, ⊤)) := by
          change scheme.toSpecΓ.appTop ((ΓSpecIso Γ(scheme, ⊤)).inv scalar) •
            (show Γ(moduleSheaf, ⊤) from moduleElement) = _
          have scalarIdentity :
              scheme.toSpecΓ.appTop ((ΓSpecIso Γ(scheme, ⊤)).inv scalar) = scalar := by
            rw [← CommRingCat.comp_apply, toSpecΓ_appTop, Iso.inv_hom_id]
            rfl
          rw [scalarIdentity]
        exact (congrArg sectionsMap (scalarAction sourceModule sectionValue)).trans
          ((sectionsMap.map_smul scalar sectionValue).trans
            (scalarAction targetModule (sectionsMap sectionValue)).symm))
  refine ⟨(pushforward scheme.toSpecΓ).preimage spectrumMap, fun sectionValue ↦ ?_⟩
  have evaluation := congr(Hom.app
    $((pushforward scheme.toSpecΓ).map_preimage spectrumMap) ⊤ sectionValue)
  exact evaluation.trans (spectrumMapSections sectionValue)

end AlgebraicGeometry.Scheme.Modules
