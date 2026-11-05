import Jacobian.AlgebraicGeometry.Modules.FinitePresentation
import Jacobian.AlgebraicGeometry.Modules.PullbackTilde

/-!
# Realizing finitely presented modules on affine schemes

A finitely presented module of global sections on an affine scheme determines
a finitely presented module sheaf. If its scalar extension agrees with the
sections of a quasi-coherent sheaf on another affine scheme, the corresponding
pullback sheaves are isomorphic.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite presentation of sections realizes an actual affine pullback model. -/
theorem exists_finitePresentation_model_of_sections
    {source target : Scheme.{schemeUniverse}} [IsAffine source] [IsAffine target]
    (morphism : source ⟶ target) (moduleSheaf : source.Modules)
    [moduleSheaf.IsQuasicoherent] (stageModule : ModuleCat.{schemeUniverse} Γ(target, ⊤))
    [Module.FinitePresentation Γ(target, ⊤) stageModule]
    (sectionsComparison : Nonempty
      ((ModuleCat.extendScalars morphism.appTop.hom).obj stageModule ≅
        ModuleCat.of Γ(source, ⊤) Γ(moduleSheaf, ⊤))) :
    ∃ stageSheaf : target.Modules, stageSheaf.IsFinitePresentation ∧
      stageSheaf.IsQuasicoherent ∧
      Nonempty ((pullback morphism).obj stageSheaf ≅ moduleSheaf) := by
  let targetTilde := tilde.functor Γ(target, ⊤)
  let sourceTilde := tilde.functor Γ(source, ⊤)
  let targetRestriction := restrictFunctor target.isoSpec.hom
  let sourceRestriction := restrictFunctor source.isoSpec.hom
  let toSpectrum := restrictFunctor source.isoSpec.inv
  let stageSheaf := targetRestriction.obj (targetTilde.obj stageModule)
  obtain ⟨generators, spanGenerators, relations, spanRelations⟩ :=
    (inferInstance : Module.FinitePresentation Γ(target, ⊤) stageModule).out
  let presentation := presentationTilde stageModule (generators : Set stageModule)
    spanGenerators (relations : Set _) spanRelations
  letI : presentation.IsFinite :=
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (generators : Set stageModule))⟩
      isFiniteType_relations :=
        ⟨inferInstanceAs (Finite (relations : Set (generators →₀ Γ(target, ⊤))))⟩ }
  letI : (targetTilde.obj stageModule).IsFinitePresentation :=
    presentation.isFinitePresentation
  have finiteStageSheaf : stageSheaf.IsFinitePresentation := by
    change ((restrictFunctor target.isoSpec.hom).obj
      (targetTilde.obj stageModule)).IsFinitePresentation
    exact (SheafOfModules.isFinitePresentation target.ringCatSheaf).prop_of_iso
      ((restrictFunctorIsoPullback target.isoSpec.hom).app
        (targetTilde.obj stageModule)).symm inferInstance
  refine ⟨stageSheaf, finiteStageSheaf, inferInstance, ?_⟩
  let comparison : targetRestriction ⋙ pullback morphism ≅
      pullback (Spec.map morphism.appTop) ⋙ sourceRestriction :=
    Functor.isoWhiskerRight (restrictFunctorIsoPullback target.isoSpec.hom)
      (pullback morphism) ≪≫
      pullbackComp morphism target.isoSpec.hom ≪≫
      pullbackCongr (Scheme.isoSpec_hom_naturality morphism).symm ≪≫
      (pullbackComp source.isoSpec.hom (Spec.map morphism.appTop)).symm ≪≫
      Functor.isoWhiskerLeft (pullback (Spec.map morphism.appTop))
        (restrictFunctorIsoPullback source.isoSpec.hom).symm
  let baseComparison : (pullback morphism).obj stageSheaf ≅
      sourceRestriction.obj
        (sourceTilde.obj ((ModuleCat.extendScalars morphism.appTop.hom).obj stageModule)) :=
    comparison.app (targetTilde.obj stageModule) ≪≫
      sourceRestriction.mapIso ((tildePullbackIso morphism.appTop).app stageModule)
  letI : (toSpectrum.obj moduleSheaf).IsQuasicoherent := by
    dsimp [toSpectrum]
    infer_instance
  letI : IsIso (fromTildeΓ (toSpectrum.obj moduleSheaf)) :=
    isIso_fromTildeΓ_of_isQuasicoherent _
  let spectrumSections : moduleSpecΓFunctor.obj (toSpectrum.obj moduleSheaf) ≅
      ModuleCat.of Γ(source, ⊤) Γ(moduleSheaf, ⊤) := by
    apply LinearEquiv.toModuleIso
    change moduleSpecΓFunctor.obj (moduleSheaf.restrict source.isoSpec.inv) ≃ₗ[Γ(source, ⊤)]
      Γ(moduleSheaf, ⊤)
    let restrictionComparison := moduleSpecΓFunctor.mapIso
      ((restrictFunctorCongr (IsAffineOpen.fromSpec_top (X := source))).app moduleSheaf)
    exact restrictionComparison.toLinearEquiv.symm ≪≫ₗ
      sectionsRestrictFromSpecLinearEquiv moduleSheaf (isAffineOpen_top source)
  let cancel : toSpectrum ⋙ sourceRestriction ≅ 𝟭 source.Modules :=
    (restrictFunctorComp source.isoSpec.hom source.isoSpec.inv).symm ≪≫
      restrictFunctorCongr source.isoSpec.hom_inv_id ≪≫ restrictFunctorId
  obtain ⟨sectionsComparison⟩ := sectionsComparison
  exact ⟨baseComparison ≪≫ sourceRestriction.mapIso
    (sourceTilde.mapIso (sectionsComparison ≪≫ spectrumSections.symm)) ≪≫
      sourceRestriction.mapIso (asIso (fromTildeΓ (toSpectrum.obj moduleSheaf))) ≪≫
        cancel.app moduleSheaf⟩

end AlgebraicGeometry.Scheme.Modules
