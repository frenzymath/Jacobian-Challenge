import Jacobian.Algebra.Category.ModuleCat.FinitePresentation.Cocone
import Jacobian.AlgebraicGeometry.Modules.AffineHom
import Jacobian.AlgebraicGeometry.Modules.AffineSections
import Jacobian.AlgebraicGeometry.Modules.Limits.Charts

/-!
# Morphisms of coefficients on affine inverse limits

Morphisms out of finitely presented coefficients descend along directed affine
inverse limits. Equality of morphisms is eventually detected at a stage. The
recovery equation uses the native pullback composition isomorphism, so these
results apply to overlap maps and their cocycle equations.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits Opposite TensorProduct
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

private theorem exists_pullback_sections_iso
    {source target : Scheme.{schemeUniverse}} [IsAffine source] [IsAffine target]
    (morphism : source ⟶ target) (moduleSheaf : target.Modules)
    [moduleSheaf.IsQuasicoherent] :
    ∃ comparison :
      (ModuleCat.extendScalars morphism.appTop.hom).obj
          ((SheafOfModules.evaluation target.ringCatSheaf (op ⊤)).obj moduleSheaf) ≅
        (SheafOfModules.evaluation source.ringCatSheaf (op ⊤)).obj
          ((pullback morphism).obj moduleSheaf),
      ∀ sectionValue : Γ(moduleSheaf, ⊤),
        comparison.hom ((1 : Γ(source, ⊤)) ⊗ₜ[Γ(target, ⊤), morphism.appTop.hom]
          sectionValue) = pullbackΓ morphism moduleSheaf sectionValue := by
  letI : Algebra Γ(target, ⊤) Γ(source, ⊤) := morphism.appTop.hom.toAlgebra
  have topMap : morphism.appLE ⊤ ⊤ le_top = morphism.appTop :=
    Scheme.Hom.appLE_eq_app morphism (U := ⊤)
  have ordinaryResult :=
    exists_linearEquiv_pullback_sections morphism moduleSheaf
      (isAffineOpen_top target) (isAffineOpen_top source) le_top
  rw [topMap] at ordinaryResult
  obtain ⟨ordinaryComparison, ordinaryNormalization⟩ := ordinaryResult
  let nativeComparison := ModuleCat.tensorEquivExtendScalars Γ(target, ⊤) Γ(source, ⊤)
    ((SheafOfModules.evaluation target.ringCatSheaf (op ⊤)).obj moduleSheaf)
  refine ⟨(nativeComparison.symm ≪≫ₗ ordinaryComparison).toModuleIso, fun sectionValue ↦ ?_⟩
  change ordinaryComparison (nativeComparison.symm _) = _
  have unitTensor : nativeComparison ((1 : Γ(source, ⊤)) ⊗ₜ[Γ(target, ⊤)] sectionValue) =
      (1 : Γ(source, ⊤)) ⊗ₜ[Γ(target, ⊤), morphism.appTop.hom] sectionValue := rfl
  rw [← unitTensor, nativeComparison.symm_apply_apply, ordinaryNormalization, pullbackΓ_eq]
  exact congrArg (fun restrictionMap :
      op (morphism ⁻¹ᵁ (⊤ : target.Opens)) ⟶ op (⊤ : source.Opens) ↦
    ((pullback morphism).obj moduleSheaf).presheaf.map restrictionMap
      (pullbackSection morphism sectionValue)) (Subsingleton.elim _ _)

private lemma pullback_sections_iso_naturality
    {source target : Scheme.{schemeUniverse}} (morphism : source ⟶ target)
    {sourceModule targetModule : target.Modules} (coefficientMap : sourceModule ⟶ targetModule)
    (sourceComparison : (ModuleCat.extendScalars morphism.appTop.hom).obj
        ((SheafOfModules.evaluation target.ringCatSheaf (op ⊤)).obj sourceModule) ≅
      (SheafOfModules.evaluation source.ringCatSheaf (op ⊤)).obj
        ((pullback morphism).obj sourceModule))
    (targetComparison : (ModuleCat.extendScalars morphism.appTop.hom).obj
        ((SheafOfModules.evaluation target.ringCatSheaf (op ⊤)).obj targetModule) ≅
      (SheafOfModules.evaluation source.ringCatSheaf (op ⊤)).obj
        ((pullback morphism).obj targetModule))
    (sourceNormalization : ∀ sectionValue : Γ(sourceModule, ⊤),
      sourceComparison.hom ((1 : Γ(source, ⊤)) ⊗ₜ[Γ(target, ⊤), morphism.appTop.hom]
        sectionValue) = pullbackΓ morphism sourceModule sectionValue)
    (targetNormalization : ∀ sectionValue : Γ(targetModule, ⊤),
      targetComparison.hom ((1 : Γ(source, ⊤)) ⊗ₜ[Γ(target, ⊤), morphism.appTop.hom]
        sectionValue) = pullbackΓ morphism targetModule sectionValue) :
    (ModuleCat.extendScalars morphism.appTop.hom).map
        ((SheafOfModules.evaluation target.ringCatSheaf (op ⊤)).map coefficientMap) ≫
          targetComparison.hom = sourceComparison.hom ≫
        (SheafOfModules.evaluation source.ringCatSheaf (op ⊤)).map
          ((pullback morphism).map coefficientMap) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro sectionValue
  change targetComparison.hom
      ((ModuleCat.extendScalars morphism.appTop.hom).map _ _) =
    ((pullback morphism).map coefficientMap).app ⊤ (sourceComparison.hom _)
  rw [ModuleCat.ExtendScalars.map_tmul, sourceNormalization, targetNormalization]
  simp only [pullbackΓ_apply]
  exact (pullbackUnit_naturality_apply morphism coefficientMap ⊤ sectionValue).symm

private lemma pullback_sections_iso_comp
    {source middle target : Scheme.{schemeUniverse}}
    (firstMap : middle ⟶ target) (secondMap : source ⟶ middle)
    (composite : source ⟶ target) (factorization : secondMap ≫ firstMap = composite)
    (moduleSheaf : target.Modules)
    (initialComparison : (ModuleCat.extendScalars composite.appTop.hom).obj
        ((SheafOfModules.evaluation target.ringCatSheaf (op ⊤)).obj moduleSheaf) ≅
      (SheafOfModules.evaluation source.ringCatSheaf (op ⊤)).obj
        ((pullback composite).obj moduleSheaf))
    (stageComparison : (ModuleCat.extendScalars firstMap.appTop.hom).obj
        ((SheafOfModules.evaluation target.ringCatSheaf (op ⊤)).obj moduleSheaf) ≅
      (SheafOfModules.evaluation middle.ringCatSheaf (op ⊤)).obj
        ((pullback firstMap).obj moduleSheaf))
    (furtherComparison : (ModuleCat.extendScalars secondMap.appTop.hom).obj
        ((SheafOfModules.evaluation middle.ringCatSheaf (op ⊤)).obj
          ((pullback firstMap).obj moduleSheaf)) ≅
      (SheafOfModules.evaluation source.ringCatSheaf (op ⊤)).obj
        ((pullback secondMap).obj ((pullback firstMap).obj moduleSheaf)))
    (tensorComparison : (ModuleCat.extendScalars composite.appTop.hom).obj
        ((SheafOfModules.evaluation target.ringCatSheaf (op ⊤)).obj moduleSheaf) ≅
      (ModuleCat.extendScalars secondMap.appTop.hom).obj
        ((ModuleCat.extendScalars firstMap.appTop.hom).obj
          ((SheafOfModules.evaluation target.ringCatSheaf (op ⊤)).obj moduleSheaf)))
    (initialNormalization : ∀ sectionValue : Γ(moduleSheaf, ⊤),
      initialComparison.hom ((1 : Γ(source, ⊤)) ⊗ₜ[Γ(target, ⊤), composite.appTop.hom]
        sectionValue) = pullbackΓ composite moduleSheaf sectionValue)
    (stageNormalization : ∀ sectionValue : Γ(moduleSheaf, ⊤),
      stageComparison.hom ((1 : Γ(middle, ⊤)) ⊗ₜ[Γ(target, ⊤), firstMap.appTop.hom]
        sectionValue) = pullbackΓ firstMap moduleSheaf sectionValue)
    (furtherNormalization : ∀ sectionValue : Γ((pullback firstMap).obj moduleSheaf, ⊤),
      furtherComparison.hom ((1 : Γ(source, ⊤)) ⊗ₜ[Γ(middle, ⊤), secondMap.appTop.hom]
        sectionValue) = pullbackΓ secondMap ((pullback firstMap).obj moduleSheaf) sectionValue)
    (tensorNormalization : ∀ sectionValue : Γ(moduleSheaf, ⊤),
      tensorComparison.hom ((1 : Γ(source, ⊤)) ⊗ₜ[Γ(target, ⊤), composite.appTop.hom]
        sectionValue) = (1 : Γ(source, ⊤)) ⊗ₜ[Γ(middle, ⊤), secondMap.appTop.hom]
          ((1 : Γ(middle, ⊤)) ⊗ₜ[Γ(target, ⊤), firstMap.appTop.hom] sectionValue)) :
    tensorComparison.hom ≫ (ModuleCat.extendScalars secondMap.appTop.hom).map
        stageComparison.hom ≫ furtherComparison.hom ≫
          (SheafOfModules.evaluation source.ringCatSheaf (op ⊤)).map
            (pullbackCompOfEq secondMap firstMap composite factorization moduleSheaf).hom =
      initialComparison.hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro sectionValue
  change (pullbackCompOfEq secondMap firstMap composite factorization moduleSheaf).hom.app ⊤
    (furtherComparison.hom
      ((ModuleCat.extendScalars secondMap.appTop.hom).map stageComparison.hom
        (tensorComparison.hom _))) = initialComparison.hom _
  rw [tensorNormalization, ModuleCat.ExtendScalars.map_tmul, stageNormalization,
    furtherNormalization, initialNormalization]
  simp only [pullbackΓ_apply]
  rw [← modulesPseudofunctor_mapComp'_inv_app_eq]
  exact modulesPseudofunctor_mapComp'_inv_app_top firstMap secondMap composite
    factorization moduleSheaf sectionValue

/-- A morphism between pullbacks of fixed coefficients on an affine inverse limit descends to
a stage when the source is finitely presented. Recovery uses native pullback composition. -/
theorem exists_hom_of_affine_limit
    {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] (diagram : Indexᵒᵖ ⥤ Scheme.{schemeUniverse})
    [∀ stageIndex, IsAffine (diagram.obj stageIndex)]
    (cone : Cone diagram) (limit : IsLimit cone) [IsAffine cone.pt]
    (initialIndex : Index) (sourceModule targetModule : (diagram.obj (op initialIndex)).Modules)
    [sourceModule.IsFinitePresentation] [sourceModule.IsQuasicoherent]
    [targetModule.IsQuasicoherent]
    (coefficientMap : (pullback (cone.π.app (op initialIndex))).obj sourceModule ⟶
      (pullback (cone.π.app (op initialIndex))).obj targetModule) :
    ∃ (stageIndex : Index) (initialLe : initialIndex ≤ stageIndex)
      (stageMap : (pullback (diagram.map (homOfLE initialLe).op)).obj sourceModule ⟶
        (pullback (diagram.map (homOfLE initialLe).op)).obj targetModule),
      (pullback (cone.π.app (op stageIndex))).map stageMap ≫
          (pullbackCompOfEq (cone.π.app (op stageIndex))
            (diagram.map (homOfLE initialLe).op) (cone.π.app (op initialIndex))
            (cone.w (homOfLE initialLe).op) targetModule).hom =
        (pullbackCompOfEq (cone.π.app (op stageIndex))
          (diagram.map (homOfLE initialLe).op) (cone.π.app (op initialIndex))
          (cone.w (homOfLE initialLe).op) sourceModule).hom ≫ coefficientMap := by
  classical
  letI : ∀ stageIndex, IsAffine (diagram.rightOp.obj stageIndex).unop :=
    fun stageIndex ↦ inferInstanceAs (IsAffine (diagram.obj (op stageIndex)))
  let ringDiagram := diagram.rightOp ⋙ Scheme.Γ
  let sectionsCocone := Scheme.Γ.mapCocone (coconeRightOpOfCone cone)
  have sectionsColimit : IsColimit sectionsCocone :=
    isColimitOfPreserves Scheme.Γ (isColimitCoconeRightOpOfCone diagram limit)
  let initialSections :=
    SheafOfModules.evaluation (diagram.obj (op initialIndex)).ringCatSheaf (op ⊤)
  let limitSections := SheafOfModules.evaluation cone.pt.ringCatSheaf (op ⊤)
  let initialMap : cone.pt ⟶ diagram.obj (op initialIndex) := cone.π.app (op initialIndex)
  letI : Module.FinitePresentation (ringDiagram.obj initialIndex)
      (initialSections.obj sourceModule) := by
    change Module.FinitePresentation Γ(diagram.obj (op initialIndex), ⊤)
      (initialSections.obj sourceModule)
    exact finitePresentation_sections_of_isFinitePresentation sourceModule (isAffineOpen_top _)
  obtain ⟨initialSourceIso, initialSourceUnit⟩ :=
    exists_pullback_sections_iso initialMap sourceModule
  obtain ⟨initialTargetIso, initialTargetUnit⟩ :=
    exists_pullback_sections_iso initialMap targetModule
  let sectionsMap := initialSourceIso.hom ≫ limitSections.map coefficientMap ≫
    initialTargetIso.inv
  obtain ⟨stageIndex, initialLe, liftedMap, sourceComparison, targetComparison,
      sourceNormalization, targetNormalization, square⟩ :=
    ModuleCat.exists_hom_at_stage_of_isColimit ringDiagram sectionsCocone sectionsColimit
      initialIndex (initialSections.obj sourceModule) (initialSections.obj targetModule)
      sectionsMap
  let transition : diagram.obj (op stageIndex) ⟶ diagram.obj (op initialIndex) :=
    diagram.map (homOfLE initialLe).op
  let stageProjection : cone.pt ⟶ diagram.obj (op stageIndex) := cone.π.app (op stageIndex)
  change sectionsMap ≫ targetComparison.hom = sourceComparison.hom ≫
    (ModuleCat.extendScalars stageProjection.appTop.hom).map liftedMap at square
  let stageSections :=
    SheafOfModules.evaluation (diagram.obj (op stageIndex)).ringCatSheaf (op ⊤)
  let sourceComposite := pullbackCompOfEq stageProjection transition initialMap
    (cone.w (homOfLE initialLe).op) sourceModule
  let targetComposite := pullbackCompOfEq stageProjection transition initialMap
    (cone.w (homOfLE initialLe).op) targetModule
  obtain ⟨stageSourceIso, stageSourceUnit⟩ :=
    exists_pullback_sections_iso transition sourceModule
  obtain ⟨stageTargetIso, stageTargetUnit⟩ :=
    exists_pullback_sections_iso transition targetModule
  obtain ⟨stageMap, stageMapSections⟩ := exists_hom_app_top_eq_of_isAffine
    (stageSourceIso.inv ≫ liftedMap ≫ stageTargetIso.hom).hom
  have stageSquare : stageSourceIso.hom ≫ stageSections.map stageMap =
      liftedMap ≫ stageTargetIso.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro sectionValue
    change stageMap.app ⊤ (stageSourceIso.hom sectionValue) = _
    rw [stageMapSections]
    change stageTargetIso.hom
        (liftedMap (stageSourceIso.inv (stageSourceIso.hom sectionValue))) =
      stageTargetIso.hom (liftedMap sectionValue)
    rw [Iso.hom_inv_id_apply]
  obtain ⟨furtherSourceIso, furtherSourceUnit⟩ :=
    exists_pullback_sections_iso stageProjection ((pullback transition).obj sourceModule)
  obtain ⟨furtherTargetIso, furtherTargetUnit⟩ :=
    exists_pullback_sections_iso stageProjection ((pullback transition).obj targetModule)
  have sourceCoherence := pullback_sections_iso_comp transition stageProjection initialMap
    (cone.w (homOfLE initialLe).op) sourceModule initialSourceIso stageSourceIso
    furtherSourceIso sourceComparison initialSourceUnit stageSourceUnit furtherSourceUnit
    sourceNormalization
  have targetCoherence := pullback_sections_iso_comp transition stageProjection initialMap
    (cone.w (homOfLE initialLe).op) targetModule initialTargetIso stageTargetIso
    furtherTargetIso targetComparison initialTargetUnit stageTargetUnit furtherTargetUnit
    targetNormalization
  have furtherNaturality := pullback_sections_iso_naturality stageProjection stageMap
    furtherSourceIso furtherTargetIso furtherSourceUnit furtherTargetUnit
  have extendedStageSquare := congrArg
    (ModuleCat.extendScalars stageProjection.appTop.hom).map stageSquare
  rw [Functor.map_comp, Functor.map_comp] at extendedStageSquare
  refine ⟨stageIndex, initialLe, stageMap, ?_⟩
  change (pullback stageProjection).map stageMap ≫ targetComposite.hom =
    sourceComposite.hom ≫ coefficientMap
  apply hom_ext_of_isQuasicoherent_of_isAffine (scheme := cone.pt)
  intro sectionValue
  suffices sectionsEqual :
      limitSections.map ((pullback stageProjection).map stageMap) ≫
          limitSections.map targetComposite.hom =
        limitSections.map sourceComposite.hom ≫ limitSections.map coefficientMap by
    exact congrArg (fun linearMap ↦ linearMap sectionValue) sectionsEqual
  apply (cancel_epi (sourceComparison.hom ≫
    (ModuleCat.extendScalars stageProjection.appTop.hom).map stageSourceIso.hom ≫
      furtherSourceIso.hom)).mp
  calc
    _ = sourceComparison.hom ≫
        (ModuleCat.extendScalars stageProjection.appTop.hom).map stageSourceIso.hom ≫
          (ModuleCat.extendScalars stageProjection.appTop.hom).map
            (stageSections.map stageMap) ≫ furtherTargetIso.hom ≫
              limitSections.map targetComposite.hom := by
      simpa only [Category.assoc, stageSections, limitSections] using
        congrArg (fun middleMap ↦ sourceComparison.hom ≫
          (ModuleCat.extendScalars stageProjection.appTop.hom).map stageSourceIso.hom ≫
            middleMap ≫ limitSections.map targetComposite.hom) furtherNaturality.symm
    _ = sourceComparison.hom ≫
        (ModuleCat.extendScalars stageProjection.appTop.hom).map liftedMap ≫
          (ModuleCat.extendScalars stageProjection.appTop.hom).map stageTargetIso.hom ≫
            furtherTargetIso.hom ≫ limitSections.map targetComposite.hom := by
      simpa only [Category.assoc] using
        congrArg (fun middleMap ↦ sourceComparison.hom ≫ middleMap ≫
          furtherTargetIso.hom ≫ limitSections.map targetComposite.hom) extendedStageSquare
    _ = sectionsMap ≫ initialTargetIso.hom := by
      calc
        _ = sectionsMap ≫ targetComparison.hom ≫
            (ModuleCat.extendScalars stageProjection.appTop.hom).map stageTargetIso.hom ≫
              furtherTargetIso.hom ≫ limitSections.map targetComposite.hom := by
          simpa only [Category.assoc] using
            congrArg (fun firstMap ↦ firstMap ≫
              (ModuleCat.extendScalars stageProjection.appTop.hom).map stageTargetIso.hom ≫
                furtherTargetIso.hom ≫ limitSections.map targetComposite.hom) square.symm
        _ = _ := by
          simpa only [Category.assoc, limitSections, targetComposite] using
            congrArg (fun linearMap ↦ sectionsMap ≫ linearMap) targetCoherence
    _ = initialSourceIso.hom ≫ limitSections.map coefficientMap := by
      simp [sectionsMap, Category.assoc]
    _ = _ := by
      simpa only [Category.assoc, limitSections, sourceComposite] using
        congrArg (fun linearMap ↦ linearMap ≫ limitSections.map coefficientMap)
          sourceCoherence.symm

/-- Equality of maps between fixed coefficients on an affine inverse limit is detected at a
stage. A finitely presented source suffices; no finiteness condition is imposed on the target. -/
theorem exists_hom_eq_of_affine_limit
    {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] (diagram : Indexᵒᵖ ⥤ Scheme.{schemeUniverse})
    [∀ stageIndex, IsAffine (diagram.obj stageIndex)]
    (cone : Cone diagram) (limit : IsLimit cone) [IsAffine cone.pt]
    (initialIndex : Index) {sourceModule targetModule : (diagram.obj (op initialIndex)).Modules}
    [sourceModule.IsFinitePresentation] [sourceModule.IsQuasicoherent]
    [targetModule.IsQuasicoherent] (firstMap secondMap : sourceModule ⟶ targetModule)
    (equality : (pullback (cone.π.app (op initialIndex))).map firstMap =
      (pullback (cone.π.app (op initialIndex))).map secondMap) :
    ∃ (stageIndex : Index) (initialLe : initialIndex ≤ stageIndex),
      (pullback (diagram.map (homOfLE initialLe).op)).map firstMap =
        (pullback (diagram.map (homOfLE initialLe).op)).map secondMap := by
  letI : ∀ stageIndex, IsAffine (diagram.rightOp.obj stageIndex).unop :=
    fun stageIndex ↦ inferInstanceAs (IsAffine (diagram.obj (op stageIndex)))
  let ringDiagram := diagram.rightOp ⋙ Scheme.Γ
  let sectionsCocone := Scheme.Γ.mapCocone (coconeRightOpOfCone cone)
  have sectionsColimit : IsColimit sectionsCocone :=
    isColimitOfPreserves Scheme.Γ (isColimitCoconeRightOpOfCone diagram limit)
  let initialSections :=
    SheafOfModules.evaluation (diagram.obj (op initialIndex)).ringCatSheaf (op ⊤)
  let initialMap : cone.pt ⟶ diagram.obj (op initialIndex) := cone.π.app (op initialIndex)
  letI : Module.FinitePresentation (ringDiagram.obj initialIndex)
      (initialSections.obj sourceModule) := by
    change Module.FinitePresentation Γ(diagram.obj (op initialIndex), ⊤)
      (initialSections.obj sourceModule)
    exact finitePresentation_sections_of_isFinitePresentation sourceModule (isAffineOpen_top _)
  obtain ⟨sourceIso, sourceUnit⟩ := exists_pullback_sections_iso initialMap sourceModule
  obtain ⟨targetIso, targetUnit⟩ := exists_pullback_sections_iso initialMap targetModule
  have sectionsEqual :
      (ModuleCat.extendScalars initialMap.appTop.hom).map (initialSections.map firstMap) =
        (ModuleCat.extendScalars initialMap.appTop.hom).map (initialSections.map secondMap) := by
    apply (cancel_mono targetIso.hom).mp
    rw [pullback_sections_iso_naturality initialMap firstMap sourceIso targetIso
      sourceUnit targetUnit,
      pullback_sections_iso_naturality initialMap secondMap sourceIso targetIso
        sourceUnit targetUnit, equality]
  obtain ⟨stageIndex, initialLe, stageEquality⟩ :=
    ModuleCat.exists_map_eq_of_map_cocone_eq ringDiagram sectionsCocone sectionsColimit
      initialIndex (initialSections.obj sourceModule) (initialSections.obj targetModule)
      (initialSections.map firstMap) (initialSections.map secondMap) sectionsEqual
  let transition : diagram.obj (op stageIndex) ⟶ diagram.obj (op initialIndex) :=
    diagram.map (homOfLE initialLe).op
  change (ModuleCat.extendScalars transition.appTop.hom).map
      (initialSections.map firstMap) =
    (ModuleCat.extendScalars transition.appTop.hom).map
      (initialSections.map secondMap) at stageEquality
  let stageSections :=
    SheafOfModules.evaluation (diagram.obj (op stageIndex)).ringCatSheaf (op ⊤)
  obtain ⟨stageSourceIso, stageSourceUnit⟩ := exists_pullback_sections_iso transition sourceModule
  obtain ⟨stageTargetIso, stageTargetUnit⟩ := exists_pullback_sections_iso transition targetModule
  refine ⟨stageIndex, initialLe, ?_⟩
  apply hom_ext_of_isQuasicoherent_of_isAffine
  intro sectionValue
  suffices sectionsEqual : stageSections.map ((pullback transition).map firstMap) =
      stageSections.map ((pullback transition).map secondMap) by
    exact congrArg (fun linearMap ↦ linearMap sectionValue) sectionsEqual
  apply (cancel_epi stageSourceIso.hom).mp
  rw [← pullback_sections_iso_naturality transition firstMap stageSourceIso stageTargetIso
    stageSourceUnit stageTargetUnit,
    ← pullback_sections_iso_naturality transition secondMap stageSourceIso stageTargetIso
      stageSourceUnit stageTargetUnit]
  change (ModuleCat.extendScalars transition.appTop.hom).map
      (initialSections.map firstMap) ≫ stageTargetIso.hom =
    (ModuleCat.extendScalars transition.appTop.hom).map
      (initialSections.map secondMap) ≫ stageTargetIso.hom
  exact congrArg (fun sectionsMap ↦ sectionsMap ≫ stageTargetIso.hom) stageEquality

end AlgebraicGeometry.Scheme.Modules
