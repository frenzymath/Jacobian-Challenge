import Jacobian.AlgebraicGeometry.Modules.Limits.Affine
import Jacobian.AlgebraicGeometry.Modules.FinitePresentation.Affine
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Final

/-!
# Finitely presented coefficients on affine charts of inverse limits

Finitely presented module sheaves descend along directed limits of affine
schemes. Applied to the pullback of a fixed affine chart over a stage, this
constructs finitely presented coefficients at a later base stage. The affine
chart itself need not be of finite presentation over the base.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A finitely presented sheaf on a directed affine limit comes from one of its stages. -/
theorem exists_finitePresentation_model_of_affine_limit
    {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] (diagram : Indexᵒᵖ ⥤ Scheme.{schemeUniverse})
    [∀ stageIndex, IsAffine (diagram.obj stageIndex)]
    (cone : Cone diagram) (limit : IsLimit cone) [IsAffine cone.pt]
    (moduleSheaf : cone.pt.Modules) [moduleSheaf.IsFinitePresentation] :
    ∃ (stageIndex : Index) (stageSheaf : (diagram.obj (op stageIndex)).Modules),
      stageSheaf.IsFinitePresentation ∧
      Nonempty ((pullback (cone.π.app (op stageIndex))).obj stageSheaf ≅ moduleSheaf) := by
  classical
  letI : ∀ stageIndex, IsAffine (diagram.rightOp.obj stageIndex).unop :=
    fun stageIndex ↦ inferInstanceAs (IsAffine (diagram.obj (op stageIndex)))
  let ringDiagram := diagram.rightOp ⋙ Scheme.Γ
  let sectionsCocone := Scheme.Γ.mapCocone (coconeRightOpOfCone cone)
  have sectionsColimit : IsColimit sectionsCocone :=
    isColimitOfPreserves Scheme.Γ (isColimitCoconeRightOpOfCone diagram limit)
  let ringComparison : colimit ringDiagram ≅ Γ(cone.pt, ⊤) :=
    (colimit.isColimit ringDiagram).coconePointUniqueUpToIso sectionsColimit
  let sections := ModuleCat.of Γ(cone.pt, ⊤) Γ(moduleSheaf, ⊤)
  letI : Module.FinitePresentation Γ(cone.pt, ⊤) sections :=
    finitePresentation_sections_of_isFinitePresentation moduleSheaf (isAffineOpen_top cone.pt)
  let limitModule := (ModuleCat.extendScalars ringComparison.inv.hom).obj sections
  letI : Algebra Γ(cone.pt, ⊤) (colimit ringDiagram : CommRingCat.{schemeUniverse}) :=
    ringComparison.inv.hom.toAlgebra
  letI : Module.FinitePresentation (colimit ringDiagram : CommRingCat.{schemeUniverse})
      limitModule := by
    change Module.FinitePresentation (colimit ringDiagram : CommRingCat.{schemeUniverse})
      (TensorProduct Γ(cone.pt, ⊤) (colimit ringDiagram : CommRingCat.{schemeUniverse}) sections)
    infer_instance
  obtain ⟨stageIndex, stageModule, finiteStageModule, ⟨moduleComparison⟩⟩ :=
    ModuleCat.exists_finitePresentation_model ringDiagram limitModule
  letI : Module.FinitePresentation Γ(diagram.obj (op stageIndex), ⊤) stageModule := by
    change Module.FinitePresentation (ringDiagram.obj stageIndex) stageModule
    exact finiteStageModule
  have inverseScalars : ringComparison.hom.hom.comp ringComparison.inv.hom =
      RingHom.id Γ(cone.pt, ⊤) :=
    congrArg CommRingCat.Hom.hom ringComparison.inv_hom_id
  let cancel : (ModuleCat.extendScalars ringComparison.hom.hom).obj limitModule ≅ sections :=
    ((ModuleCat.extendScalarsComp ringComparison.inv.hom ringComparison.hom.hom).app
      sections).symm ≪≫
      eqToIso (congrArg (fun ringMap ↦ (ModuleCat.extendScalars ringMap).obj sections)
        inverseScalars) ≪≫ (ModuleCat.extendScalarsId Γ(cone.pt, ⊤)).app sections
  have scalarCompatibility : ringComparison.hom.hom.comp
      (colimit.ι ringDiagram stageIndex).hom = (cone.π.app (op stageIndex)).appTop.hom :=
    congrArg CommRingCat.Hom.hom
      ((colimit.isColimit ringDiagram).comp_coconePointUniqueUpToIso_hom
        sectionsColimit stageIndex)
  let sectionsComparison :
      (ModuleCat.extendScalars (cone.π.app (op stageIndex)).appTop.hom).obj stageModule ≅
        sections :=
    eqToIso (congrArg (fun ringMap ↦ (ModuleCat.extendScalars ringMap).obj stageModule)
      scalarCompatibility.symm) ≪≫
      (ModuleCat.extendScalarsComp (colimit.ι ringDiagram stageIndex).hom
        ringComparison.hom.hom).app stageModule ≪≫
      (ModuleCat.extendScalars ringComparison.hom.hom).mapIso moduleComparison ≪≫ cancel
  letI : moduleSheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData moduleSheaf).choose.isQuasicoherent
  obtain ⟨stageSheaf, finiteStageSheaf, _, comparison⟩ :=
    exists_finitePresentation_model_of_sections
      (source := cone.pt) (target := diagram.obj (op stageIndex))
      (cone.π.app (op stageIndex))
      moduleSheaf stageModule ⟨sectionsComparison⟩
  exact ⟨stageIndex, stageSheaf, finiteStageSheaf, comparison⟩

private def spectrumOverDiagram {Index : Type schemeUniverse} [Preorder Index]
    (diagram : Index ⥤ CommRingCat.{schemeUniverse}) (initialIndex : Index) :
    ({stageIndex : Index // initialIndex ≤ stageIndex})ᵒᵖ ⥤
      Over (Spec (diagram.obj initialIndex)) where
  obj stageIndex := Over.mk (Spec.map (diagram.map (homOfLE stageIndex.unop.property)))
  map {sourceIndex targetIndex} transition := Over.homMk
    ((diagram.op ⋙ Scheme.Spec).map
      (homOfLE (show targetIndex.unop.val ≤ sourceIndex.unop.val from
        leOfHom transition.unop)).op) (by
      change Spec.map (diagram.map _) ≫ Spec.map (diagram.map _) = Spec.map (diagram.map _)
      rw [← Spec.map_comp, ← diagram.map_comp]
      rfl)
  map_id stageIndex := by ext; simp
  map_comp firstTransition secondTransition := by
    ext
    change Spec.map (diagram.map _) = Spec.map (diagram.map _) ≫ Spec.map (diagram.map _)
    rw [← Spec.map_comp, ← diagram.map_comp]
    rfl

private def spectrumOverCone {Index : Type schemeUniverse} [Preorder Index]
    (diagram : Index ⥤ CommRingCat.{schemeUniverse})
    (cone : Cone (diagram.op ⋙ Scheme.Spec)) (initialIndex : Index) :
    Cone (spectrumOverDiagram diagram initialIndex) where
  pt := Over.mk (cone.π.app (op initialIndex))
  π.app stageIndex := Over.homMk (cone.π.app (op stageIndex.unop.val)) (cone.w _)
  π.naturality sourceIndex targetIndex transition := by
    ext
    change cone.π.app (op targetIndex.unop.val) = cone.π.app (op sourceIndex.unop.val) ≫
      (diagram.op ⋙ Scheme.Spec).map (homOfLE (leOfHom transition.unop)).op
    exact (cone.w _).symm

private def chartDiagram {Index : Type schemeUniverse} [Preorder Index]
    (diagram : Index ⥤ CommRingCat.{schemeUniverse}) (initialIndex : Index)
    {chart : Scheme.{schemeUniverse}} (chartMap : chart ⟶ Spec (diagram.obj initialIndex)) :
    ({stageIndex : Index // initialIndex ≤ stageIndex})ᵒᵖ ⥤ Scheme.{schemeUniverse} :=
  spectrumOverDiagram diagram initialIndex ⋙ Over.pullback chartMap ⋙ Over.forget chart

private def chartCone {Index : Type schemeUniverse} [Preorder Index]
    (diagram : Index ⥤ CommRingCat.{schemeUniverse})
    (cone : Cone (diagram.op ⋙ Scheme.Spec)) (initialIndex : Index)
    {chart : Scheme.{schemeUniverse}} (chartMap : chart ⟶ Spec (diagram.obj initialIndex)) :
    Cone (chartDiagram diagram initialIndex chartMap) :=
  (Over.forget chart).mapCone
    ((Over.pullback chartMap).mapCone (spectrumOverCone diagram cone initialIndex))

private theorem isLimit_chartCone
    {Index : Type schemeUniverse} [Preorder Index] [IsDirected Index (· ≤ ·)]
    (diagram : Index ⥤ CommRingCat.{schemeUniverse})
    (cone : Cone (diagram.op ⋙ Scheme.Spec)) (limit : IsLimit cone) (initialIndex : Index)
    {chart : Scheme.{schemeUniverse}} (chartMap : chart ⟶ Spec (diagram.obj initialIndex)) :
    Nonempty (IsLimit (chartCone diagram cone initialIndex chartMap)) := by
  let Tail := {stageIndex : Index // initialIndex ≤ stageIndex}
  letI : Nonempty Tail := ⟨⟨initialIndex, le_rfl⟩⟩
  letI : IsDirectedOrder Tail := ⟨by
    intro sourceIndex targetIndex
    obtain ⟨commonIndex, sourceLe, targetLe⟩ := exists_ge_ge sourceIndex.val targetIndex.val
    exact ⟨⟨commonIndex, sourceIndex.property.trans sourceLe⟩, sourceLe, targetLe⟩⟩
  let inclusion : Tail ⥤ Index :=
    (Subtype.mono_coe (fun stageIndex : Index ↦ initialIndex ≤ stageIndex)).functor
  letI : inclusion.Final := (Monotone.final_functor_iff _).mpr (by
    intro stageIndex
    obtain ⟨commonIndex, initialLe, stageLe⟩ := exists_ge_ge initialIndex stageIndex
    exact ⟨⟨commonIndex, initialLe⟩, stageLe⟩)
  have restrictedLimit : IsLimit (cone.whisker inclusion.op) :=
    (Functor.Initial.isLimitWhiskerEquiv inclusion.op cone).symm limit
  letI : IsConnected Tailᵒᵖ := IsCofiltered.isConnected _
  let comparison :
      (spectrumOverDiagram diagram initialIndex ⋙ Over.forget (Spec (diagram.obj initialIndex))) ≅
        inclusion.op ⋙ diagram.op ⋙ Scheme.Spec :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro sourceIndex targetIndex transition
      simp only [Functor.comp_map, Over.forget_map, spectrumOverDiagram,
        Iso.refl_hom, Category.comp_id, Category.id_comp]
      congr 2)
  have baseLimit : IsLimit ((Over.forget (Spec (diagram.obj initialIndex))).mapCone
      (spectrumOverCone diagram cone initialIndex)) :=
    IsLimit.equivOfNatIsoOfIso comparison _ _ (Cone.ext (Iso.refl _)) restrictedLimit
  have overLimit : IsLimit (spectrumOverCone diagram cone initialIndex) :=
    isLimitOfReflects (Over.forget _) baseLimit
  exact ⟨isLimitOfPreserves (Over.forget chart)
    (isLimitOfPreserves (Over.pullback chartMap) overLimit)⟩

/-- Coefficients on an affine chart after a directed base change come from a later stage. -/
theorem exists_finitePresentation_model_on_affine_pullback
    {Index : Type schemeUniverse} [Preorder Index] [IsDirected Index (· ≤ ·)]
    (diagram : Index ⥤ CommRingCat.{schemeUniverse})
    (cone : Cone (diagram.op ⋙ Scheme.Spec)) (limit : IsLimit cone) [IsAffine cone.pt]
    (initialIndex : Index) {chart : Scheme.{schemeUniverse}} [IsAffine chart]
    (chartMap : chart ⟶ Spec (diagram.obj initialIndex))
    (moduleSheaf : (Limits.pullback (cone.π.app (op initialIndex)) chartMap).Modules)
    [moduleSheaf.IsFinitePresentation] :
    ∃ (stageIndex : Index) (initialLe : initialIndex ≤ stageIndex),
      let parameterMap : Over.mk (cone.π.app (op initialIndex)) ⟶
          Over.mk (Spec.map (diagram.map (homOfLE initialLe))) :=
        Over.homMk (cone.π.app (op stageIndex)) (cone.w (homOfLE initialLe).op)
      ∃ stageSheaf :
          (Limits.pullback (Spec.map (diagram.map (homOfLE initialLe))) chartMap).Modules,
        stageSheaf.IsFinitePresentation ∧
        Nonempty ((pullback (((Over.pullback chartMap).map parameterMap).left)).obj
          stageSheaf ≅ moduleSheaf) := by
  let Tail := {stageIndex : Index // initialIndex ≤ stageIndex}
  letI : Nonempty Tail := ⟨⟨initialIndex, le_rfl⟩⟩
  letI : IsDirectedOrder Tail := ⟨by
    intro sourceIndex targetIndex
    obtain ⟨commonIndex, sourceLe, targetLe⟩ := exists_ge_ge sourceIndex.val targetIndex.val
    exact ⟨⟨commonIndex, sourceIndex.property.trans sourceLe⟩, sourceLe, targetLe⟩⟩
  let stageDiagram := chartDiagram diagram initialIndex chartMap
  let limitCone := chartCone diagram cone initialIndex chartMap
  obtain ⟨chartLimit⟩ := isLimit_chartCone diagram cone limit initialIndex chartMap
  letI : ∀ stageIndex, IsAffine (stageDiagram.obj stageIndex) := by
    intro stageIndex
    change IsAffine
      (Limits.pullback (Spec.map (diagram.map (homOfLE stageIndex.unop.property))) chartMap)
    infer_instance
  letI : IsAffine limitCone.pt := Scheme.isAffine_of_isLimit limitCone chartLimit
  obtain ⟨stageIndex, stageSheaf, finiteStageSheaf, comparison⟩ :=
    exists_finitePresentation_model_of_affine_limit stageDiagram limitCone chartLimit moduleSheaf
  exact ⟨stageIndex.val, stageIndex.property, stageSheaf, finiteStageSheaf, comparison⟩

end AlgebraicGeometry.Scheme.Modules
