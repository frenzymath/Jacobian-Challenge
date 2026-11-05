import Jacobian.AlgebraicGeometry.Modules.Limits.GlobalHom
import Jacobian.AlgebraicGeometry.Modules.FpqcSectionDescent
import Jacobian.CategoryTheory.Sites.IsSheafFor

/-!
# Descent of coefficient morphisms over finite affine covers

A morphism between the pullbacks of a finitely presented quasi-coherent source
and a quasi-coherent target along a directed affine inverse limit descends to a
stage. A finite affine cover by affine open immersions suffices: local lifts
descend simultaneously, their agreements on the affine overlaps hold at a
common later stage, and Zariski descent glues the resulting morphism.

The coefficient objects are given on the base scheme. No descent of coefficient
objects or prescribed compatibility of local lifts is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

private lemma homPresheaf_map_eq_iff
    (presheaf : Pseudofunctor (LocallyDiscrete Scheme.{schemeUniverse}ᵒᵖ) Cat)
    {scheme : Scheme.{schemeUniverse}}
    (sourceModule targetModule : presheaf.obj (.mk (op scheme)))
    {source target : Over scheme} (morphism : source ⟶ target)
    (firstMap secondMap : (presheaf.map target.hom.op.toLoc).toFunctor.obj sourceModule ⟶
      (presheaf.map target.hom.op.toLoc).toFunctor.obj targetModule) :
    (presheaf.presheafHom sourceModule targetModule).map morphism.op firstMap =
        (presheaf.presheafHom sourceModule targetModule).map morphism.op secondMap ↔
      (presheaf.map morphism.left.op.toLoc).toFunctor.map firstMap =
        (presheaf.map morphism.left.op.toLoc).toFunctor.map secondMap := by
  change pullHom (F := presheaf) firstMap morphism.left source.hom source.hom
      morphism.w morphism.w =
    pullHom (F := presheaf) secondMap morphism.left source.hom source.hom
      morphism.w morphism.w ↔ _
  dsimp only [pullHom]
  simp only [← Category.assoc, cancel_mono, cancel_epi]

private lemma presheaf_recovery_of_overMap_iso
    {scheme initialScheme : Scheme.{schemeUniverse}} (baseMap : initialScheme ⟶ scheme)
    (presheaf : (Over scheme)ᵒᵖ ⥤ Type schemeUniverse)
    (localPresheaf : (Over initialScheme)ᵒᵖ ⥤ Type schemeUniverse)
    (comparison : (Over.map baseMap).op ⋙ presheaf ≅ localPresheaf)
    {limitObject stageObject : Over initialScheme} {limitPoint stagePoint : Over scheme}
    (limitIso : (Over.map baseMap).obj limitObject ≅ limitPoint)
    (stageIso : (Over.map baseMap).obj stageObject ≅ stagePoint)
    (transition : limitObject ⟶ stageObject) (projection : limitPoint ⟶ stagePoint)
    (factorization : projection ≫ stageIso.inv =
      limitIso.inv ≫ (Over.map baseMap).map transition)
    (limitMap : presheaf.obj (op limitPoint))
    (stageMap : localPresheaf.obj (op stageObject))
    (recovery : localPresheaf.map transition.op stageMap =
      comparison.hom.app (op limitObject) (presheaf.map limitIso.hom.op limitMap)) :
    presheaf.map projection.op
      (presheaf.map stageIso.inv.op (comparison.inv.app (op stageObject) stageMap)) =
        limitMap := by
  have naturality : presheaf.map ((Over.map baseMap).map transition).op
        (comparison.inv.app (op stageObject) stageMap) =
      comparison.inv.app (op limitObject) (localPresheaf.map transition.op stageMap) := by
    simpa only [Functor.comp_obj, Functor.comp_map, Functor.op_obj, Functor.op_map,
      unop_op, Quiver.Hom.unop_op] using
      (comparison.inv.naturality_apply transition.op stageMap).symm
  calc
    _ = presheaf.map limitIso.inv.op
        (comparison.inv.app (op limitObject) (localPresheaf.map transition.op stageMap)) := by
      rw [← presheaf.map_comp_apply, ← op_comp, factorization, op_comp,
        presheaf.map_comp_apply, naturality]
    _ = presheaf.map limitIso.inv.op (presheaf.map limitIso.hom.op limitMap) := by
      rw [recovery]
      exact congrArg (presheaf.map limitIso.inv.op)
        (Iso.hom_inv_id_apply (comparison.app (op limitObject)) _)
    _ = limitMap := by
      rw [← presheaf.map_comp_apply, ← op_comp, limitIso.inv_hom_id,
        CategoryTheory.op_id, CategoryTheory.Functor.map_id_apply]

private theorem exists_homPresheaf_lifts_of_affine_limits
    {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] {Label : Type schemeUniverse} [Finite Label]
    {scheme : Scheme.{schemeUniverse}} (sourceModule targetModule : scheme.Modules)
    [sourceModule.IsFinitePresentation] [sourceModule.IsQuasicoherent]
    [targetModule.IsQuasicoherent]
    (diagrams : Label → Indexᵒᵖ ⥤ Over scheme)
    [∀ label stageIndex, IsAffine ((diagrams label).obj stageIndex).left]
    (cones : ∀ label, Cone (diagrams label))
    (limits : ∀ label, IsLimit ((Over.forget scheme).mapCone (cones label)))
    [∀ label, IsAffine (cones label).pt.left] (initialIndex : Index)
    (coefficientMaps : ∀ label,
      (modulesPseudofunctor.presheafHom sourceModule targetModule).obj
        (op (cones label).pt)) :
    ∃ (stageIndex : Index) (_ : initialIndex ≤ stageIndex)
      (stageMaps : ∀ label,
        (modulesPseudofunctor.presheafHom sourceModule targetModule).obj
          (op ((diagrams label).obj (op stageIndex)))),
      ∀ label,
        (modulesPseudofunctor.presheafHom sourceModule targetModule).map
          ((cones label).π.app (op stageIndex)).op (stageMaps label) = coefficientMaps label := by
  let homPresheaf : (Over scheme)ᵒᵖ ⥤ Type schemeUniverse :=
    modulesPseudofunctor.presheafHom sourceModule targetModule
  let initialProjection (label : Label) := ((diagrams label).obj (op initialIndex)).hom
  let localSource (label : Label) := (pullback (initialProjection label)).obj sourceModule
  let localTarget (label : Label) := (pullback (initialProjection label)).obj targetModule
  haveI (label : Label) : (localSource label).IsFinitePresentation := by
    dsimp only [localSource]
    infer_instance
  haveI (label : Label) : (localSource label).IsQuasicoherent := by
    dsimp only [localSource]
    infer_instance
  haveI (label : Label) : (localTarget label).IsQuasicoherent := by
    dsimp only [localTarget]
    infer_instance
  have comparison (label : Label) :
      (Over.map (initialProjection label)).op ⋙ homPresheaf ≅
        modulesPseudofunctor.presheafHom (localSource label) (localTarget label) :=
    modulesPseudofunctor.overMapCompPresheafHomIso sourceModule targetModule
      (initialProjection label)
  let limitObject (label : Label) : Over ((diagrams label).obj (op initialIndex)).left :=
    Over.mk ((cones label).π.app (op initialIndex)).left
  let limitIso (label : Label) :
      (Over.map (initialProjection label)).obj (limitObject label) ≅ (cones label).pt :=
    Over.isoMk (Iso.refl _) (by
      dsimp only [Iso.refl_hom]
      rw [Category.id_comp]
      exact ((cones label).π.app (op initialIndex)).w.symm)
  let localCoefficientMaps (label : Label) :
      (modulesPseudofunctor.presheafHom (localSource label) (localTarget label)).obj
        (op (limitObject label)) :=
    (comparison label).hom.app (op (limitObject label))
      (homPresheaf.map (limitIso label).hom.op (coefficientMaps label))
  haveI : ∀ label stageIndex,
      IsAffine ((diagrams label ⋙ Over.forget scheme).obj stageIndex) :=
    fun label stageIndex ↦ inferInstanceAs (IsAffine ((diagrams label).obj stageIndex).left)
  haveI : ∀ label, IsAffine ((Over.forget scheme).mapCone (cones label)).pt :=
    fun label ↦ inferInstanceAs (IsAffine (cones label).pt.left)
  obtain ⟨stageIndex, initialLe, localMaps, localRecovery⟩ :=
    exists_homs_of_affine_limits
      (fun label ↦ diagrams label ⋙ Over.forget scheme)
      (fun label ↦ (Over.forget scheme).mapCone (cones label)) limits initialIndex
      localSource localTarget localCoefficientMaps
  let stageObject (label : Label) : Over ((diagrams label).obj (op initialIndex)).left :=
    Over.mk ((diagrams label).map (homOfLE initialLe).op).left
  let stageIso (label : Label) :
      (Over.map (initialProjection label)).obj (stageObject label) ≅
        (diagrams label).obj (op stageIndex) :=
    Over.isoMk (Iso.refl _) (by
      dsimp only [Iso.refl_hom]
      rw [Category.id_comp]
      exact ((diagrams label).map (homOfLE initialLe).op).w.symm)
  let stageMaps (label : Label) :
      homPresheaf.obj (op ((diagrams label).obj (op stageIndex))) :=
    homPresheaf.map (stageIso label).inv.op
      ((comparison label).inv.app (op (stageObject label)) (localMaps label))
  refine ⟨stageIndex, initialLe, stageMaps, ?_⟩
  intro label
  let transition : limitObject label ⟶ stageObject label :=
    Over.homMk ((cones label).π.app (op stageIndex)).left
      (congrArg Over.Hom.left ((cones label).w (homOfLE initialLe).op))
  have factorization : (cones label).π.app (op stageIndex) ≫ (stageIso label).inv =
      (limitIso label).inv ≫ (Over.map (initialProjection label)).map transition := by
    ext
    change ((cones label).π.app (op stageIndex)).left ≫ 𝟙 _ =
      𝟙 _ ≫ ((cones label).π.app (op stageIndex)).left
    simp only [Category.comp_id, Category.id_comp]
  have recovery :
      (modulesPseudofunctor.presheafHom (localSource label) (localTarget label)).map
          transition.op (localMaps label) = localCoefficientMaps label := by
    rw [Pseudofunctor.presheafHom_map_eq_pullHom]
    exact localRecovery label
  exact presheaf_recovery_of_overMap_iso (initialProjection label) homPresheaf
    (modulesPseudofunctor.presheafHom (localSource label) (localTarget label))
    (comparison label) (limitIso label) (stageIso label) transition
    ((cones label).π.app (op stageIndex)) factorization (coefficientMaps label)
    (localMaps label) recovery

private theorem exists_homPresheaf_equalities_of_affine_limits
    {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] {Label : Type schemeUniverse} [Finite Label]
    {scheme : Scheme.{schemeUniverse}} (sourceModule targetModule : scheme.Modules)
    [sourceModule.IsFinitePresentation] [sourceModule.IsQuasicoherent]
    [targetModule.IsQuasicoherent]
    (diagrams : Label → Indexᵒᵖ ⥤ Over scheme)
    [∀ label stageIndex, IsAffine ((diagrams label).obj stageIndex).left]
    (cones : ∀ label, Cone (diagrams label))
    (limits : ∀ label, IsLimit ((Over.forget scheme).mapCone (cones label)))
    [∀ label, IsAffine (cones label).pt.left] (initialIndex : Index)
    (firstMaps secondMaps : ∀ label,
      (modulesPseudofunctor.presheafHom sourceModule targetModule).obj
        (op ((diagrams label).obj (op initialIndex))))
    (equalities : ∀ label,
      (modulesPseudofunctor.presheafHom sourceModule targetModule).map
          ((cones label).π.app (op initialIndex)).op (firstMaps label) =
        (modulesPseudofunctor.presheafHom sourceModule targetModule).map
          ((cones label).π.app (op initialIndex)).op (secondMaps label)) :
    ∃ (stageIndex : Index) (initialLe : initialIndex ≤ stageIndex), ∀ label,
      (modulesPseudofunctor.presheafHom sourceModule targetModule).map
          ((diagrams label).map (homOfLE initialLe).op).op (firstMaps label) =
        (modulesPseudofunctor.presheafHom sourceModule targetModule).map
          ((diagrams label).map (homOfLE initialLe).op).op (secondMaps label) := by
  letI : ∀ label stageIndex,
      IsAffine ((diagrams label ⋙ Over.forget scheme).obj stageIndex) :=
    fun label stageIndex ↦ inferInstanceAs (IsAffine ((diagrams label).obj stageIndex).left)
  letI : ∀ label, IsAffine ((Over.forget scheme).mapCone (cones label)).pt :=
    fun label ↦ inferInstanceAs (IsAffine (cones label).pt.left)
  letI : ∀ label,
      ((pullback ((diagrams label).obj (op initialIndex)).hom).obj sourceModule).IsFinitePresentation :=
    fun label ↦ inferInstance
  letI : ∀ label,
      ((pullback ((diagrams label).obj (op initialIndex)).hom).obj sourceModule).IsQuasicoherent :=
    fun label ↦ inferInstance
  letI : ∀ label,
      ((pullback ((diagrams label).obj (op initialIndex)).hom).obj targetModule).IsQuasicoherent :=
    fun label ↦ inferInstance
  obtain ⟨stageIndex, initialLe, stageEqualities⟩ :=
    exists_hom_eqs_of_affine_limits
      (fun label ↦ diagrams label ⋙ Over.forget scheme)
      (fun label ↦ (Over.forget scheme).mapCone (cones label)) limits initialIndex
      (fun label ↦ (pullback ((diagrams label).obj (op initialIndex)).hom).obj sourceModule)
      (fun label ↦ (pullback ((diagrams label).obj (op initialIndex)).hom).obj targetModule)
      firstMaps secondMaps (fun label ↦
        (homPresheaf_map_eq_iff modulesPseudofunctor sourceModule targetModule _ _ _).mp
          (equalities label))
  exact ⟨stageIndex, initialLe, fun label ↦
    (homPresheaf_map_eq_iff modulesPseudofunctor sourceModule targetModule _ _ _).mpr
      (stageEqualities label)⟩

private abbrev chartDiagram
    {Index : Type schemeUniverse} [Preorder Index] {scheme : Scheme.{schemeUniverse}}
    (diagram : Indexᵒᵖ ⥤ Over scheme) {chart : Scheme.{schemeUniverse}}
    (chartMap : chart ⟶ scheme) : Indexᵒᵖ ⥤ Over scheme where
  obj stageIndex := Over.mk (pullback.fst (diagram.obj stageIndex).hom chartMap ≫
    (diagram.obj stageIndex).hom)
  map {sourceIndex targetIndex} transition :=
    Over.homMk (pullback.lift
      (pullback.fst (diagram.obj sourceIndex).hom chartMap ≫ (diagram.map transition).left)
      (pullback.snd (diagram.obj sourceIndex).hom chartMap)
      (by rw [Category.assoc, (diagram.map transition).w, pullback.condition])) (by
        simpa only [Over.mk_hom, pullback.lift_fst_assoc, Category.assoc] using
          congrArg (fun structureMap ↦
            pullback.fst (diagram.obj sourceIndex).hom chartMap ≫ structureMap)
            (diagram.map transition).w)
  map_id stageIndex := by
    ext
    apply pullback.hom_ext <;> simp
  map_comp firstTransition secondTransition := by
    ext
    apply pullback.hom_ext <;> simp [Category.assoc]

private abbrev chartCone
    {Index : Type schemeUniverse} [Preorder Index] {scheme : Scheme.{schemeUniverse}}
    {diagram : Indexᵒᵖ ⥤ Over scheme} (cone : Cone diagram)
    {chart : Scheme.{schemeUniverse}} (chartMap : chart ⟶ scheme) :
    Cone (chartDiagram diagram chartMap) where
  pt := Over.mk (pullback.fst cone.pt.hom chartMap ≫ cone.pt.hom)
  π :=
    { app stageIndex := Over.homMk (pullback.lift
        (pullback.fst cone.pt.hom chartMap ≫ (cone.π.app stageIndex).left)
        (pullback.snd cone.pt.hom chartMap)
        (by
          rw [Category.assoc, (cone.π.app stageIndex).w]
          change pullback.fst cone.pt.hom chartMap ≫ cone.pt.hom =
            pullback.snd cone.pt.hom chartMap ≫ chartMap
          exact pullback.condition)) (by
          simpa only [Over.mk_hom, pullback.lift_fst_assoc, Category.assoc,
            Functor.const_obj_obj] using
            congrArg (fun structureMap ↦ pullback.fst cone.pt.hom chartMap ≫ structureMap)
              (cone.π.app stageIndex).w)
      naturality := by
        intro sourceIndex targetIndex transition
        ext
        apply pullback.hom_ext
        · simpa only [Functor.const_obj_map, Functor.const_obj_obj, Over.id_left,
            Over.homMk_left, Over.comp_left,
            pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp, Category.assoc] using
            (congrArg (fun projection ↦ pullback.fst cone.pt.hom chartMap ≫ projection.left)
              (cone.w transition)).symm
        · simp }

private def isLimit_chartCone
    {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] {scheme : Scheme.{schemeUniverse}}
    {diagram : Indexᵒᵖ ⥤ Over scheme} (cone : Cone diagram)
    (limit : IsLimit ((Over.forget scheme).mapCone cone))
    {chart : Scheme.{schemeUniverse}} (chartMap : chart ⟶ scheme) :
    IsLimit ((Over.forget scheme).mapCone (chartCone cone chartMap)) := by
  letI : IsConnected Indexᵒᵖ := IsCofiltered.isConnected _
  have overLimit : IsLimit cone := isLimitOfReflects (Over.forget scheme) limit
  change IsLimit ((Over.forget chart).mapCone ((Over.pullback chartMap).mapCone cone))
  exact isLimitOfPreserves (Over.forget chart)
    (isLimitOfPreserves (Over.pullback chartMap) overLimit)

private def chartProjection
    {scheme chart : Scheme.{schemeUniverse}} (point : Over scheme) (chartMap : chart ⟶ scheme) :
    Over.mk (pullback.fst point.hom chartMap ≫ point.hom) ⟶ point :=
  Over.homMk (pullback.fst point.hom chartMap) rfl

private def chartFactor
    {scheme firstChart secondChart : Scheme.{schemeUniverse}} (point : Over scheme)
    (firstChartMap : firstChart ⟶ scheme) (secondChartMap : secondChart ⟶ scheme)
    (factor : firstChart ⟶ secondChart) (factorization : factor ≫ secondChartMap = firstChartMap) :
    Over.mk (pullback.fst point.hom firstChartMap ≫ point.hom) ⟶
      Over.mk (pullback.fst point.hom secondChartMap ≫ point.hom) :=
  Over.homMk (pullback.lift (pullback.fst point.hom firstChartMap)
    (pullback.snd point.hom firstChartMap ≫ factor)
    (by rw [Category.assoc, factorization, pullback.condition])) (by simp)

private lemma chartFactor_naturality
    {Index : Type schemeUniverse} [Preorder Index] {scheme : Scheme.{schemeUniverse}}
    (diagram : Indexᵒᵖ ⥤ Over scheme)
    {firstChart secondChart : Scheme.{schemeUniverse}}
    (firstChartMap : firstChart ⟶ scheme) (secondChartMap : secondChart ⟶ scheme)
    (factor : firstChart ⟶ secondChart) (factorization : factor ≫ secondChartMap = firstChartMap)
    {sourceIndex targetIndex : Indexᵒᵖ} (transition : sourceIndex ⟶ targetIndex) :
    (chartDiagram diagram firstChartMap).map transition ≫
        chartFactor (diagram.obj targetIndex) firstChartMap secondChartMap factor factorization =
      chartFactor (diagram.obj sourceIndex) firstChartMap secondChartMap factor factorization ≫
        (chartDiagram diagram secondChartMap).map transition := by
  ext
  apply pullback.hom_ext <;> simp [chartDiagram, chartFactor, Category.assoc]

private lemma chartFactor_cone
    {Index : Type schemeUniverse} [Preorder Index] {scheme : Scheme.{schemeUniverse}}
    {diagram : Indexᵒᵖ ⥤ Over scheme} (cone : Cone diagram)
    {firstChart secondChart : Scheme.{schemeUniverse}}
    (firstChartMap : firstChart ⟶ scheme) (secondChartMap : secondChart ⟶ scheme)
    (factor : firstChart ⟶ secondChart) (factorization : factor ≫ secondChartMap = firstChartMap)
    (stageIndex : Indexᵒᵖ) :
    (chartCone cone firstChartMap).π.app stageIndex ≫
        chartFactor (diagram.obj stageIndex) firstChartMap secondChartMap factor factorization =
      chartFactor cone.pt firstChartMap secondChartMap factor factorization ≫
        (chartCone cone secondChartMap).π.app stageIndex := by
  ext
  apply pullback.hom_ext <;> simp [chartCone, chartFactor, Category.assoc]

private lemma chartProjection_naturality
    {Index : Type schemeUniverse} [Preorder Index] {scheme : Scheme.{schemeUniverse}}
    {diagram : Indexᵒᵖ ⥤ Over scheme} (cone : Cone diagram)
    {chart : Scheme.{schemeUniverse}} (chartMap : chart ⟶ scheme) (stageIndex : Indexᵒᵖ) :
    (chartCone cone chartMap).π.app stageIndex ≫
        chartProjection (diagram.obj stageIndex) chartMap =
      chartProjection cone.pt chartMap ≫ cone.π.app stageIndex := by
  ext
  simp [chartCone, chartProjection]

private lemma chartFactor_projection
    {scheme firstChart secondChart : Scheme.{schemeUniverse}} (point : Over scheme)
    (firstChartMap : firstChart ⟶ scheme) (secondChartMap : secondChart ⟶ scheme)
    (factor : firstChart ⟶ secondChart) (factorization : factor ≫ secondChartMap = firstChartMap) :
    chartFactor point firstChartMap secondChartMap factor factorization ≫
        chartProjection point secondChartMap = chartProjection point firstChartMap := by
  ext
  simp [chartFactor, chartProjection]

private lemma compatible_of_overlap_eq
    {scheme : Scheme.{schemeUniverse}} (homPresheaf : (Over scheme)ᵒᵖ ⥤ Type*)
    (point : Over scheme) (cover : scheme.OpenCover.{schemeUniverse})
    (localMaps : ∀ chartIndex, homPresheaf.obj
      (op (Over.mk (pullback.fst point.hom (cover.f chartIndex) ≫ point.hom))))
    (overlapEqualities : ∀ firstIndex secondIndex,
      homPresheaf.map (chartFactor point
          (pullback.fst (cover.f firstIndex) (cover.f secondIndex) ≫ cover.f firstIndex)
          (cover.f firstIndex) (pullback.fst _ _) rfl).op (localMaps firstIndex) =
        homPresheaf.map (chartFactor point
          (pullback.fst (cover.f firstIndex) (cover.f secondIndex) ≫ cover.f firstIndex)
          (cover.f secondIndex) (pullback.snd _ _) pullback.condition.symm).op
          (localMaps secondIndex)) :
    Presieve.Arrows.Compatible homPresheaf
      (fun chartIndex ↦ chartProjection point (cover.f chartIndex)) localMaps := by
  intro firstIndex secondIndex testScheme firstMap secondMap equality
  have projectionEquality :
      firstMap.left ≫ pullback.fst point.hom (cover.f firstIndex) =
        secondMap.left ≫ pullback.fst point.hom (cover.f secondIndex) :=
    congrArg Over.Hom.left equality
  let overlapMap := pullback.fst (cover.f firstIndex) (cover.f secondIndex) ≫ cover.f firstIndex
  let pairMap : testScheme.left ⟶ Limits.pullback (cover.f firstIndex) (cover.f secondIndex) :=
    pullback.lift (firstMap.left ≫ pullback.snd point.hom (cover.f firstIndex))
      (secondMap.left ≫ pullback.snd point.hom (cover.f secondIndex)) (by
        calc
          _ = (firstMap.left ≫ pullback.fst point.hom (cover.f firstIndex)) ≫ point.hom := by
            simpa only [Category.assoc] using
              congrArg (fun projection ↦ firstMap.left ≫ projection)
                (Limits.pullback.condition (f := point.hom) (g := cover.f firstIndex)).symm
          _ = (secondMap.left ≫ pullback.fst point.hom (cover.f secondIndex)) ≫ point.hom :=
            congrArg (fun projection ↦ projection ≫ point.hom) projectionEquality
          _ = _ := by
            simpa only [Category.assoc] using
              congrArg (fun projection ↦ secondMap.left ≫ projection)
                (Limits.pullback.condition (f := point.hom) (g := cover.f secondIndex)))
  let overlapLift : testScheme ⟶ Over.mk (pullback.fst point.hom overlapMap ≫ point.hom) :=
    Over.homMk
      (pullback.lift (firstMap.left ≫ pullback.fst point.hom (cover.f firstIndex)) pairMap
        (by
          calc
            _ = (firstMap.left ≫ pullback.snd point.hom (cover.f firstIndex)) ≫
                cover.f firstIndex := by
              simpa only [Category.assoc] using
                congrArg (fun projection ↦ firstMap.left ≫ projection)
                  (Limits.pullback.condition (f := point.hom) (g := cover.f firstIndex))
            _ = _ := by
              dsimp only [pairMap, overlapMap]
              simp only [pullback.lift_fst_assoc, Category.assoc])) (by
          simpa only [Over.mk_hom, pullback.lift_fst_assoc, Category.assoc] using firstMap.w)
  have firstFactorization : overlapLift ≫ chartFactor point overlapMap
      (cover.f firstIndex) (pullback.fst _ _) rfl = firstMap := by
    ext
    apply pullback.hom_ext <;> simp [overlapLift, pairMap, chartFactor, Category.assoc]
  have secondFactorization : overlapLift ≫ chartFactor point overlapMap
      (cover.f secondIndex) (pullback.snd _ _) pullback.condition.symm = secondMap := by
    ext
    apply pullback.hom_ext
    · simpa [overlapLift, chartFactor, Category.assoc] using projectionEquality
    · simp [overlapLift, pairMap, chartFactor, Category.assoc]
  rw [← firstFactorization, ← secondFactorization]
  simpa only [op_comp, Functor.map_comp, types_comp_apply] using
    congrArg (homPresheaf.map overlapLift.op) (overlapEqualities firstIndex secondIndex)

/-- A morphism out of a finitely presented quasi-coherent coefficient on a directed affine
inverse limit descends to a stage. A finite affine cover by affine morphisms ensures that
the pair intersections used to enforce compatibility are affine. The target coefficient
need only be quasi-coherent. The recovery equation is native coherent module pullback. -/
theorem exists_hom_of_finite_affine_cover_limit
    {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] {scheme : Scheme.{schemeUniverse}}
    (cover : scheme.OpenCover.{schemeUniverse}) [Finite cover.I₀]
    [∀ chartIndex, IsAffine (cover.X chartIndex)]
    [∀ chartIndex, IsAffineHom (cover.f chartIndex)]
    (diagram : Indexᵒᵖ ⥤ Over scheme)
    [∀ stageIndex, IsAffineHom (diagram.obj stageIndex).hom]
    (cone : Cone diagram) (limit : IsLimit ((Over.forget scheme).mapCone cone))
    [IsAffineHom cone.pt.hom] (initialIndex : Index)
    {sourceModule targetModule : scheme.Modules}
    [sourceModule.IsFinitePresentation] [sourceModule.IsQuasicoherent]
    [targetModule.IsQuasicoherent]
    (coefficientMap : (pullback cone.pt.hom).obj sourceModule ⟶
      (pullback cone.pt.hom).obj targetModule) :
    ∃ (stageIndex : Index) (_ : initialIndex ≤ stageIndex)
      (stageMap : (pullback (diagram.obj (op stageIndex)).hom).obj sourceModule ⟶
        (pullback (diagram.obj (op stageIndex)).hom).obj targetModule),
      pullHom (F := modulesPseudofunctor) stageMap (cone.π.app (op stageIndex)).left
        cone.pt.hom cone.pt.hom (cone.π.app (op stageIndex)).w
        (cone.π.app (op stageIndex)).w = coefficientMap := by
  classical
  let homPresheaf : (Over scheme)ᵒᵖ ⥤ Type schemeUniverse :=
    modulesPseudofunctor.presheafHom sourceModule targetModule
  let limitCoefficientMap : homPresheaf.obj (op cone.pt) := coefficientMap
  let diagrams (chartIndex : cover.I₀) := chartDiagram diagram (cover.f chartIndex)
  let cones (chartIndex : cover.I₀) := chartCone cone (cover.f chartIndex)
  haveI (chartIndex : cover.I₀) (stageIndex : Indexᵒᵖ) :
      IsAffine ((diagrams chartIndex).obj stageIndex).left := by
    change IsAffine (Limits.pullback (diagram.obj stageIndex).hom (cover.f chartIndex))
    infer_instance
  haveI (chartIndex : cover.I₀) : IsAffine (cones chartIndex).pt.left := by
    change IsAffine (Limits.pullback cone.pt.hom (cover.f chartIndex))
    infer_instance
  let localCoefficientMaps (chartIndex : cover.I₀) :=
    homPresheaf.map (chartProjection cone.pt (cover.f chartIndex)).op limitCoefficientMap
  obtain ⟨localIndex, initialLeLocal, localMaps, localRecovery⟩ :=
    exists_homPresheaf_lifts_of_affine_limits sourceModule targetModule diagrams cones
      (fun chartIndex ↦ isLimit_chartCone cone limit (cover.f chartIndex))
      initialIndex localCoefficientMaps
  have chartRecovery (chartIndex : cover.I₀) :
      homPresheaf.map ((chartCone cone (cover.f chartIndex)).π.app (op localIndex)).op
          (localMaps chartIndex) =
        homPresheaf.map (chartProjection cone.pt (cover.f chartIndex)).op limitCoefficientMap :=
    localRecovery chartIndex
  let overlapMap (pair : cover.I₀ × cover.I₀) :=
    pullback.fst (cover.f pair.1) (cover.f pair.2) ≫ cover.f pair.1
  let overlapDiagrams (pair : cover.I₀ × cover.I₀) := chartDiagram diagram (overlapMap pair)
  let overlapCones (pair : cover.I₀ × cover.I₀) := chartCone cone (overlapMap pair)
  haveI (pair : cover.I₀ × cover.I₀) : IsAffine (Limits.pullback (cover.f pair.1) (cover.f pair.2)) :=
    inferInstance
  haveI (pair : cover.I₀ × cover.I₀) (stageIndex : Indexᵒᵖ) :
      IsAffine ((overlapDiagrams pair).obj stageIndex).left := by
    change IsAffine (Limits.pullback (diagram.obj stageIndex).hom (overlapMap pair))
    infer_instance
  haveI (pair : cover.I₀ × cover.I₀) : IsAffine (overlapCones pair).pt.left := by
    change IsAffine (Limits.pullback cone.pt.hom (overlapMap pair))
    infer_instance
  let firstOverlapMaps (pair : cover.I₀ × cover.I₀) :=
    homPresheaf.map (chartFactor (diagram.obj (op localIndex)) (overlapMap pair)
      (cover.f pair.1) (pullback.fst _ _) rfl).op (localMaps pair.1)
  let secondOverlapMaps (pair : cover.I₀ × cover.I₀) :=
    homPresheaf.map (chartFactor (diagram.obj (op localIndex)) (overlapMap pair)
      (cover.f pair.2) (pullback.snd _ _) pullback.condition.symm).op (localMaps pair.2)
  have overlapRecovery (pair : cover.I₀ × cover.I₀) :
      homPresheaf.map ((overlapCones pair).π.app (op localIndex)).op (firstOverlapMaps pair) =
        homPresheaf.map ((overlapCones pair).π.app (op localIndex)).op
          (secondOverlapMaps pair) := by
    change homPresheaf.map ((chartCone cone (overlapMap pair)).π.app (op localIndex)).op
        (homPresheaf.map (chartFactor (diagram.obj (op localIndex)) (overlapMap pair)
          (cover.f pair.1) (pullback.fst _ _) rfl).op (localMaps pair.1)) =
      homPresheaf.map ((chartCone cone (overlapMap pair)).π.app (op localIndex)).op
        (homPresheaf.map (chartFactor (diagram.obj (op localIndex)) (overlapMap pair)
          (cover.f pair.2) (pullback.snd _ _) pullback.condition.symm).op (localMaps pair.2))
    rw [← homPresheaf.map_comp_apply, ← homPresheaf.map_comp_apply, ← op_comp, ← op_comp]
    rw [chartFactor_cone, chartFactor_cone]
    simp only [op_comp, Functor.map_comp_apply]
    refine (congrArg (homPresheaf.map (chartFactor cone.pt (overlapMap pair)
      (cover.f pair.1) (pullback.fst _ _) rfl).op) (chartRecovery pair.1)).trans ?_
    refine Eq.trans ?_ (congrArg (homPresheaf.map (chartFactor cone.pt (overlapMap pair)
      (cover.f pair.2) (pullback.snd _ _) pullback.condition.symm).op)
        (chartRecovery pair.2)).symm
    rw [← homPresheaf.map_comp_apply, ← homPresheaf.map_comp_apply, ← op_comp, ← op_comp,
      chartFactor_projection, chartFactor_projection]
  obtain ⟨stageIndex, localLe, overlapEqualities⟩ :=
    exists_homPresheaf_equalities_of_affine_limits sourceModule targetModule
      overlapDiagrams overlapCones
      (fun pair ↦ isLimit_chartCone cone limit (overlapMap pair)) localIndex
      firstOverlapMaps secondOverlapMaps overlapRecovery
  let stageMaps (chartIndex : cover.I₀) :
      homPresheaf.obj (op ((diagrams chartIndex).obj (op stageIndex))) :=
    homPresheaf.map ((diagrams chartIndex).map (homOfLE localLe).op).op (localMaps chartIndex)
  have stageOverlapEqualities (firstIndex secondIndex : cover.I₀) :
      homPresheaf.map (chartFactor (diagram.obj (op stageIndex))
          (overlapMap (firstIndex, secondIndex)) (cover.f firstIndex) (pullback.fst _ _) rfl).op
          (stageMaps firstIndex) =
        homPresheaf.map (chartFactor (diagram.obj (op stageIndex))
          (overlapMap (firstIndex, secondIndex)) (cover.f secondIndex) (pullback.snd _ _)
          pullback.condition.symm).op (stageMaps secondIndex) := by
    have equality := overlapEqualities (firstIndex, secondIndex)
    change homPresheaf.map
        ((chartDiagram diagram (overlapMap (firstIndex, secondIndex))).map
          (homOfLE localLe).op).op
        (homPresheaf.map (chartFactor (diagram.obj (op localIndex))
          (overlapMap (firstIndex, secondIndex)) (cover.f firstIndex) (pullback.fst _ _) rfl).op
          (localMaps firstIndex)) =
      homPresheaf.map
        ((chartDiagram diagram (overlapMap (firstIndex, secondIndex))).map
          (homOfLE localLe).op).op
        (homPresheaf.map (chartFactor (diagram.obj (op localIndex))
          (overlapMap (firstIndex, secondIndex)) (cover.f secondIndex) (pullback.snd _ _)
          pullback.condition.symm).op (localMaps secondIndex)) at equality
    rw [← homPresheaf.map_comp_apply, ← homPresheaf.map_comp_apply, ← op_comp, ← op_comp,
      chartFactor_naturality, chartFactor_naturality] at equality
    simpa only [op_comp, Functor.map_comp_apply] using equality
  let stageCover := cover.pullback₁ (diagram.obj (op stageIndex)).hom
  have stageSheaf := isSheafFor_presheafHom_ofArrows_openCover sourceModule targetModule
    stageCover (diagram.obj (op stageIndex)).hom
  obtain ⟨stageMap, stageRestrictions, _⟩ :=
    ((Presieve.isSheafFor_arrows_iff homPresheaf _).mp stageSheaf) stageMaps
      (compatible_of_overlap_eq homPresheaf (diagram.obj (op stageIndex)) cover stageMaps
        stageOverlapEqualities)
  change ∀ chartIndex : cover.I₀,
    homPresheaf.map
      (chartProjection (diagram.obj (op stageIndex)) (cover.f chartIndex)).op stageMap =
        stageMaps chartIndex at stageRestrictions
  have stageChartRecovery (chartIndex : cover.I₀) :
      homPresheaf.map ((cones chartIndex).π.app (op stageIndex)).op
          (stageMaps chartIndex) =
        homPresheaf.map (chartProjection cone.pt (cover.f chartIndex)).op
          limitCoefficientMap := by
    change homPresheaf.map ((cones chartIndex).π.app (op stageIndex)).op
        (homPresheaf.map ((diagrams chartIndex).map (homOfLE localLe).op).op
          (localMaps chartIndex)) = _
    rw [← homPresheaf.map_comp_apply, ← op_comp,
      (cones chartIndex).w (homOfLE localLe).op]
    exact chartRecovery chartIndex
  let limitCover := cover.pullback₁ cone.pt.hom
  have limitSheaf := isSheafFor_presheafHom_ofArrows_openCover sourceModule targetModule
    limitCover cone.pt.hom
  have recoveredMap :
      homPresheaf.map (cone.π.app (op stageIndex)).op stageMap = limitCoefficientMap :=
    Presieve.IsSeparatedFor.map_eq_of_commutative_squares homPresheaf
      (fun chartIndex : cover.I₀ ↦ chartProjection cone.pt (cover.f chartIndex))
      (fun chartIndex : cover.I₀ ↦
        chartProjection (diagram.obj (op stageIndex)) (cover.f chartIndex))
      (cone.π.app (op stageIndex))
      (fun chartIndex : cover.I₀ ↦ (cones chartIndex).π.app (op stageIndex))
      (fun chartIndex ↦ chartProjection_naturality cone (cover.f chartIndex) (op stageIndex))
      limitSheaf.isSeparatedFor stageMap limitCoefficientMap stageMaps stageRestrictions
      stageChartRecovery
  refine ⟨stageIndex, initialLeLocal.trans localLe, stageMap, ?_⟩
  refine (Pseudofunctor.presheafHom_map_eq_pullHom
    (F := modulesPseudofunctor) (M := sourceModule) (N := targetModule)
    (cone.π.app (op stageIndex)) stageMap).symm.trans ?_
  change homPresheaf.map (cone.π.app (op stageIndex)).op stageMap = limitCoefficientMap
  exact recoveredMap

end AlgebraicGeometry.Scheme.Modules
