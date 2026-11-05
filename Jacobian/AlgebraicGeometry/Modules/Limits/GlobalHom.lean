import Jacobian.AlgebraicGeometry.Modules.Limits.FiniteMaps
import Jacobian.AlgebraicGeometry.Modules.ZariskiDescent
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Coefficient morphisms on finite affine covers of inverse limits

Equality of coefficient morphisms is detected at a stage of a directed inverse
system of affine morphisms. A finite affine cover reduces this to affine limits;
the cover and its limiting charts are obtained by actual scheme pullback.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

private lemma pullback_map_eq_iff_of_comp
    {source middle target : Scheme.{schemeUniverse}}
    (firstMap : source ⟶ middle) (secondMap : middle ⟶ target)
    (composite : source ⟶ target) (factorization : firstMap ≫ secondMap = composite)
    {sourceModule targetModule : target.Modules}
    (firstCoefficientMap secondCoefficientMap : sourceModule ⟶ targetModule) :
    (pullback firstMap).map ((pullback secondMap).map firstCoefficientMap) =
        (pullback firstMap).map ((pullback secondMap).map secondCoefficientMap) ↔
      (pullback composite).map firstCoefficientMap =
        (pullback composite).map secondCoefficientMap := by
  let comparison : pullback composite ≅ pullback secondMap ⋙ pullback firstMap :=
    (pullbackCongr factorization.symm) ≪≫ (pullbackComp firstMap secondMap).symm
  constructor
  · intro equality
    apply (cancel_mono (comparison.hom.app targetModule)).mp
    rw [comparison.hom.naturality, comparison.hom.naturality]
    exact congrArg (fun coefficientMap ↦ comparison.hom.app sourceModule ≫ coefficientMap)
      equality
  · intro equality
    apply (cancel_epi (comparison.hom.app sourceModule)).mp
    have firstNaturality := comparison.hom.naturality firstCoefficientMap
    have secondNaturality := comparison.hom.naturality secondCoefficientMap
    simp only [Functor.comp_map] at firstNaturality secondNaturality
    exact firstNaturality.symm.trans
      ((congrArg (fun coefficientMap ↦ coefficientMap ≫ comparison.hom.app targetModule)
        equality).trans secondNaturality)

private def affineCoverDiagram
    {Index : Type schemeUniverse} [Preorder Index] {scheme : Scheme.{schemeUniverse}}
    (diagram : Indexᵒᵖ ⥤ Over scheme) {chart : Scheme.{schemeUniverse}}
    (chartMap : chart ⟶ scheme) : Indexᵒᵖ ⥤ Scheme.{schemeUniverse} :=
  diagram ⋙ Over.pullback chartMap ⋙ Over.forget chart

private def affineCoverCone
    {Index : Type schemeUniverse} [Preorder Index] {scheme : Scheme.{schemeUniverse}}
    {diagram : Indexᵒᵖ ⥤ Over scheme} (cone : Cone diagram)
    {chart : Scheme.{schemeUniverse}} (chartMap : chart ⟶ scheme) :
    Cone (affineCoverDiagram diagram chartMap) :=
  (Over.forget chart).mapCone ((Over.pullback chartMap).mapCone cone)

private def isLimit_affineCoverCone
    {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] {scheme : Scheme.{schemeUniverse}}
    {diagram : Indexᵒᵖ ⥤ Over scheme} (cone : Cone diagram)
    (limit : IsLimit ((Over.forget scheme).mapCone cone))
    {chart : Scheme.{schemeUniverse}} (chartMap : chart ⟶ scheme) :
    IsLimit (affineCoverCone cone chartMap) := by
  letI : IsConnected Indexᵒᵖ := IsCofiltered.isConnected _
  have overLimit : IsLimit cone := isLimitOfReflects (Over.forget scheme) limit
  exact isLimitOfPreserves (Over.forget chart)
    (isLimitOfPreserves (Over.pullback chartMap) overLimit)

/-- Equality after an affine inverse limit is detected at a later stage over a scheme with
a finite affine cover. Only the source coefficient is finitely presented; the target need
only be quasi-coherent. No affine-overlap or Noetherian hypothesis is needed for equality. -/
theorem exists_hom_eq_of_finite_affine_cover_limit
    {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] {scheme : Scheme.{schemeUniverse}}
    (cover : scheme.OpenCover.{schemeUniverse}) [Finite cover.I₀]
    [∀ chartIndex, IsAffine (cover.X chartIndex)]
    (diagram : Indexᵒᵖ ⥤ Over scheme)
    [∀ stageIndex, IsAffineHom (diagram.obj stageIndex).hom]
    (cone : Cone diagram) (limit : IsLimit ((Over.forget scheme).mapCone cone))
    [IsAffineHom cone.pt.hom] (initialIndex : Index)
    {sourceModule targetModule : scheme.Modules}
    [sourceModule.IsFinitePresentation] [sourceModule.IsQuasicoherent]
    [targetModule.IsQuasicoherent]
    (firstMap secondMap : sourceModule ⟶ targetModule)
    (limitEquality : (pullback cone.pt.hom).map firstMap =
      (pullback cone.pt.hom).map secondMap) :
    ∃ (stageIndex : Index) (_ : initialIndex ≤ stageIndex),
      (pullback (diagram.obj (op stageIndex)).hom).map firstMap =
        (pullback (diagram.obj (op stageIndex)).hom).map secondMap := by
  classical
  let diagrams (chartIndex : cover.I₀) := affineCoverDiagram diagram (cover.f chartIndex)
  let cones (chartIndex : cover.I₀) := affineCoverCone cone (cover.f chartIndex)
  letI (chartIndex : cover.I₀) (stageIndex : Indexᵒᵖ) :
      IsAffine ((diagrams chartIndex).obj stageIndex) := by
    change IsAffine (Limits.pullback (diagram.obj stageIndex).hom (cover.f chartIndex))
    infer_instance
  letI (chartIndex : cover.I₀) : IsAffine (cones chartIndex).pt := by
    change IsAffine (Limits.pullback cone.pt.hom (cover.f chartIndex))
    infer_instance
  let initialProjection (chartIndex : cover.I₀) :
      (diagrams chartIndex).obj (op initialIndex) ⟶ scheme :=
    ((diagram ⋙ Over.pullback (cover.f chartIndex)).obj (op initialIndex)).hom ≫
      cover.f chartIndex
  let limitProjection (chartIndex : cover.I₀) : (cones chartIndex).pt ⟶ scheme :=
    ((Over.pullback (cover.f chartIndex)).obj cone.pt).hom ≫ cover.f chartIndex
  let sourceModules (chartIndex : cover.I₀) :=
    (pullback (initialProjection chartIndex)).obj sourceModule
  let targetModules (chartIndex : cover.I₀) :=
    (pullback (initialProjection chartIndex)).obj targetModule
  letI (chartIndex : cover.I₀) : (sourceModules chartIndex).IsFinitePresentation := by
    dsimp only [sourceModules]
    infer_instance
  letI (chartIndex : cover.I₀) : (sourceModules chartIndex).IsQuasicoherent := by
    dsimp only [sourceModules]
    infer_instance
  letI (chartIndex : cover.I₀) : (targetModules chartIndex).IsQuasicoherent := by
    dsimp only [targetModules]
    infer_instance
  have projectionCompatibility (chartIndex : cover.I₀) :
      (cones chartIndex).π.app (op initialIndex) ≫ initialProjection chartIndex =
        limitProjection chartIndex := by
    change ((Over.pullback (cover.f chartIndex)).map (cone.π.app (op initialIndex))).left ≫
        (((Over.pullback (cover.f chartIndex)).obj (diagram.obj (op initialIndex))).hom ≫
          cover.f chartIndex) =
      ((Over.pullback (cover.f chartIndex)).obj cone.pt).hom ≫ cover.f chartIndex
    simpa only [Functor.const_obj_obj, Category.assoc] using
      congrArg (fun projection ↦ projection ≫ cover.f chartIndex)
        (((Over.pullback (cover.f chartIndex)).map (cone.π.app (op initialIndex))).w)
  have localEqualities (chartIndex : cover.I₀) :
      (pullback ((cones chartIndex).π.app (op initialIndex))).map
          ((pullback (initialProjection chartIndex)).map firstMap) =
        (pullback ((cones chartIndex).π.app (op initialIndex))).map
          ((pullback (initialProjection chartIndex)).map secondMap) := by
    apply (pullback_map_eq_iff_of_comp _ _ _ (projectionCompatibility chartIndex)
      firstMap secondMap).mpr
    apply (pullback_map_eq_iff_of_comp
      (Limits.pullback.fst cone.pt.hom (cover.f chartIndex)) cone.pt.hom
      (limitProjection chartIndex)
      (Limits.pullback.condition (f := cone.pt.hom) (g := cover.f chartIndex))
      firstMap secondMap).mp
    exact congrArg (pullback (Limits.pullback.fst cone.pt.hom (cover.f chartIndex))).map
      limitEquality
  obtain ⟨stageIndex, initialLe, localStageEqualities⟩ :=
    exists_hom_eqs_of_affine_limits diagrams cones
      (fun chartIndex ↦ isLimit_affineCoverCone cone limit (cover.f chartIndex))
      initialIndex sourceModules targetModules
      (fun chartIndex ↦ (pullback (initialProjection chartIndex)).map firstMap)
      (fun chartIndex ↦ (pullback (initialProjection chartIndex)).map secondMap)
      localEqualities
  refine ⟨stageIndex, initialLe, ?_⟩
  let stageProjection := (diagram.obj (op stageIndex)).hom
  let stageCover : (diagram.obj (op stageIndex)).left.OpenCover.{schemeUniverse} :=
    cover.pullback₁ stageProjection
  apply (bijective_toDescentData_map_of_isOpenImmersion stageCover.f
    (Scheme.OpenCover.iSup_opensRange stageCover) _ _).1
  apply Pseudofunctor.DescentData.hom_ext
  intro chartIndex
  change (pullback (Limits.pullback.fst stageProjection (cover.f chartIndex))).map
      ((pullback stageProjection).map firstMap) =
    (pullback (Limits.pullback.fst stageProjection (cover.f chartIndex))).map
      ((pullback stageProjection).map secondMap)
  let stageChartProjection : (diagrams chartIndex).obj (op stageIndex) ⟶ scheme :=
    ((diagram ⋙ Over.pullback (cover.f chartIndex)).obj (op stageIndex)).hom ≫
      cover.f chartIndex
  apply (pullback_map_eq_iff_of_comp _ _ stageChartProjection
    (Limits.pullback.condition (f := stageProjection) (g := cover.f chartIndex))
    firstMap secondMap).mpr
  have stageCompatibility :
      (diagrams chartIndex).map (homOfLE initialLe).op ≫ initialProjection chartIndex =
        stageChartProjection := by
    change ((Over.pullback (cover.f chartIndex)).map
        (diagram.map (homOfLE initialLe).op)).left ≫
          (((Over.pullback (cover.f chartIndex)).obj (diagram.obj (op initialIndex))).hom ≫
            cover.f chartIndex) =
      ((Over.pullback (cover.f chartIndex)).obj (diagram.obj (op stageIndex))).hom ≫
        cover.f chartIndex
    simpa only [Category.assoc] using
      congrArg (fun projection ↦ projection ≫ cover.f chartIndex)
        (((Over.pullback (cover.f chartIndex)).map
          (diagram.map (homOfLE initialLe).op)).w)
  exact (pullback_map_eq_iff_of_comp _ _ _ stageCompatibility firstMap secondMap).mp
    (localStageEqualities chartIndex)

end AlgebraicGeometry.Scheme.Modules
