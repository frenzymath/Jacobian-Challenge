import Jacobian.AlgebraicGeometry.Modules.Limits.Charts
import Jacobian.AlgebraicGeometry.Modules.PullbackUnit

/-!
# Simultaneous descent of finitely presented coefficients on affine charts

A finite family of finitely presented module sheaves on affine charts after a
directed base change descends to one common stage. The coefficients are constructed
from the given limit sheaves, rather than supplied as additional models.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Finitely many affine-chart coefficients descend simultaneously to a common base stage.
No finite-presentation hypothesis on the chart morphisms is needed. -/
theorem exists_finitePresentation_models_on_affine_pullbacks
    {Index : Type schemeUniverse} [Preorder Index] [IsDirected Index (· ≤ ·)]
    (diagram : Index ⥤ CommRingCat.{schemeUniverse})
    (cone : Cone (diagram.op ⋙ Scheme.Spec)) (limit : IsLimit cone) [IsAffine cone.pt]
    (initialIndex : Index) {Chart : Type schemeUniverse} [Finite Chart]
    (charts : Chart → Scheme.{schemeUniverse}) [∀ chartIndex, IsAffine (charts chartIndex)]
    (chartMaps : ∀ chartIndex, charts chartIndex ⟶ Spec (diagram.obj initialIndex))
    (coefficients : ∀ chartIndex,
      (Limits.pullback (cone.π.app (op initialIndex)) (chartMaps chartIndex)).Modules)
    [∀ chartIndex, (coefficients chartIndex).IsFinitePresentation] :
    ∃ (stageIndex : Index) (initialLe : initialIndex ≤ stageIndex),
      let parameterMap : Over.mk (cone.π.app (op initialIndex)) ⟶
          Over.mk (Spec.map (diagram.map (homOfLE initialLe))) :=
        Over.homMk (cone.π.app (op stageIndex)) (cone.w (homOfLE initialLe).op)
      ∃ stageCoefficients : ∀ chartIndex,
          (Limits.pullback (Spec.map (diagram.map (homOfLE initialLe)))
            (chartMaps chartIndex)).Modules,
        (∀ chartIndex, (stageCoefficients chartIndex).IsFinitePresentation) ∧
        (∀ chartIndex, Nonempty
          ((pullback (((Over.pullback (chartMaps chartIndex)).map parameterMap).left)).obj
            (stageCoefficients chartIndex) ≅ coefficients chartIndex)) := by
  classical
  letI : Fintype Chart := Fintype.ofFinite Chart
  letI : Nonempty Index := ⟨initialIndex⟩
  have chartModels (chartIndex : Chart) :=
    exists_finitePresentation_model_on_affine_pullback diagram cone limit initialIndex
      (chartMaps chartIndex) (coefficients chartIndex)
  choose chartStage initialLeChart chartCoefficient finiteChartCoefficient chartComparison
    using chartModels
  obtain ⟨stageIndex, stageBound⟩ :=
    (insert initialIndex (Finset.univ.image chartStage)).exists_le
  have initialLe : initialIndex ≤ stageIndex :=
    stageBound initialIndex (Finset.mem_insert_self _ _)
  have chartLe (chartIndex : Chart) : chartStage chartIndex ≤ stageIndex :=
    stageBound (chartStage chartIndex)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨chartIndex, Finset.mem_univ chartIndex, rfl⟩))
  refine ⟨stageIndex, initialLe, ?_⟩
  dsimp only
  let parameterMap : Over.mk (cone.π.app (op initialIndex)) ⟶
      Over.mk (Spec.map (diagram.map (homOfLE initialLe))) :=
    Over.homMk (cone.π.app (op stageIndex)) (cone.w (homOfLE initialLe).op)
  let chartTransition (chartIndex : Chart) :
      Over.mk (Spec.map (diagram.map (homOfLE initialLe))) ⟶
        Over.mk (Spec.map (diagram.map (homOfLE (initialLeChart chartIndex)))) :=
    Over.homMk (Spec.map (diagram.map (homOfLE (chartLe chartIndex)))) (by
      change Spec.map (diagram.map (homOfLE (chartLe chartIndex))) ≫
          Spec.map (diagram.map (homOfLE (initialLeChart chartIndex))) =
        Spec.map (diagram.map (homOfLE initialLe))
      rw [← Spec.map_comp, ← diagram.map_comp]
      rfl)
  let limitParameterMap (chartIndex : Chart) :
      Over.mk (cone.π.app (op initialIndex)) ⟶
        Over.mk (Spec.map (diagram.map (homOfLE (initialLeChart chartIndex)))) :=
    Over.homMk (cone.π.app (op (chartStage chartIndex)))
      (cone.w (homOfLE (initialLeChart chartIndex)).op)
  have parameterCompatibility (chartIndex : Chart) :
      parameterMap ≫ chartTransition chartIndex = limitParameterMap chartIndex := by
    ext
    exact cone.w (homOfLE (chartLe chartIndex)).op
  let chartTransitionMap (chartIndex : Chart) :=
    ((Over.pullback (chartMaps chartIndex)).map (chartTransition chartIndex)).left
  let stageCoefficients (chartIndex : Chart) :=
    (pullback (chartTransitionMap chartIndex)).obj (chartCoefficient chartIndex)
  refine ⟨stageCoefficients, fun chartIndex ↦ ?_, fun chartIndex ↦ ?_⟩
  · letI : (chartCoefficient chartIndex).IsFinitePresentation :=
      finiteChartCoefficient chartIndex
    exact inferInstanceAs
      (((pullback (chartTransitionMap chartIndex)).obj
        (chartCoefficient chartIndex)).IsFinitePresentation)
  · have chartCompatibility :
        ((Over.pullback (chartMaps chartIndex)).map parameterMap).left ≫
            chartTransitionMap chartIndex =
          ((Over.pullback (chartMaps chartIndex)).map
            (limitParameterMap chartIndex)).left := by
      change ((Over.pullback (chartMaps chartIndex)).map parameterMap).left ≫
        ((Over.pullback (chartMaps chartIndex)).map (chartTransition chartIndex)).left = _
      rw [← Over.comp_left, ← Functor.map_comp, parameterCompatibility]
    exact ⟨pullbackCompOfEq
      (((Over.pullback (chartMaps chartIndex)).map parameterMap).left)
      (chartTransitionMap chartIndex)
      (((Over.pullback (chartMaps chartIndex)).map
        (limitParameterMap chartIndex)).left)
      chartCompatibility (chartCoefficient chartIndex) ≪≫
        (chartComparison chartIndex).some⟩

end AlgebraicGeometry.Scheme.Modules
