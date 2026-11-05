import Jacobian.CategoryTheory.Limits.Shapes.Pullback.Map
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Checking Cartesian squares on open charts

A commutative square of schemes is Cartesian if its restrictions to an open
cover of the upper-right scheme are Cartesian. A binary-cover form is useful
when gluing finite-presentation models.
-/

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A square of schemes is Cartesian if it is Cartesian on an open cover. -/
lemma isPullback_of_iSup_opensRange_eq_top {sourceScheme targetScheme sourceBase targetBase :
    Scheme.{schemeUniverse}} {comparison : sourceScheme ⟶ targetScheme} {sourceMap : sourceScheme ⟶
    sourceBase}
    {targetMap : targetScheme ⟶ targetBase} {baseMap : sourceBase ⟶ targetBase} (compatible : comparison
      ≫ targetMap = sourceMap ≫ baseMap)
    {Chart : Type*} {targetChart sourceChart : Chart → Scheme.{schemeUniverse}} {targetInclusion : ∀
      chartIndex, targetChart chartIndex ⟶ targetScheme} {sourceInclusion : ∀ chartIndex, sourceChart
      chartIndex ⟶ sourceScheme}
    {chartComparison : ∀ chartIndex, sourceChart chartIndex ⟶ targetChart chartIndex} [∀ chartIndex,
      IsOpenImmersion (targetInclusion chartIndex)]
    (hm : ⨆ chartIndex, (targetInclusion chartIndex).opensRange = ⊤)
    (hchart : ∀ chartIndex, IsPullback (chartComparison chartIndex) (sourceInclusion chartIndex)
      (targetInclusion chartIndex) comparison)
    (cartesian : ∀ chartIndex, IsPullback (chartComparison chartIndex) (sourceInclusion chartIndex ≫
      sourceMap) (targetInclusion chartIndex ≫ targetMap) baseMap) :
    IsPullback comparison sourceMap targetMap baseMap := by
  set pullbackComparison : sourceScheme ⟶ pullback targetMap baseMap := pullback.lift comparison
    sourceMap compatible with hq
  have hq₁ : pullbackComparison ≫ pullback.fst targetMap baseMap = comparison := pullback.lift_fst ..
  have hq₂ : pullbackComparison ≫ pullback.snd targetMap baseMap = sourceMap := pullback.lift_snd ..
  suffices hiso : IsIso pullbackComparison from IsPullback.of_iso_pullback ⟨compatible⟩ (asIso
    pullbackComparison) hq₁ hq₂
  set pullbackChartMap : ∀ chartIndex, pullback (targetInclusion chartIndex ≫ targetMap) baseMap ⟶
    pullback targetMap baseMap := fun chartIndex ↦
    pullback.map (targetInclusion chartIndex ≫ targetMap) baseMap targetMap baseMap (targetInclusion
      chartIndex) (𝟙 sourceBase) (𝟙 targetBase) (by simp) (by simp) with hμdef
  have hμ : ∀ chartIndex, IsPullback (pullback.fst (targetInclusion chartIndex ≫ targetMap) baseMap)
    (pullbackChartMap chartIndex) (targetInclusion chartIndex) (pullback.fst targetMap baseMap) :=
    fun chartIndex ↦ isPullback_pullback_map_left (targetInclusion chartIndex) targetMap baseMap
  have : ∀ chartIndex, IsOpenImmersion (pullbackChartMap chartIndex) := fun chartIndex ↦
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hμ chartIndex) inferInstance

  have key : ∀ chartIndex, IsPullback ((cartesian chartIndex).isoPullback.hom) (sourceInclusion
    chartIndex) (pullbackChartMap chartIndex) pullbackComparison := by
    intro chartIndex
    refine IsPullback.of_right ?_ ?_ (hμ chartIndex)
    · rw [show (cartesian chartIndex).isoPullback.hom ≫ pullback.fst (targetInclusion chartIndex ≫
      targetMap) baseMap = chartComparison chartIndex from
        IsPullback.isoPullback_hom_fst _, hq₁]
      exact hchart chartIndex
    · have h1 : (cartesian chartIndex).isoPullback.hom ≫ pullback.fst (targetInclusion chartIndex ≫
      targetMap) baseMap = chartComparison chartIndex :=
        IsPullback.isoPullback_hom_fst _
      have h2 : (cartesian chartIndex).isoPullback.hom ≫ pullback.snd (targetInclusion chartIndex ≫
        targetMap) baseMap = sourceInclusion chartIndex ≫ sourceMap :=
        IsPullback.isoPullback_hom_snd _
      apply pullback.hom_ext
      · have : pullbackChartMap chartIndex ≫ pullback.fst targetMap baseMap =
            pullback.fst (targetInclusion chartIndex ≫ targetMap) baseMap ≫
              targetInclusion chartIndex := by
          simp only [hμdef, pullback.map, pullback.lift_fst]
        rw [Category.assoc, this, ← Category.assoc, h1, (hchart chartIndex).w, Category.assoc, hq₁]
      · have : pullbackChartMap chartIndex ≫ pullback.snd targetMap baseMap =
            pullback.snd (targetInclusion chartIndex ≫ targetMap) baseMap := by
          simp only [hμdef, pullback.map, pullback.lift_snd, Category.comp_id]
        rw [Category.assoc, this, h2, Category.assoc, hq₂]
  let cover : (pullback targetMap baseMap).OpenCover :=
    Scheme.Cover.mkOfCovers Chart _ pullbackChartMap (fun point ↦ by
      have hx : pullback.fst targetMap baseMap point ∈ (⨆ chartIndex, (targetInclusion
        chartIndex).opensRange) := by rw [hm]; trivial
      obtain ⟨chartIndex, ⟨y, hy⟩⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback (hμ chartIndex) y point hy
      exact ⟨chartIndex, z, hz⟩)
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_openCover cover fun chartIndex ↦ ?_
  rw [MorphismProperty.isomorphisms.iff]
  change IsIso (pullback.snd pullbackComparison (pullbackChartMap chartIndex))
  rw [show pullback.snd pullbackComparison (pullbackChartMap chartIndex) = (key
    chartIndex).flip.isoPullback.inv ≫ (cartesian chartIndex).isoPullback.hom by
    rw [Iso.eq_inv_comp]
    exact IsPullback.isoPullback_hom_snd _]
  infer_instance

/-- **Being a cartesian square is local on the target**, two-chart version. -/
lemma isPullback_of_opensRange_sup_eq_top {sourceScheme targetScheme sourceBase targetBase :
    Scheme.{schemeUniverse}} {comparison : sourceScheme ⟶ targetScheme} {sourceMap : sourceScheme ⟶
    sourceBase}
    {targetMap : targetScheme ⟶ targetBase} {baseMap : sourceBase ⟶ targetBase} (compatible : comparison
      ≫ targetMap = sourceMap ≫ baseMap) {firstTargetChart secondTargetChart firstSourceChart
      secondSourceChart : Scheme.{schemeUniverse}}
    (firstTargetInclusion : firstTargetChart ⟶ targetScheme) (secondTargetInclusion : secondTargetChart ⟶
      targetScheme) [IsOpenImmersion firstTargetInclusion] [IsOpenImmersion secondTargetInclusion]
    {firstSourceInclusion : firstSourceChart ⟶ sourceScheme} {secondSourceInclusion : secondSourceChart ⟶
      sourceScheme} {firstChartComparison : firstSourceChart ⟶ firstTargetChart} {secondChartComparison :
      secondSourceChart ⟶ secondTargetChart}
    (hm : firstTargetInclusion.opensRange ⊔ secondTargetInclusion.opensRange = ⊤)
    (hchart₁ : IsPullback firstChartComparison firstSourceInclusion firstTargetInclusion comparison)
      (hchart₂ : IsPullback secondChartComparison secondSourceInclusion secondTargetInclusion comparison)
    (firstCartesian : IsPullback firstChartComparison (firstSourceInclusion ≫ sourceMap)
      (firstTargetInclusion ≫ targetMap) baseMap) (secondCartesian : IsPullback secondChartComparison
      (secondSourceInclusion ≫ sourceMap) (secondTargetInclusion ≫ targetMap) baseMap) :
    IsPullback comparison sourceMap targetMap baseMap := by
  have : ∀ chartIndex : Bool, IsOpenImmersion (Bool.rec (motive := fun chartIndex ↦ (cond chartIndex
    firstTargetChart secondTargetChart) ⟶ targetScheme) secondTargetInclusion firstTargetInclusion
    chartIndex) :=
    fun chartIndex ↦ by cases chartIndex <;> assumption
  refine isPullback_of_iSup_opensRange_eq_top compatible (Chart := Bool) (targetChart := fun chartIndex ↦
    cond
    chartIndex firstTargetChart secondTargetChart)
    (sourceChart := fun chartIndex ↦ cond chartIndex firstSourceChart secondSourceChart)
    (targetInclusion := fun chartIndex ↦ Bool.rec (motive := fun chartIndex ↦ (cond chartIndex
      firstTargetChart
      secondTargetChart) ⟶ targetScheme) secondTargetInclusion firstTargetInclusion chartIndex)
    (sourceInclusion := fun chartIndex ↦ Bool.rec (motive := fun chartIndex ↦ (cond chartIndex
      firstSourceChart
      secondSourceChart) ⟶ sourceScheme) secondSourceInclusion firstSourceInclusion chartIndex)
    (chartComparison := fun chartIndex ↦ Bool.rec (motive := fun chartIndex ↦ (cond chartIndex
      firstSourceChart
      secondSourceChart) ⟶ (cond chartIndex firstTargetChart secondTargetChart)) secondChartComparison
      firstChartComparison chartIndex)
    ?_ ?_ ?_
  · rw [iSup_bool_eq]
    exact hm
  · intro chartIndex; cases chartIndex
    · exact hchart₂
    · exact hchart₁
  · intro chartIndex; cases chartIndex
    · exact secondCartesian
    · exact firstCartesian


end AlgebraicGeometry
