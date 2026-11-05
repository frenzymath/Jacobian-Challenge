import Jacobian.AlgebraicGeometry.Gluing.Pushout
import Jacobian.AlgebraicGeometry.Limits.FinitePresentation
import Jacobian.AlgebraicGeometry.Limits.Isomorphism
import Jacobian.AlgebraicGeometry.Pullback.Local

/-!
# Descent of finitely presented schemes to a finite stage

A finitely presented scheme over a cofiltered limit of quasi-compact,
quasi-separated schemes with affine transition maps comes from an actual
finite-stage scheme. The proof descends affine charts, descends their
quasi-compact intersections, and glues the resulting models after making
the intersection identifications agree at a later stage.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

private lemma isCompact_finset_sup {sourceScheme : Scheme.{schemeUniverse}} (opens : Finset
    sourceScheme.Opens)
    (hs : ∀ openSubset ∈ opens, IsCompact (openSubset : Set sourceScheme)) : IsCompact ((opens.sup id :
      sourceScheme.Opens) : Set sourceScheme) := by
  classical
  induction opens using Finset.induction with
  | empty => simp
  | insert addedOpen opens not_mem inductionHypothesis =>
      rw [Finset.sup_insert]
      refine IsCompact.union (hs addedOpen (Finset.mem_insert_self addedOpen opens)) ?_
      exact inductionHypothesis fun openSubset hV ↦ hs openSubset (Finset.mem_insert_of_mem hV)

private lemma isBasis_affineOpens_le_preimage {sourceScheme targetScheme : Scheme.{schemeUniverse}}
    (morphism : sourceScheme ⟶ targetScheme) :
    TopologicalSpace.Opens.IsBasis {openSubset : sourceScheme.Opens | IsAffineOpen openSubset ∧
      ∃ targetOpen : targetScheme.Opens, IsAffineOpen targetOpen ∧ openSubset ≤ morphism ⁻¹ᵁ targetOpen}
        := by
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {neighborhood point} hxU ↦ ?_
  obtain ⟨targetOpen, hV, hxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    targetScheme.isBasis_affineOpens
    (U := ⊤) (x := morphism.base point) trivial
  obtain ⟨openSubset, hW, hxW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    sourceScheme.isBasis_affineOpens
    (U := neighborhood ⊓ morphism ⁻¹ᵁ targetOpen) ⟨hxU, hxV⟩
  exact ⟨openSubset, ⟨hW, targetOpen, hV, hWU.trans inf_le_right⟩, hxW, hWU.trans inf_le_left⟩

variable {Index : Type schemeUniverse} [Category.{schemeUniverse} Index]
  {diagram : Index ⥤ Scheme.{schemeUniverse}} {cone : Cone diagram} (limit : IsLimit cone)
  [IsCofiltered Index]
  [∀ {sourceIndex targetIndex : Index} (transition : sourceIndex ⟶ targetIndex),
    IsAffineHom (diagram.map transition)]

variable (diagram cone) in
/-- The comparison morphism to the base change of a finite-stage model. -/
private noncomputable def modelBaseChangeLift {stageIndex laterIndex : Index} (transition : laterIndex ⟶
    stageIndex) {sourceScheme stageScheme : Scheme.{schemeUniverse}} {sourceMap : sourceScheme ⟶ cone.pt}
    {stageMap : stageScheme ⟶ diagram.obj stageIndex} {comparison : sourceScheme ⟶ stageScheme}
      (modelData : IsPullback comparison sourceMap stageMap (cone.π.app stageIndex)) :
    sourceScheme ⟶ pullback stageMap (diagram.map transition) :=
  pullback.lift comparison (sourceMap ≫ cone.π.app laterIndex) (by rw [modelData.w, ← cone.w transition,
    Category.assoc])

@[reassoc (attr := simp)]
private lemma modelBaseChangeLift_fst {stageIndex laterIndex : Index} (transition : laterIndex ⟶
    stageIndex) {sourceScheme stageScheme : Scheme.{schemeUniverse}} {sourceMap : sourceScheme ⟶ cone.pt}
    {stageMap : stageScheme ⟶ diagram.obj stageIndex} {comparison : sourceScheme ⟶ stageScheme}
      (modelData : IsPullback comparison sourceMap stageMap (cone.π.app stageIndex)) :
    modelBaseChangeLift diagram cone transition modelData ≫ pullback.fst stageMap (diagram.map
      transition) = comparison := pullback.lift_fst ..

@[reassoc (attr := simp)]
private lemma modelBaseChangeLift_snd {stageIndex laterIndex : Index} (transition : laterIndex ⟶
    stageIndex) {sourceScheme stageScheme : Scheme.{schemeUniverse}} {sourceMap : sourceScheme ⟶ cone.pt}
    {stageMap : stageScheme ⟶ diagram.obj stageIndex} {comparison : sourceScheme ⟶ stageScheme}
      (modelData : IsPullback comparison sourceMap stageMap (cone.π.app stageIndex)) :
    modelBaseChangeLift diagram cone transition modelData ≫ pullback.snd stageMap (diagram.map
      transition) = sourceMap ≫ cone.π.app laterIndex := pullback.lift_snd ..

private lemma isPullback_modelBaseChangeLift {stageIndex laterIndex : Index} (transition : laterIndex ⟶
    stageIndex) {sourceScheme stageScheme : Scheme.{schemeUniverse}} {sourceMap : sourceScheme ⟶ cone.pt}
    {stageMap : stageScheme ⟶ diagram.obj stageIndex} {comparison : sourceScheme ⟶ stageScheme}
      (modelData : IsPullback comparison sourceMap stageMap (cone.π.app stageIndex)) :
    IsPullback (modelBaseChangeLift diagram cone transition modelData) sourceMap (pullback.snd stageMap
      (diagram.map transition)) (cone.π.app laterIndex) := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback stageMap (diagram.map transition))
  rw [modelBaseChangeLift_fst, cone.w transition]
  exact modelData


variable (diagram cone) in
/-- The property that `sourceMap : sourceScheme ⟶ lim Dⱼ` is the base change along
`lim Dⱼ ⟶ D_k` of a scheme of finite presentation over the stage `D_k`. -/
private def HasModelAt (stageIndex : Index) {sourceScheme : Scheme.{schemeUniverse}} (sourceMap :
    sourceScheme ⟶ cone.pt) : Prop :=
  ∃ (stageScheme : Scheme.{schemeUniverse}) (stageMap : stageScheme ⟶ diagram.obj stageIndex) (comparison
    : sourceScheme ⟶ stageScheme), LocallyOfFinitePresentation stageMap ∧
    CompactSpace stageScheme ∧ QuasiSeparatedSpace stageScheme ∧ IsPullback comparison sourceMap stageMap
      (cone.π.app stageIndex)

variable (diagram cone) in
/-- Refinement of the finite-stage model data remembering a descent of a
quasi-compact open `chosenOpen ⊆ sourceScheme` to a quasi-compact open of the finite-stage model.
  -/
private def HasModelWithOpenAt (stageIndex : Index) {sourceScheme : Scheme.{schemeUniverse}} (sourceMap :
    sourceScheme ⟶ cone.pt) (chosenOpen : sourceScheme.Opens) : Prop :=
  ∃ (stageScheme : Scheme.{schemeUniverse}) (stageMap : stageScheme ⟶ diagram.obj stageIndex) (comparison
    : sourceScheme ⟶ stageScheme) (stageOpen : stageScheme.Opens),
    LocallyOfFinitePresentation stageMap ∧ CompactSpace stageScheme ∧ QuasiSeparatedSpace stageScheme ∧
      IsPullback comparison sourceMap stageMap (cone.π.app stageIndex) ∧ IsCompact (stageOpen : Set
        stageScheme) ∧ comparison ⁻¹ᵁ stageOpen = chosenOpen

variable (diagram cone) in
/-- The property that `sourceMap : sourceScheme ⟶ lim Dⱼ` is the base change of a scheme of
finite presentation over one of the stages. -/
private def HasFiniteStageModel {sourceScheme : Scheme.{schemeUniverse}} (sourceMap : sourceScheme ⟶
    cone.pt) : Prop := ∃ stageIndex, HasModelAt diagram cone stageIndex sourceMap

private lemma HasModelWithOpenAt.mono {stageIndex laterIndex : Index} (transition : laterIndex ⟶
    stageIndex) {sourceScheme : Scheme.{schemeUniverse}} {sourceMap : sourceScheme ⟶ cone.pt}
    {chosenOpen : sourceScheme.Opens} (modelData : HasModelWithOpenAt diagram cone stageIndex sourceMap
      chosenOpen) : HasModelWithOpenAt diagram cone laterIndex sourceMap chosenOpen := by
  obtain ⟨stageScheme, stageMap, comparison, stageOpen, hp, hcpt, hqs, hsq, hOc, hO⟩ := modelData
  have := hp; have := hcpt; have := hqs
  have : QuasiCompact (pullback.fst stageMap (diagram.map transition)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  refine ⟨pullback stageMap (diagram.map transition), pullback.snd _ _, modelBaseChangeLift diagram cone
    transition hsq,
    pullback.fst stageMap (diagram.map transition) ⁻¹ᵁ stageOpen, inferInstance, inferInstance,
      inferInstance,
    isPullback_modelBaseChangeLift transition hsq,
    QuasiCompact.isCompact_preimage _ stageOpen.isOpen hOc, ?_⟩
  rw [← Scheme.Hom.comp_preimage, modelBaseChangeLift_fst, hO]

include limit in
/-- A quasi-compact open of a scheme over the limit descends to a
finite stage. -/
private lemma exists_modelWithOpenAt {stageIndex : Index} {sourceScheme : Scheme.{schemeUniverse}}
    {sourceMap : sourceScheme ⟶ cone.pt}
    (modelData : HasModelAt diagram cone stageIndex sourceMap) (chosenOpen : sourceScheme.Opens) (hW :
      IsCompact (chosenOpen : Set sourceScheme)) :
    ∃ laterIndex : Index, HasModelWithOpenAt diagram cone laterIndex sourceMap chosenOpen := by
  obtain ⟨stageScheme, stageMap, comparison, hp, hcpt, hqs, hsq⟩ := modelData
  have := hp; have := hcpt; have := hqs
  have hlim : IsLimit ((baseChangeCone diagram cone stageMap).extend hsq.isoPullback.hom) :=
    (isLimitBaseChangeCone diagram cone stageMap limit).ofIsoLimit
      (Cone.ext hsq.isoPullback.symm (fun overIndex ↦ by simp))
  obtain ⟨overIndex, stageOpen, hOc, hO⟩ := exists_preimage_eq (baseChangeDiagram diagram stageMap) _
    hlim chosenOpen hW
  refine ⟨overIndex.left, pullback stageMap (diagram.map overIndex.hom), pullback.snd _ _,
    modelBaseChangeLift diagram cone overIndex.hom hsq, stageOpen,
    inferInstance, inferInstance, inferInstance, isPullback_modelBaseChangeLift overIndex.hom hsq, hOc,
      ?_⟩
  have hmap : modelBaseChangeLift diagram cone overIndex.hom hsq =
      ((baseChangeCone diagram cone stageMap).extend hsq.isoPullback.hom).π.app overIndex := by
    apply pullback.hom_ext <;>
      simp [Cone.extend, IsPullback.isoPullback_hom_fst]
  rw [← hO, hmap]

include limit in
/-- **An affine scheme of finite presentation over the limit that lies over an
affine open of one of the stages descends to a finite stage.**

The system is base changed to the affine open `secondOpen ⊆ Dᵢ₀`: the base changed system has affine
stages, so the affine case
`AlgebraicGeometry.Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine`
applies to it. -/
private lemma HasFiniteStageModel.of_isAffine {baseStage : Index} {sourceScheme :
    Scheme.{schemeUniverse}} [IsAffine sourceScheme] (sourceMap : sourceScheme ⟶ cone.pt)
    [LocallyOfFinitePresentation sourceMap] {secondOpen : (diagram.obj baseStage).Opens} (hV :
      IsAffineOpen secondOpen)
    (openLift : sourceScheme ⟶ secondOpen.toScheme) (hq : openLift ≫ secondOpen.ι = sourceMap ≫
      cone.π.app baseStage) : HasFiniteStageModel diagram cone sourceMap := by
  have : IsAffine secondOpen.toScheme := hV
  have : ∀ overIndex : Over baseStage, IsAffine ((baseChangeDiagram diagram secondOpen.ι).obj overIndex)
    := fun overIndex ↦
    inferInstanceAs (IsAffine (pullback secondOpen.ι (diagram.map overIndex.hom)))
  have hsnd : pullback.lift openLift sourceMap hq ≫ pullback.snd secondOpen.ι (cone.π.app baseStage) =
    sourceMap := pullback.lift_snd ..
  have hmono : MorphismProperty.monomorphisms Scheme.{schemeUniverse} (pullback.snd secondOpen.ι
    (cone.π.app baseStage)) :=
    inferInstanceAs (Mono _)
  have hcomp : LocallyOfFinitePresentation
      (pullback.lift openLift sourceMap hq ≫ pullback.snd secondOpen.ι (cone.π.app baseStage)) := by
    rw [hsnd]
    exact ‹LocallyOfFinitePresentation sourceMap›
  have : @LocallyOfFinitePresentation sourceScheme (baseChangeCone diagram cone secondOpen.ι).pt
    (pullback.lift openLift sourceMap hq) :=
    MorphismProperty.of_postcomp (W := @LocallyOfFinitePresentation)
      (W' := MorphismProperty.monomorphisms Scheme.{schemeUniverse}) _ (pullback.snd secondOpen.ι
        (cone.π.app baseStage))
      hmono hcomp
  obtain ⟨overIndex, stageScheme, hYaff, stageMap, hp, comparison, hsq⟩ :=
    Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine
      (baseChangeDiagram diagram secondOpen.ι) (baseChangeCone diagram cone secondOpen.ι)
      (isLimitBaseChangeCone diagram cone secondOpen.ι limit) (pullback.lift openLift sourceMap hq)
  have := hYaff
  have := hp
  have : IsOpenImmersion ((baseChangeDiagramπ diagram secondOpen.ι).app overIndex) :=
    inferInstanceAs (IsOpenImmersion (pullback.snd secondOpen.ι (diagram.map overIndex.hom)))
  have hP : LocallyOfFinitePresentation (stageMap ≫ (baseChangeDiagramπ diagram secondOpen.ι).app
    overIndex) := inferInstance
  refine ⟨overIndex.left, stageScheme, stageMap ≫ (baseChangeDiagramπ diagram secondOpen.ι).app
    overIndex, comparison, hP, inferInstance,
    inferInstance, ?_⟩
  rw [← hsnd]
  exact hsq.paste_vert (isPullback_baseChangeCone_π diagram cone secondOpen.ι overIndex)

include limit in
/-- An affine open of a scheme over the limit that lies over an affine open of
one of the stages descends to a finite stage. -/
private lemma HasFiniteStageModel.of_isAffineOpen {baseStage : Index} {sourceScheme :
    Scheme.{schemeUniverse}} (sourceMap : sourceScheme ⟶ cone.pt)
    [LocallyOfFinitePresentation sourceMap] {chosenOpen : sourceScheme.Opens} (hW : IsAffineOpen
      chosenOpen)
    {secondOpen : (diagram.obj baseStage).Opens} (hV : IsAffineOpen secondOpen) (hle : chosenOpen ≤
      (sourceMap ≫ cone.π.app baseStage) ⁻¹ᵁ secondOpen) :
    HasFiniteStageModel diagram cone (chosenOpen.ι ≫ sourceMap) := by
  have : IsAffine chosenOpen.toScheme := hW
  refine HasFiniteStageModel.of_isAffine limit _ hV ((sourceMap ≫ cone.π.app baseStage).resLE secondOpen
    chosenOpen hle) ?_
  rw [Scheme.Hom.resLE_comp_ι, Category.assoc]

private lemma HasFiniteStageModel.comp_iso {sourceScheme isomorphicSource : Scheme.{schemeUniverse}}
    (modelIso : isomorphicSource ≅ sourceScheme) {sourceMap : sourceScheme ⟶ cone.pt}
    (modelData : HasFiniteStageModel diagram cone sourceMap) : HasFiniteStageModel diagram cone
      (modelIso.hom ≫ sourceMap) := by
  obtain ⟨stageIndex, stageScheme, stageMap, comparison, hp, hcpt, hqs, hsq⟩ := modelData
  refine ⟨stageIndex, stageScheme, stageMap, modelIso.hom ≫ comparison, hp, hcpt, hqs, ?_⟩
  have hiso : IsPullback modelIso.hom (modelIso.hom ≫ sourceMap) sourceMap (𝟙 cone.pt) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa using hiso.paste_horiz hsq


include limit in
/-- **The two-open gluing step**: if a scheme over the limit is covered by
two opens with quasi-compact intersection, each of which descends to a finite stage, then it
descends to a finite stage. -/
private lemma HasFiniteStageModel.of_sup_eq_top {ambientScheme : Scheme.{schemeUniverse}} (ambientMap :
    ambientScheme ⟶ cone.pt) (firstOpen secondOpen : ambientScheme.Opens)
    (hUV : firstOpen ⊔ secondOpen = ⊤) (hWc : IsCompact ((firstOpen ⊓ secondOpen : ambientScheme.Opens) :
      Set ambientScheme))
    (hU : HasFiniteStageModel diagram cone (firstOpen.ι ≫ ambientMap)) (hV : HasFiniteStageModel diagram
      cone (secondOpen.ι ≫ ambientMap)) :
    HasFiniteStageModel diagram cone ambientMap := by
  obtain ⟨firstStage, hU⟩ := hU
  obtain ⟨secondStage, hV⟩ := hV

  have hWU : IsCompact ((firstOpen.ι ⁻¹ᵁ secondOpen : firstOpen.toScheme.Opens) : Set firstOpen.toScheme)
    := by
    have he : (firstOpen.ι ⁻¹ᵁ secondOpen : firstOpen.toScheme.Opens) = firstOpen.ι ⁻¹ᵁ (firstOpen ⊓
      secondOpen) := by
      rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]
    rw [he]
    refine firstOpen.ι.isOpenEmbedding.isInducing.isCompact_preimage' hWc ?_
    rw [Scheme.Opens.range_ι]
    exact inf_le_left
  have hWV : IsCompact ((secondOpen.ι ⁻¹ᵁ firstOpen : secondOpen.toScheme.Opens) : Set
    secondOpen.toScheme) := by
    have he : (secondOpen.ι ⁻¹ᵁ firstOpen : secondOpen.toScheme.Opens) = secondOpen.ι ⁻¹ᵁ (firstOpen ⊓
      secondOpen) := by
      rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]
    rw [he]
    refine secondOpen.ι.isOpenEmbedding.isInducing.isCompact_preimage' hWc ?_
    rw [Scheme.Opens.range_ι]
    exact inf_le_right

  obtain ⟨firstOpenStage, hU⟩ := exists_modelWithOpenAt limit hU _ hWU
  obtain ⟨secondOpenStage, hV⟩ := exists_modelWithOpenAt limit hV _ hWV
  replace hU := hU.mono (IsCofiltered.minToLeft firstOpenStage secondOpenStage)
  replace hV := hV.mono (IsCofiltered.minToRight firstOpenStage secondOpenStage)
  set stageIndex := IsCofiltered.min firstOpenStage secondOpenStage with hk
  obtain ⟨firstStageScheme, firstStageMap, firstComparison, firstStageOpen, hpU, hcU, hqU, firstSquare,
    hOUc, hOU⟩ := hU
  obtain ⟨secondStageScheme, secondStageMap, secondComparison, secondStageOpen, hpV, hcV, hqV,
    secondSquare, hOVc, hOV⟩ := hV
  have := hpU; have := hcU; have := hqU; have := hpV; have := hcV; have := hqV
  have : CompactSpace firstStageOpen.toScheme := isCompact_iff_compactSpace.mp hOUc
  have : CompactSpace secondStageOpen.toScheme := isCompact_iff_compactSpace.mp hOVc
  have : QuasiSeparatedSpace firstStageOpen.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding firstStageOpen.ι.isOpenEmbedding
  have : QuasiSeparatedSpace secondStageOpen.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding secondStageOpen.ι.isOpenEmbedding

  have hrangeU : ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen))).opensRange
    = firstOpen.ι ⁻¹ᵁ secondOpen := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self,
      top_inf_eq]
  have hrangeV : ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤
    secondOpen))).opensRange = secondOpen.ι ⁻¹ᵁ firstOpen := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self,
      inf_top_eq]
  have hsubU : Set.range ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)) ≫
    firstComparison) ⊆ Set.range firstStageOpen.ι := by
    rintro - ⟨point, rfl⟩
    rw [Scheme.Opens.range_ι]
    change firstComparison (((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)))
      point) ∈ firstStageOpen
    have : ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen))) point ∈
      firstComparison ⁻¹ᵁ firstStageOpen := by
      rw [hOU, ← hrangeU]
      exact ⟨point, rfl⟩
    exact this
  have hsubV : Set.range ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)) ≫
    secondComparison) ⊆ Set.range secondStageOpen.ι := by
    rintro - ⟨point, rfl⟩
    rw [Scheme.Opens.range_ι]
    change secondComparison (((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤
      secondOpen))) point) ∈ secondStageOpen
    have : ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen))) point ∈
      secondComparison ⁻¹ᵁ secondStageOpen := by
      rw [hOV, ← hrangeV]
      exact ⟨point, rfl⟩
    exact this
  set firstIntersectionComparison : (firstOpen ⊓ secondOpen : ambientScheme.Opens).toScheme ⟶
    firstStageOpen.toScheme :=
    IsOpenImmersion.lift firstStageOpen.ι ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤
      firstOpen)) ≫ firstComparison) hsubU with haU₀
  set secondIntersectionComparison : (firstOpen ⊓ secondOpen : ambientScheme.Opens).toScheme ⟶
    secondStageOpen.toScheme :=
    IsOpenImmersion.lift secondStageOpen.ι ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen
      ≤ secondOpen)) ≫ secondComparison) hsubV with haV₀
  have HaU : IsPullback firstIntersectionComparison ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓
    secondOpen ≤ firstOpen))) firstStageOpen.ι firstComparison :=
    IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ hsubU).symm
      (by rw [Scheme.Opens.opensRange_ι, hOU, hrangeU])
  have HaV : IsPullback secondIntersectionComparison ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓
    secondOpen ≤ secondOpen))) secondStageOpen.ι secondComparison :=
    IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ hsubV).symm
      (by rw [Scheme.Opens.opensRange_ι, hOV, hrangeV])
  have HWU : IsPullback firstIntersectionComparison ((firstOpen ⊓ secondOpen : ambientScheme.Opens).ι ≫
    ambientMap) (firstStageOpen.ι ≫ firstStageMap) (cone.π.app stageIndex) := by
    have comparison := HaU.paste_vert firstSquare
    rwa [← Category.assoc, Scheme.homOfLE_ι] at comparison
  have HWV : IsPullback secondIntersectionComparison ((firstOpen ⊓ secondOpen : ambientScheme.Opens).ι ≫
    ambientMap) (secondStageOpen.ι ≫ secondStageMap) (cone.π.app stageIndex) := by
    have comparison := HaV.paste_vert secondSquare
    rwa [← Category.assoc, Scheme.homOfLE_ι] at comparison

  obtain ⟨laterIndex, laterTransition, hiso⟩ := Scheme.exists_iso_of_isPullback_of_isLimit limit HWU HWV

  set firstLaterScheme := pullback firstStageMap (diagram.map laterTransition) with hYU'
  set secondLaterScheme := pullback secondStageMap (diagram.map laterTransition) with hYV'
  set firstLaterMap : firstLaterScheme ⟶ diagram.obj laterIndex := pullback.snd firstStageMap
    (diagram.map laterTransition) with hpU'
  set secondLaterMap : secondLaterScheme ⟶ diagram.obj laterIndex := pullback.snd secondStageMap
    (diagram.map laterTransition) with hpV'
  set firstLaterComparison : firstOpen.toScheme ⟶ firstLaterScheme := modelBaseChangeLift diagram cone
    laterTransition firstSquare with hhU'
  set secondLaterComparison : secondOpen.toScheme ⟶ secondLaterScheme := modelBaseChangeLift diagram cone
    laterTransition secondSquare with hhV'
  have firstLaterSquare : IsPullback firstLaterComparison (firstOpen.ι ≫ ambientMap) firstLaterMap
    (cone.π.app laterIndex) := isPullback_modelBaseChangeLift laterTransition firstSquare
  have secondLaterSquare : IsPullback secondLaterComparison (secondOpen.ι ≫ ambientMap) secondLaterMap
    (cone.π.app laterIndex) := isPullback_modelBaseChangeLift laterTransition secondSquare
  set firstLaterOpen : firstLaterScheme.Opens := pullback.fst firstStageMap (diagram.map laterTransition)
    ⁻¹ᵁ firstStageOpen with hOU'
  set secondLaterOpen : secondLaterScheme.Opens := pullback.fst secondStageMap (diagram.map
    laterTransition) ⁻¹ᵁ secondStageOpen with hOV'
  have HqU : IsPullback (pullback.fst firstStageMap (diagram.map laterTransition) ∣_ firstStageOpen)
    (firstLaterOpen.ι ≫ firstLaterMap) (firstStageOpen.ι ≫ firstStageMap)
      (diagram.map laterTransition) :=
    (isPullback_morphismRestrict (pullback.fst firstStageMap (diagram.map laterTransition))
      firstStageOpen).paste_vert
      (IsPullback.of_hasPullback firstStageMap (diagram.map laterTransition))
  have HqV : IsPullback (pullback.fst secondStageMap (diagram.map laterTransition) ∣_ secondStageOpen)
    (secondLaterOpen.ι ≫ secondLaterMap) (secondStageOpen.ι ≫ secondStageMap)
      (diagram.map laterTransition) :=
    (isPullback_morphismRestrict (pullback.fst secondStageMap (diagram.map laterTransition))
      secondStageOpen).paste_vert
      (IsPullback.of_hasPullback secondStageMap (diagram.map laterTransition))
  set firstLaterIntersectionComparison : (firstOpen ⊓ secondOpen : ambientScheme.Opens).toScheme ⟶
    firstLaterOpen.toScheme :=
    HqU.lift firstIntersectionComparison ((firstOpen ⊓ secondOpen : ambientScheme.Opens).ι ≫ ambientMap ≫
      cone.π.app laterIndex)
      (by rw [HWU.w]; simp only [Category.assoc]; rw [cone.w laterTransition]) with hh₁'
  set secondLaterIntersectionComparison : (firstOpen ⊓ secondOpen : ambientScheme.Opens).toScheme ⟶
    secondLaterOpen.toScheme :=
    HqV.lift secondIntersectionComparison ((firstOpen ⊓ secondOpen : ambientScheme.Opens).ι ≫ ambientMap
      ≫ cone.π.app laterIndex)
      (by rw [HWV.w]; simp only [Category.assoc]; rw [cone.w laterTransition]) with hh₂'
  obtain ⟨modelIso, he₁, he₂⟩ := hiso (firstLaterComparison := firstLaterIntersectionComparison)
    (secondLaterComparison := secondLaterIntersectionComparison) HqU
    (by rw [hh₁']; exact IsPullback.lift_fst ..)
    (by rw [hh₁', IsPullback.lift_snd, Category.assoc]) HqV
    (by rw [hh₂']; exact IsPullback.lift_fst ..)
    (by rw [hh₂', IsPullback.lift_snd, Category.assoc])

  have hOU'c : IsCompact ((firstLaterOpen : firstLaterScheme.Opens) : Set firstLaterScheme) := by
    have : QuasiCompact (pullback.fst firstStageMap (diagram.map laterTransition)) :=
      MorphismProperty.pullback_fst _ _ inferInstance
    rw [hOU']
    exact QuasiCompact.isCompact_preimage _ firstStageOpen.isOpen hOUc
  have : CompactSpace ↥(firstLaterOpen.toScheme) := isCompact_iff_compactSpace.mp hOU'c
  have hcomm : firstLaterOpen.ι ≫ firstLaterMap = (modelIso.hom ≫ secondLaterOpen.ι) ≫ secondLaterMap
    := by rw [Category.assoc, he₁]
  have hpreU : firstLaterComparison ⁻¹ᵁ firstLaterOpen = firstOpen.ι ⁻¹ᵁ secondOpen := by
    rw [hOU', ← Scheme.Hom.comp_preimage, hhU', modelBaseChangeLift_fst, hOU]
  have hpreV : secondLaterComparison ⁻¹ᵁ secondLaterOpen = secondOpen.ι ⁻¹ᵁ firstOpen := by
    rw [hOV', ← Scheme.Hom.comp_preimage, hhV', modelBaseChangeLift_fst, hOV]
  have hcommU : (ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)) ≫
    firstLaterComparison = firstLaterIntersectionComparison ≫ firstLaterOpen.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hhU', modelBaseChangeLift_fst, Category.assoc,
        ← morphismRestrict_ι (pullback.fst firstStageMap (diagram.map laterTransition)) firstStageOpen, ←
          Category.assoc, hh₁',
        IsPullback.lift_fst, haU₀, IsOpenImmersion.lift_fac]
    · rw [Category.assoc, hhU', modelBaseChangeLift_snd, Category.assoc]
      change _ = firstLaterIntersectionComparison ≫ firstLaterOpen.ι ≫ firstLaterMap
      rw [← Category.assoc, hh₁', IsPullback.lift_snd, Category.assoc,
        ← Category.assoc ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen))),
          Scheme.homOfLE_ι]
  have hcommV' : (ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)) ≫
    secondLaterComparison = secondLaterIntersectionComparison ≫ secondLaterOpen.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hhV', modelBaseChangeLift_fst, Category.assoc,
        ← morphismRestrict_ι (pullback.fst secondStageMap (diagram.map laterTransition)) secondStageOpen,
          ← Category.assoc, hh₂',
        IsPullback.lift_fst, haV₀, IsOpenImmersion.lift_fac]
    · rw [Category.assoc, hhV', modelBaseChangeLift_snd, Category.assoc]
      change _ = secondLaterIntersectionComparison ≫ secondLaterOpen.ι ≫ secondLaterMap
      rw [← Category.assoc, hh₂', IsPullback.lift_snd, Category.assoc,
        ← Category.assoc ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen))),
          Scheme.homOfLE_ι]
  have hcommV : (ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)) ≫
    secondLaterComparison = firstLaterIntersectionComparison ≫ modelIso.hom ≫ secondLaterOpen.ι := by
    rw [← Category.assoc, he₂, hcommV']
  have HsqU : IsPullback firstLaterIntersectionComparison ((ambientScheme.homOfLE (inf_le_left :
    firstOpen ⊓ secondOpen ≤ firstOpen))) firstLaterOpen.ι firstLaterComparison :=
    IsOpenImmersion.isPullback _ _ _ _ hcommU
      (by rw [Scheme.Opens.opensRange_ι, hpreU, hrangeU])
  have HsqV : IsPullback firstLaterIntersectionComparison ((ambientScheme.homOfLE (inf_le_right :
    firstOpen ⊓ secondOpen ≤ secondOpen))) (modelIso.hom ≫ secondLaterOpen.ι) secondLaterComparison :=
    IsOpenImmersion.isPullback _ _ _ _ hcommV
      (by
        rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι, hpreV, hrangeV])

  have hf : firstLaterIntersectionComparison ≫ firstLaterOpen.ι = (ambientScheme.homOfLE (inf_le_left :
    firstOpen ⊓ secondOpen ≤ firstOpen)) ≫ firstLaterComparison := hcommU.symm
  have hg : firstLaterIntersectionComparison ≫ (modelIso.hom ≫ secondLaterOpen.ι) =
    (ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)) ≫ secondLaterComparison
    := hcommV.symm
  set stageMap : pushout firstLaterOpen.ι (modelIso.hom ≫ secondLaterOpen.ι) ⟶ diagram.obj laterIndex :=
    pushout.desc firstLaterMap secondLaterMap hcomm with hp
  set gluedComparison := pushout.map ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤
    firstOpen)))
    ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen))) firstLaterOpen.ι
      (modelIso.hom ≫ secondLaterOpen.ι) firstLaterComparison secondLaterComparison
      firstLaterIntersectionComparison
    hf.symm hg.symm with hρ
  have hchartU := isPullback_pushout_map_inl_of_isPullback firstLaterOpen.ι (modelIso.hom ≫
    secondLaterOpen.ι)
    ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen))) ((ambientScheme.homOfLE
      (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)))
    firstLaterComparison secondLaterComparison firstLaterIntersectionComparison hf hg HsqV
  have hchartV := isPullback_pushout_map_inr_of_isPullback firstLaterOpen.ι (modelIso.hom ≫
    secondLaterOpen.ι)
    ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen))) ((ambientScheme.homOfLE
      (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)))
    firstLaterComparison secondLaterComparison firstLaterIntersectionComparison hf hg HsqU
  have hw : gluedComparison ≫ stageMap = (pushoutOpensDesc firstOpen secondOpen ≫ ambientMap) ≫
    cone.π.app laterIndex := by
    apply pushout.hom_ext
    · rw [← Category.assoc, hρ, pushout.inl_desc, Category.assoc, hp, pushout.inl_desc]
      have hw' := firstLaterSquare.w
      simp only [Category.assoc] at hw' ⊢
      rw [inl_pushoutOpensDesc_assoc]
      exact hw'
    · rw [← Category.assoc, hρ, pushout.inr_desc, Category.assoc, hp, pushout.inr_desc]
      have hw' := secondLaterSquare.w
      simp only [Category.assoc] at hw' ⊢
      rw [inr_pushoutOpensDesc_assoc]
      exact hw'
  have hmain : IsPullback gluedComparison (pushoutOpensDesc firstOpen secondOpen ≫ ambientMap) stageMap
    (cone.π.app laterIndex) := by
    refine isPullback_of_opensRange_sup_eq_top hw (pushout.inl firstLaterOpen.ι (modelIso.hom ≫
      secondLaterOpen.ι))
      (pushout.inr firstLaterOpen.ι (modelIso.hom ≫ secondLaterOpen.ι))
      (opensRange_pushout_inl_sup_opensRange_pushout_inr firstLaterOpen.ι (modelIso.hom ≫
        secondLaterOpen.ι))
      hchartU hchartV ?_ ?_
    · rw [inl_pushoutOpensDesc_assoc, hp, pushout.inl_desc]
      exact firstLaterSquare
    · rw [inr_pushoutOpensDesc_assoc, hp, pushout.inr_desc]
      exact secondLaterSquare
  have := isIso_pushoutOpensDesc firstOpen secondOpen hUV
  refine ⟨laterIndex, pushout firstLaterOpen.ι (modelIso.hom ≫ secondLaterOpen.ι), stageMap, inv
    (pushoutOpensDesc firstOpen secondOpen) ≫ gluedComparison,
    IsZariskiLocalAtSource.pushout_desc firstLaterOpen.ι (modelIso.hom ≫ secondLaterOpen.ι) hcomm
      inferInstance inferInstance,
    inferInstance,
    quasiSeparatedSpace_pushout firstLaterOpen.ι (modelIso.hom ≫ secondLaterOpen.ι), ?_⟩
  have hiso : IsPullback (inv (pushoutOpensDesc firstOpen secondOpen)) ambientMap (pushoutOpensDesc
    firstOpen secondOpen ≫ ambientMap)
      (𝟙 cone.pt) := IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa using hiso.paste_horiz hmain

include limit in
/-- **Descent to a finite stage for a finite union of affine opens**, each of
which lies over an affine open of the stage `baseStage`. -/
private lemma hasFiniteStageModel_finsetSup {sourceScheme : Scheme.{schemeUniverse}} [QuasiSeparatedSpace
    sourceScheme] {baseStage : Index} (sourceMap : sourceScheme ⟶ cone.pt)
    [LocallyOfFinitePresentation sourceMap] (opens : Finset sourceScheme.Opens)
    (hs : ∀ chosenOpen ∈ opens, IsAffineOpen chosenOpen ∧
      ∃ secondOpen : (diagram.obj baseStage).Opens, IsAffineOpen secondOpen ∧ chosenOpen ≤ (sourceMap ≫
        cone.π.app baseStage) ⁻¹ᵁ secondOpen) :
    HasFiniteStageModel diagram cone ((opens.sup id : sourceScheme.Opens).ι ≫ sourceMap) := by
  classical
  induction opens using Finset.induction with
  | empty =>
      rw [Finset.sup_empty]
      exact HasFiniteStageModel.of_isAffineOpen limit sourceMap (isAffineOpen_bot sourceScheme)
        (isAffineOpen_bot (diagram.obj baseStage)) bot_le
  | insert addedOpen opens not_mem inductionHypothesis =>
      obtain ⟨haff, Va, hVa, hale⟩ := hs addedOpen (Finset.mem_insert_self addedOpen opens)
      have hsaff : ∀ chosenOpen ∈ opens, IsAffineOpen chosenOpen ∧
          ∃ secondOpen : (diagram.obj baseStage).Opens, IsAffineOpen secondOpen ∧ chosenOpen ≤ (sourceMap
            ≫ cone.π.app baseStage) ⁻¹ᵁ secondOpen :=
        fun chosenOpen hW ↦ hs chosenOpen (Finset.mem_insert_of_mem hW)
      rw [Finset.sup_insert, id]
      set ambientScheme : sourceScheme.Opens := addedOpen ⊔ opens.sup id with hZ
      have : QuasiSeparatedSpace ambientScheme.toScheme :=
        QuasiSeparatedSpace.of_isOpenEmbedding ambientScheme.ι.isOpenEmbedding
      set firstOpen : ambientScheme.toScheme.Opens := ambientScheme.ι ⁻¹ᵁ (opens.sup id) with hUdef
      set secondOpen : ambientScheme.toScheme.Opens := ambientScheme.ι ⁻¹ᵁ addedOpen with hVdef
      have hUV : firstOpen ⊔ secondOpen = ⊤ := by
        rw [hUdef, hVdef, ← Scheme.Hom.preimage_sup, sup_comm, ← hZ,
          Scheme.Opens.ι_preimage_self]

      have hsc : IsCompact ((opens.sup id : sourceScheme.Opens) : Set sourceScheme) :=
        isCompact_finset_sup opens fun chosenOpen hW ↦ (hsaff chosenOpen hW).1.isCompact
      have hinfc : IsCompact (((opens.sup id ⊓ addedOpen : sourceScheme.Opens)) : Set sourceScheme) := by
        rw [TopologicalSpace.Opens.coe_inf]
        exact QuasiSeparatedSpace.inter_isCompact _ _ (opens.sup id).2 hsc addedOpen.2 haff.isCompact
      have hUVc : IsCompact ((firstOpen ⊓ secondOpen : ambientScheme.toScheme.Opens) : Set
        ambientScheme.toScheme) := by
        have he : (firstOpen ⊓ secondOpen : ambientScheme.toScheme.Opens) = ambientScheme.ι ⁻¹ᵁ
          (opens.sup id ⊓ addedOpen) := by
          rw [hUdef, hVdef, Scheme.Hom.preimage_inf]
        rw [he]
        refine ambientScheme.ι.isOpenEmbedding.isInducing.isCompact_preimage' hinfc ?_
        rw [Scheme.Opens.range_ι]
        exact le_trans inf_le_left le_sup_right
      refine HasFiniteStageModel.of_sup_eq_top limit (ambientScheme.ι ≫ sourceMap) firstOpen secondOpen
        hUV hUVc ?_ ?_
      ·
        have hrange : Set.range (firstOpen.ι ≫ ambientScheme.ι) = Set.range (opens.sup id :
          sourceScheme.Opens).ι := by
          rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange]
          congr 1
          simp only [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, hUdef,
            Scheme.Hom.image_preimage_eq_opensRange_inf, hZ]
          exact inf_eq_right.mpr (le_sup_right : (opens.sup id : sourceScheme.Opens) ≤ addedOpen ⊔
            opens.sup id)
        have := HasFiniteStageModel.comp_iso
          (IsOpenImmersion.isoOfRangeEq (firstOpen.ι ≫ ambientScheme.ι) (opens.sup id :
            sourceScheme.Opens).ι hrange) (inductionHypothesis hsaff)
        rwa [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Category.assoc] at this
      ·
        refine HasFiniteStageModel.of_isAffineOpen limit (ambientScheme.ι ≫ sourceMap) ?_ hVa ?_
        · refine haff.preimage_of_isOpenImmersion ambientScheme.ι ?_
          rw [Scheme.Opens.opensRange_ι, hZ]
          exact le_sup_left
        · rw [Category.assoc, Scheme.Hom.comp_preimage]
          exact ambientScheme.ι.preimage_mono hale

set_option backward.isDefEq.respectTransparency false in
include limit in
/-- A finitely presented scheme over a cofiltered limit of quasi-compact,
quasi-separated schemes with affine transitions is the pullback of an actual
finitely presented scheme over some stage. -/
theorem Scheme.exists_isPullback_of_finitePresentation [∀ index, CompactSpace (diagram.obj index)]
    [∀ index, QuasiSeparatedSpace (diagram.obj index)] {sourceScheme : Scheme.{schemeUniverse}}
      (sourceMap : sourceScheme ⟶ cone.pt)
    [LocallyOfFinitePresentation sourceMap] [QuasiCompact sourceMap] [QuasiSeparated sourceMap] :
    ∃ (index : Index) (stageScheme : Scheme.{schemeUniverse}) (stageMap : stageScheme ⟶ diagram.obj
      index) (_ : LocallyOfFinitePresentation stageMap)
      (_ : QuasiCompact stageMap) (_ : QuasiSeparated stageMap) (comparison : sourceScheme ⟶
        stageScheme),
      IsPullback comparison sourceMap stageMap (cone.π.app index) := by
  classical
  obtain ⟨baseStage⟩ : Nonempty Index := IsCofiltered.nonempty
  have := isAffineHom_π_app _ _ limit
  have : CompactSpace cone.pt := QuasiCompact.compactSpace_of_compactSpace (cone.π.app baseStage)
  have : QuasiSeparatedSpace cone.pt := quasiSeparatedSpace_of_quasiSeparated (cone.π.app baseStage)
  have : CompactSpace sourceScheme := QuasiCompact.compactSpace_of_compactSpace sourceMap
  have : QuasiSeparatedSpace sourceScheme := quasiSeparatedSpace_of_quasiSeparated sourceMap
  obtain ⟨coverOpens, cover_basis, cover_finite, cover_union⟩ :=
    (isBasis_affineOpens_le_preimage (sourceMap ≫ cone.π.app baseStage)).exists_finite_of_isCompact
      (U := ⊤) (by simpa using isCompact_univ)
  have modelData := hasFiniteStageModel_finsetSup limit (baseStage := baseStage) sourceMap
    cover_finite.toFinset
    (fun chosenOpen hW ↦ cover_basis (cover_finite.mem_toFinset.mp hW))
  rw [Finset.sup_id_eq_sSup, cover_finite.coe_toFinset, ← cover_union] at modelData
  replace modelData := HasFiniteStageModel.comp_iso sourceScheme.topIso.symm modelData
  rw [Iso.symm_hom, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp] at modelData
  obtain ⟨index, stageScheme, stageMap, comparison, hp, hcpt, hqs, hsq⟩ := modelData
  have := hp; have := hcpt; have := hqs
  exact ⟨index, stageScheme, stageMap, hp, inferInstance, inferInstance, comparison, hsq⟩

end AlgebraicGeometry
