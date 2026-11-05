import Jacobian.AlgebraicGeometry.Descent.Morphisms
import Jacobian.AlgebraicGeometry.Descent.InvariantOpen
import Jacobian.AlgebraicGeometry.Morphisms.LocalIso
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Gluing effective scheme descent

For a faithfully flat quasi-compact morphism, effectivity is local on invariant
open subschemes. Descend all effective invariant opens and their inclusions,
then glue the resulting locally directed diagram of open immersions. The
comparison with the original scheme is an injective and surjective local
isomorphism.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {sourceScheme baseScheme : Scheme.{schemeUniverse}} {baseMap : sourceScheme ⟶ baseScheme} {representation : Over sourceScheme} {datum : DescentDatum baseMap representation}

section Saturation

variable {openSubset : representation.left.Opens} {hU : datum.IsInvariant openSubset} {descendedObject : Over baseScheme} {descentMap : openSubset.toScheme ⟶ descendedObject.left}
  (hq : IsPullback descentMap (openSubset.ι ≫ representation.hom) descendedObject.hom baseMap)
  (hinv : ∀ {testScheme : Scheme.{schemeUniverse}} (firstMap secondMap : testScheme ⟶ sourceScheme) (covering : firstMap ≫ baseMap = secondMap ≫ baseMap)
    (point : Over.mk firstMap ⟶ Over.mk (openSubset.ι ≫ representation.hom)),
    ((datum.restrict openSubset hU).transport firstMap secondMap covering point).left ≫ descentMap = point.left ≫ descentMap)

include hq hinv in
lemma mem_of_apply_eq_apply {descendedOpen : representation.left.Opens} (hO : datum.IsInvariant descendedOpen) {point otherPoint : openSubset}
    (hww' : descentMap point = descentMap otherPoint) (hw' : (otherPoint : representation.left) ∈ descendedOpen) : (point : representation.left) ∈ descendedOpen := by
  obtain ⟨pullbackPoint, ht₁, ht₂⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := descentMap) (g := descentMap) otherPoint point hww'.symm
  let testScheme := (pullback.fst descentMap descentMap ≫ openSubset.ι) ⁻¹ᵁ descendedOpen
  have ht : pullbackPoint ∈ testScheme := by
    rw [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply, ht₁]
    exact hw'
  have hp : (testScheme.ι ≫ pullback.fst descentMap descentMap ≫ openSubset.ι ≫ representation.hom) ≫ baseMap =
      (testScheme.ι ≫ pullback.snd descentMap descentMap ≫ openSubset.ι ≫ representation.hom) ≫ baseMap := by
    simp only [Category.assoc, ← hq.w, pullback.condition_assoc]
  have he := (datum.restrict openSubset hU).transport_eq_of_isPullback hq hinv _ _ hp
    (Over.homMk (testScheme.ι ≫ pullback.fst descentMap descentMap) (by simp))
    (Over.homMk (testScheme.ι ≫ pullback.snd descentMap descentMap) (by simp)) (by simp [pullback.condition])
  have hl := restrict_transport_left_ι openSubset hU _ _ hp (Over.homMk (testScheme.ι ≫ pullback.fst descentMap descentMap) (by simp))
  rw [he] at hl
  have hr := hO _ _ hp (Over.homMk ((Over.homMk (testScheme.ι ≫ pullback.fst descentMap descentMap) (by simp) :
      Over.mk (testScheme.ι ≫ pullback.fst descentMap descentMap ≫ openSubset.ι ≫ representation.hom) ⟶ Over.mk (openSubset.ι ≫ representation.hom)).left ≫ openSubset.ι)
      (by simp)) (by
    rintro _ ⟨sectionPoint, rfl⟩
    exact sectionPoint.2)
  rw [← hl] at hr
  refine hr ⟨⟨pullbackPoint, ht⟩, ?_⟩
  simp [ht₂]

end Saturation

@[reassoc]
lemma restrict_transport_left_homOfLE {openSubset smallerOpen : representation.left.Opens} (hU : datum.IsInvariant openSubset)
    (hU' : datum.IsInvariant smallerOpen) (hle : smallerOpen ≤ openSubset) {testScheme : Scheme.{schemeUniverse}} (firstMap secondMap : testScheme ⟶ sourceScheme)
    (covering : firstMap ≫ baseMap = secondMap ≫ baseMap) (point : Over.mk firstMap ⟶ Over.mk (smallerOpen.ι ≫ representation.hom)) :
    ((datum.restrict smallerOpen hU').transport firstMap secondMap covering point).left ≫ representation.left.homOfLE hle =
      ((datum.restrict openSubset hU).transport firstMap secondMap covering
        (Over.homMk (point.left ≫ representation.left.homOfLE hle) (by simpa using Over.w point))).left := by
  rw [← cancel_mono openSubset.ι, Category.assoc, Scheme.homOfLE_ι, restrict_transport_left_ι,
    restrict_transport_left_ι]
  exact datum.transport_left_congr _ _ _ _ rfl rfl (by simp)

lemma isEffective_restrict_of_le [Flat baseMap] [Surjective baseMap] [QuasiCompact baseMap] {openSubset smallerOpen : representation.left.Opens}
    (hU : datum.IsInvariant openSubset) (hU' : datum.IsInvariant smallerOpen) (hle : smallerOpen ≤ openSubset)
    (hE : (datum.restrict openSubset hU).IsEffective) : (datum.restrict smallerOpen hU').IsEffective := by
  obtain ⟨descendedObject, descentMap, hq, hinv⟩ := hE
  have : Flat descentMap := MorphismProperty.of_isPullback hq.flip inferInstance
  have : Surjective descentMap := MorphismProperty.of_isPullback hq.flip inferInstance
  have : QuasiCompact descentMap := MorphismProperty.of_isPullback hq.flip inferInstance
  have hsat : descentMap ⁻¹' (descentMap '' (openSubset.ι ⁻¹ᵁ smallerOpen : Set openSubset.toScheme)) = (openSubset.ι ⁻¹ᵁ smallerOpen : Set openSubset.toScheme) := by
    refine subset_antisymm (fun point ⟨otherPoint, hw', point_eq⟩ ↦ ?_) (Set.subset_preimage_image _ _)
    exact mem_of_apply_eq_apply hq hinv hU' point_eq.symm hw'
  let descendedOpen : descendedObject.left.Opens := ⟨descentMap '' (openSubset.ι ⁻¹ᵁ smallerOpen : Set openSubset.toScheme),
    (Flat.isQuotientMap_of_surjective descentMap).isOpen_preimage.mp (by
      rw [hsat]
      exact (openSubset.ι ⁻¹ᵁ smallerOpen).2)⟩
  have hO : descentMap ⁻¹ᵁ descendedOpen = openSubset.ι ⁻¹ᵁ smallerOpen := TopologicalSpace.Opens.ext hsat
  have hr : Set.range (representation.left.homOfLE hle ≫ descentMap) ⊆ Set.range descendedOpen.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨point, rfl⟩
    refine ⟨representation.left.homOfLE hle point, ?_, rfl⟩
    rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply]
    rw [Scheme.homOfLE_ι]
    exact point.2
  let q' := IsOpenImmersion.lift descendedOpen.ι (representation.left.homOfLE hle ≫ descentMap) hr
  have hq' : q' ≫ descendedOpen.ι = representation.left.homOfLE hle ≫ descentMap := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.mk (descendedOpen.ι ≫ descendedObject.hom), q', ?_, fun firstMap secondMap covering point ↦ ?_⟩
  · have top : IsPullback q' (representation.left.homOfLE hle) descendedOpen.ι descentMap :=
      IsOpenImmersion.isPullback _ _ _ _ hq'.symm (by
        rw [Scheme.Opens.opensRange_ι, Scheme.opensRange_homOfLE, hO])
    simpa using top.paste_vert hq
  · rw [← cancel_mono descendedOpen.ι, Category.assoc, hq', Category.assoc, hq',
      restrict_transport_left_homOfLE_assoc hU hU' hle, hinv]
    rfl

namespace EffectiveGluing

variable (datum) in
private abbrev Index : Type schemeUniverse := {openSubset : representation.left.Opens // ∃ hU : datum.IsInvariant openSubset, (datum.restrict openSubset hU).IsEffective}

private instance : PartialOrder (Index datum) := Subtype.partialOrder _

private instance : Category (Index datum) := Preorder.smallCategory _

private instance : Quiver.IsThin (Index datum) := fun _ _ ↦ inferInstanceAs (Subsingleton (ULift _))

private lemma isInvariant (index : Index datum) : datum.IsInvariant index.1 := index.2.1

private noncomputable def descended (index : Index datum) : Over baseScheme := index.2.2.choose

private noncomputable def projection (index : Index datum) : index.1.toScheme ⟶ (descended index).left := index.2.2.choose_spec.choose

private lemma isPullback_projection (index : Index datum) : IsPullback (projection index) (index.1.ι ≫ representation.hom) (descended index).hom baseMap :=
  index.2.2.choose_spec.choose_spec.1

@[reassoc]
private lemma projection_transport (index : Index datum) {testScheme : Scheme.{schemeUniverse}} (firstMap secondMap : testScheme ⟶ sourceScheme) (covering : firstMap ≫ baseMap = secondMap ≫ baseMap)
    (point : Over.mk firstMap ⟶ Over.mk (index.1.ι ≫ representation.hom)) :
    ((datum.restrict index.1 (isInvariant index)).transport firstMap secondMap covering point).left ≫ projection index = point.left ≫ projection index :=
  index.2.2.choose_spec.choose_spec.2 firstMap secondMap covering point

variable [Flat baseMap] [Surjective baseMap] [QuasiCompact baseMap]

private instance (index : Index datum) : Flat (projection index) :=
  MorphismProperty.of_isPullback (isPullback_projection index).flip inferInstance

private instance (index : Index datum) : Surjective (projection index) :=
  MorphismProperty.of_isPullback (isPullback_projection index).flip inferInstance

private instance (index : Index datum) : QuasiCompact (projection index) :=
  MorphismProperty.of_isPullback (isPullback_projection index).flip inferInstance

private lemma existsUnique_transition {index largerIndex : Index datum} (hle : index.1 ≤ largerIndex.1) :
    ∃! transitionMap : (descended index).left ⟶ (descended largerIndex).left, projection index ≫ transitionMap = representation.left.homOfLE hle ≫ projection largerIndex :=
  (datum.restrict index.1 (isInvariant index)).existsUnique_desc_of_isPullback (isPullback_projection index)
    (projection_transport index) _ fun firstMap secondMap covering point ↦ by
      rw [← Category.assoc, restrict_transport_left_homOfLE (isInvariant largerIndex) (isInvariant index) hle,
        projection_transport largerIndex]
      simp

private noncomputable def transition {index largerIndex : Index datum} (hle : index.1 ≤ largerIndex.1) : (descended index).left ⟶ (descended largerIndex).left :=
  (existsUnique_transition hle).exists.choose

@[reassoc]
private lemma projection_transition {index largerIndex : Index datum} (hle : index.1 ≤ largerIndex.1) :
    projection index ≫ transition hle = representation.left.homOfLE hle ≫ projection largerIndex :=
  (existsUnique_transition hle).exists.choose_spec

private lemma transition_unique {index largerIndex : Index datum} (hle : index.1 ≤ largerIndex.1) (transitionMap : (descended index).left ⟶ (descended largerIndex).left)
    (hg : projection index ≫ transitionMap = representation.left.homOfLE hle ≫ projection largerIndex) : transitionMap = transition hle :=
  (existsUnique_transition hle).unique hg (projection_transition hle)

@[reassoc (attr := simp)]
private lemma transition_hom {index largerIndex : Index datum} (hle : index.1 ≤ largerIndex.1) : transition hle ≫ (descended largerIndex).hom = (descended index).hom := by
  rw [← cancel_epi (projection index), projection_transition_assoc, (isPullback_projection largerIndex).w, (isPullback_projection index).w]
  simp

@[simps]
private noncomputable def diagram : Index datum ⥤ Scheme.{schemeUniverse} where
  obj index := (descended index).left
  map transitionMap := transition (leOfHom transitionMap)
  map_id index := (transition_unique _ _ (by simp)).symm
  map_comp {index largerIndex lastIndex} transitionMap secondTransitionMap := (transition_unique _ _ (by
    rw [projection_transition_assoc, projection_transition, Scheme.homOfLE_homOfLE_assoc])).symm

private lemma isPullback_trans {index largerIndex : Index datum} (hle : index.1 ≤ largerIndex.1) :
    IsPullback (representation.left.homOfLE hle) (projection index) (projection largerIndex) (transition hle) := by
  refine (IsPullback.of_bot ?_ (projection_transition hle) (isPullback_projection largerIndex)).flip
  simpa using isPullback_projection index

private instance {index largerIndex : Index datum} (transitionMap : index ⟶ largerIndex) : IsOpenImmersion ((diagram (datum := datum)).map transitionMap) :=
  MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (isPullback_trans (leOfHom transitionMap))
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

private lemma transition_projection_apply {index largerIndex : Index datum} (hle : index.1 ≤ largerIndex.1) (point : index.1.toScheme) :
    transition hle (projection index point) = projection largerIndex (representation.left.homOfLE hle point) := by
  rw [← Scheme.Hom.comp_apply, projection_transition, Scheme.Hom.comp_apply]

private def inf (firstIndex secondIndex : Index datum) : Index datum :=
  ⟨firstIndex.1 ⊓ secondIndex.1, (isInvariant firstIndex).inf _ (isInvariant secondIndex),
    isEffective_restrict_of_le (isInvariant firstIndex) _ inf_le_left firstIndex.2.2⟩

private lemma inf_le_left (firstIndex secondIndex : Index datum) : inf firstIndex secondIndex ≤ firstIndex := _root_.inf_le_left (a := firstIndex.1) (b := secondIndex.1)

private lemma inf_le_right (firstIndex secondIndex : Index datum) : inf firstIndex secondIndex ≤ secondIndex := _root_.inf_le_right (a := firstIndex.1) (b := secondIndex.1)

private instance isLocallyDirected : ((diagram (datum := datum)) ⋙ Scheme.forget).IsLocallyDirected where
  cond {firstIndex secondIndex commonIndex} fi fj xi xj hx := by
    obtain ⟨wi, rfl⟩ := (projection firstIndex).surjective xi
    obtain ⟨wj, rfl⟩ := (projection secondIndex).surjective xj
    change transition _ (projection firstIndex wi) = transition _ (projection secondIndex wj) at hx
    rw [transition_projection_apply, transition_projection_apply] at hx
    have hwj : (representation.left.homOfLE (leOfHom fi) wi).1 ∈ secondIndex.1 :=
      mem_of_apply_eq_apply (isPullback_projection commonIndex) (projection_transport commonIndex) (isInvariant secondIndex) hx
        (by simp)
    let point : (inf firstIndex secondIndex).1.toScheme := ⟨wi.1, wi.2, by simpa using hwj⟩
    refine ⟨inf firstIndex secondIndex, homOfLE (inf_le_left firstIndex secondIndex), homOfLE (inf_le_right firstIndex secondIndex), projection (inf firstIndex secondIndex) point,
      ?_, ?_⟩
    · change transition _ (projection _ point) = _
      rw [transition_projection_apply]
      congr 1
      exact Subtype.ext (by simp [point])
    · change transition _ (projection _ point) = _
      rw [transition_projection_apply]
      apply ((diagram (datum := datum)).map fj).isOpenEmbedding.injective
      change transition _ (projection _ _) = transition _ (projection _ _)
      rw [transition_projection_apply, transition_projection_apply, ← hx]
      congr 1
      exact Subtype.ext (by simp [point])

section Colimit

private noncomputable abbrev glued : Scheme.{schemeUniverse} := colimit (diagram (datum := datum))

private noncomputable def gluedHom : glued (datum := datum) ⟶ baseScheme :=
  colimit.desc _ { pt := baseScheme, ι := { app index := (descended index).hom } }

@[reassoc (attr := simp)]
private lemma ι_gluedHom (index : Index datum) : colimit.ι (diagram (datum := datum)) index ≫ gluedHom = (descended index).hom :=
  colimit.ι_desc _ _

private noncomputable def localComparison (index : Index datum) : index.1.toScheme ⟶ Limits.pullback (gluedHom (datum := datum)) baseMap :=
  pullback.lift (projection index ≫ colimit.ι (diagram (datum := datum)) index) (index.1.ι ≫ representation.hom)
    (by rw [Category.assoc, ι_gluedHom, (isPullback_projection index).w])

@[reassoc (attr := simp)]
private lemma localComparison_fst (index : Index datum) : localComparison index ≫ pullback.fst gluedHom baseMap = projection index ≫ colimit.ι (diagram (datum := datum)) index :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private lemma localComparison_snd (index : Index datum) : localComparison index ≫ pullback.snd gluedHom baseMap = index.1.ι ≫ representation.hom :=
  pullback.lift_snd _ _ _

private lemma isPullback_localComparison (index : Index datum) :
    IsPullback (localComparison index) (projection index) (pullback.fst gluedHom baseMap) (colimit.ι (diagram (datum := datum)) index) := by
  refine IsPullback.of_right ?_ (localComparison_fst index) (IsPullback.of_hasPullback gluedHom baseMap).flip
  simpa using (isPullback_projection index).flip

private instance (index : Index datum) : IsOpenImmersion (localComparison index) :=
  MorphismProperty.of_isPullback (isPullback_localComparison index).flip inferInstance

private lemma homOfLE_localComparison {index largerIndex : Index datum} (hle : index.1 ≤ largerIndex.1) : representation.left.homOfLE hle ≫ localComparison largerIndex = localComparison index := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, localComparison_fst, localComparison_fst, ← projection_transition_assoc hle]
    exact congrArg (projection index ≫ ·) (colimit.w (diagram (datum := datum)) (homOfLE hle))
  · simp

private lemma localComparison_compat (firstIndex secondIndex : Index datum) :
    pullback.fst firstIndex.1.ι secondIndex.1.ι ≫ localComparison firstIndex = pullback.snd firstIndex.1.ι secondIndex.1.ι ≫ localComparison secondIndex := by
  have hr : Set.range (pullback.fst firstIndex.1.ι secondIndex.1.ι ≫ firstIndex.1.ι) ⊆ Set.range (inf firstIndex secondIndex).1.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨chartPoint, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    · rw [← Scheme.Opens.range_ι, pullback.condition]
      exact ⟨_, rfl⟩
  let intersectionMap := IsOpenImmersion.lift (inf firstIndex secondIndex).1.ι (pullback.fst _ _ ≫ firstIndex.1.ι) hr
  have hπ : intersectionMap ≫ (inf firstIndex secondIndex).1.ι = pullback.fst _ _ ≫ firstIndex.1.ι := IsOpenImmersion.lift_fac _ _ _
  have h1 : pullback.fst firstIndex.1.ι secondIndex.1.ι = intersectionMap ≫ representation.left.homOfLE (inf_le_left firstIndex secondIndex) := by
    rw [← cancel_mono firstIndex.1.ι, Category.assoc, Scheme.homOfLE_ι, hπ]
  have h2 : pullback.snd firstIndex.1.ι secondIndex.1.ι = intersectionMap ≫ representation.left.homOfLE (inf_le_right firstIndex secondIndex) := by
    rw [← cancel_mono secondIndex.1.ι, Category.assoc, Scheme.homOfLE_ι, hπ, pullback.condition]
  rw [h1, h2, Category.assoc, Category.assoc, homOfLE_localComparison, homOfLE_localComparison]

end Colimit

section Glue

variable (covering : ∀ point : representation.left, ∃ index : Index datum, point ∈ index.1)

private noncomputable def openCover : representation.left.OpenCover :=
  Scheme.Cover.mkOfCovers (Index datum) (fun index ↦ index.1.toScheme) (fun index ↦ index.1.ι) (fun point ↦ by
    obtain ⟨index, hW⟩ := covering point
    exact ⟨index, ⟨point, hW⟩, rfl⟩)

private noncomputable def comparison : representation.left ⟶ Limits.pullback (gluedHom (datum := datum)) baseMap :=
  (openCover covering).glueMorphisms localComparison localComparison_compat

@[reassoc (attr := simp)]
private lemma ι_comparison (index : Index datum) : index.1.ι ≫ comparison covering = localComparison index :=
  (openCover covering).ι_glueMorphisms localComparison localComparison_compat index

@[reassoc (attr := simp)]
private lemma comparison_snd : comparison covering ≫ pullback.snd gluedHom baseMap = representation.hom := by
  refine (openCover covering).hom_ext _ _ fun index ↦ ?_
  change index.1.ι ≫ comparison covering ≫ _ = index.1.ι ≫ representation.hom
  rw [ι_comparison_assoc, localComparison_snd]

private lemma comparison_apply (index : Index datum) (point : index.1.toScheme) : comparison covering point.1 = localComparison index point := by
  rw [← ι_comparison covering index, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]

private lemma comparison_injective : Function.Injective (comparison covering) := by
  intro point otherPoint huu'
  obtain ⟨index, hW⟩ := covering point
  obtain ⟨largerIndex, hW'⟩ := covering otherPoint
  have point_eq := congrArg (pullback.fst gluedHom baseMap) huu'
  rw [comparison_apply covering index ⟨point, hW⟩, comparison_apply covering largerIndex ⟨otherPoint, hW'⟩, ← Scheme.Hom.comp_apply,
    ← Scheme.Hom.comp_apply, localComparison_fst, localComparison_fst, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at point_eq
  obtain ⟨intermediateIndex, transitionMap, secondTransitionMap, imagePoint, hy, hy'⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (diagram (datum := datum))).mp point_eq
  obtain ⟨pullbackPoint, rfl⟩ := (projection intermediateIndex).surjective imagePoint
  change transition _ (projection intermediateIndex pullbackPoint) = _ at hy
  change transition _ (projection intermediateIndex pullbackPoint) = _ at hy'
  rw [transition_projection_apply] at hy hy'
  have hul : point ∈ intermediateIndex.1 := mem_of_apply_eq_apply (isPullback_projection index) (projection_transport index)
    (isInvariant intermediateIndex) hy.symm (by simp)
  have hul' : otherPoint ∈ intermediateIndex.1 := mem_of_apply_eq_apply (isPullback_projection largerIndex) (projection_transport largerIndex)
    (isInvariant intermediateIndex) hy'.symm (by simp)
  rw [comparison_apply covering intermediateIndex ⟨point, hul⟩, comparison_apply covering intermediateIndex ⟨otherPoint, hul'⟩] at huu'
  exact congrArg Subtype.val ((localComparison intermediateIndex).isOpenEmbedding.injective huu')

private lemma comparison_surjective : Function.Surjective (comparison covering) := by
  intro pullbackPoint
  obtain ⟨index, chartPoint, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diagram (datum := datum))
    (pullback.fst gluedHom baseMap pullbackPoint)
  obtain ⟨pullbackPoint, ht₁, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.fst gluedHom baseMap) (g := colimit.ι (diagram (datum := datum)) index) pullbackPoint chartPoint hx.symm
  refine ⟨((isPullback_localComparison index).isoPullback.inv ≫ index.1.ι) pullbackPoint, ?_⟩
  rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, comparison_apply, ← Scheme.Hom.comp_apply,
    IsPullback.isoPullback_inv_fst, ht₁]

private instance : IsLocalIso (comparison covering) where
  exists_isOpenImmersion point := by
    obtain ⟨index, hW⟩ := covering point
    refine ⟨index.1, hW, ?_⟩
    rw [ι_comparison covering index]
    infer_instance

private instance : IsOpenImmersion (comparison covering) :=
  IsOpenImmersion.of_isLocalIso_of_injective _ (comparison_injective covering)

private instance : IsIso (comparison covering) :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _
    (by ext1; simpa using Set.range_eq_univ.mpr (comparison_surjective covering))

private lemma toHom_comparison_fst :
    datum.toHom ≫ comparison covering ≫ pullback.fst gluedHom baseMap =
      pullback.fst (representation.hom ≫ baseMap) baseMap ≫ comparison covering ≫ pullback.fst gluedHom baseMap := by
  let universalCover : (Limits.pullback (representation.hom ≫ baseMap) baseMap).OpenCover :=
    Scheme.Cover.mkOfCovers (Index datum)
      (fun index ↦ (pullback.fst (representation.hom ≫ baseMap) baseMap ⁻¹ᵁ index.1).toScheme)
      (fun index ↦ (pullback.fst (representation.hom ≫ baseMap) baseMap ⁻¹ᵁ index.1).ι) (fun pullbackPoint ↦ by
        obtain ⟨index, hW⟩ := covering (pullback.fst (representation.hom ≫ baseMap) baseMap pullbackPoint)
        exact ⟨index, ⟨pullbackPoint, hW⟩, rfl⟩)
  refine universalCover.hom_ext _ _ fun index ↦ ?_
  let descendedOpen := pullback.fst (representation.hom ≫ baseMap) baseMap ⁻¹ᵁ index.1
  change descendedOpen.ι ≫ _ = descendedOpen.ι ≫ _
  have hr : Set.range (descendedOpen.ι ≫ pullback.fst (representation.hom ≫ baseMap) baseMap) ⊆ Set.range index.1.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨pullbackPoint, rfl⟩
    exact pullbackPoint.2
  let pointOver : Over.mk (descendedOpen.ι ≫ pullback.fst (representation.hom ≫ baseMap) baseMap ≫ representation.hom) ⟶ Over.mk (index.1.ι ≫ representation.hom) :=
    Over.homMk (IsOpenImmersion.lift index.1.ι _ hr) (by simp)
  have hb : pointOver.left ≫ index.1.ι = descendedOpen.ι ≫ pullback.fst (representation.hom ≫ baseMap) baseMap := IsOpenImmersion.lift_fac _ _ _
  have hp : (descendedOpen.ι ≫ pullback.fst (representation.hom ≫ baseMap) baseMap ≫ representation.hom) ≫ baseMap =
      (descendedOpen.ι ≫ pullback.snd (representation.hom ≫ baseMap) baseMap) ≫ baseMap := by
    simp [pullback.condition]
  have ht : ((datum.restrict index.1 (isInvariant index)).transport _ _ hp pointOver).left ≫ index.1.ι = descendedOpen.ι ≫ datum.toHom := by
    rw [restrict_transport_left_ι, datum.transport_left_eq_lift_toHom]
    congr 1
    apply pullback.hom_ext <;> simp [hb]
  rw [← reassoc_of% ht, ι_comparison_assoc, localComparison_fst, projection_transport_assoc, ← localComparison_fst, ← ι_comparison_assoc covering index,
    reassoc_of% hb]

end Glue

end EffectiveGluing

open EffectiveGluing in
theorem isEffective_of_forall_exists_mem [Flat baseMap] [Surjective baseMap] [QuasiCompact baseMap]
    (covering : ∀ point : representation.left, ∃ (openSubset : representation.left.Opens) (hU : datum.IsInvariant openSubset), point ∈ openSubset ∧
      (datum.restrict openSubset hU).IsEffective) : datum.IsEffective := by
  have h' (point : representation.left) : ∃ index : Index datum, point ∈ index.1 := by
    obtain ⟨openSubset, hU, hv, hE⟩ := covering point
    exact ⟨⟨openSubset, hU, hE⟩, hv⟩
  refine ⟨Over.mk gluedHom, comparison h' ≫ pullback.fst gluedHom baseMap,
    IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ (asIso (comparison h')) rfl (comparison_snd h'),
    fun firstMap secondMap hf point ↦ ?_⟩
  rw [datum.transport_left_eq_lift_toHom, Category.assoc, toHom_comparison_fst h', pullback.lift_fst_assoc]

end CategoryTheory.Over.DescentDatum
