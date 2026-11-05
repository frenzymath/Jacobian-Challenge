import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Pushouts of open immersions

Schemes glue along a common open subscheme. The two charts cover the pushout,
Cartesian maps of gluing data induce Cartesian chart squares, and a
quasi-compact common open preserves quasi-separatedness. A two-open cover of
a scheme gives such a pushout presentation.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {intersectionScheme firstScheme secondScheme : Scheme.{schemeUniverse}} (firstMap :
  intersectionScheme ⟶ firstScheme) (secondMap : intersectionScheme ⟶ secondScheme) [IsOpenImmersion
  firstMap] [IsOpenImmersion secondMap]

/-- Every arrow of the span of two open immersions is an open immersion: the two
non-identity arrows are `firstMap` and `secondMap` themselves. This is what makes the span a locally
directed diagram, hence gluable. -/
instance IsOpenImmersion.span_map : ∀ {spanIndex spanTarget : WalkingSpan} (spanArrow : spanIndex ⟶
  spanTarget),
    IsOpenImmersion ((span firstMap secondMap).map spanArrow)
  | _, _, .id _ => by rw [span_map_id]; infer_instance
  | _, _, .init WalkingPair.left => inferInstanceAs (IsOpenImmersion firstMap)
  | _, _, .init WalkingPair.right => inferInstanceAs (IsOpenImmersion secondMap)

/-- The pushout of two open immersions of schemes with common source exists: the span
is a locally directed diagram of open immersions, glued by
`AlgebraicGeometry.Scheme.IsLocallyDirected`. -/
instance IsOpenImmersion.hasPushout : HasPushout firstMap secondMap :=
  inferInstanceAs (HasColimit (span firstMap secondMap))

instance : IsOpenImmersion (pushout.inl firstMap secondMap) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span firstMap secondMap) WalkingSpan.left))

instance : IsOpenImmersion (pushout.inr firstMap secondMap) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span firstMap secondMap) WalkingSpan.right))

/-- The two charts of the pushout of two open immersions cover the pushout. -/
lemma range_pushout_inl_union_range_pushout_inr :
    Set.range (pushout.inl firstMap secondMap) ∪ Set.range (pushout.inr firstMap secondMap) = Set.univ
      := by
  rw [Set.eq_univ_iff_forall]
  intro gluedPoint
  obtain ⟨spanIndex, chartPoint, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span firstMap
    secondMap) gluedPoint
  match spanIndex, chartPoint with
  | .left, chartPoint => exact Or.inl ⟨chartPoint, rfl⟩
  | .right, chartPoint => exact Or.inr ⟨chartPoint, rfl⟩
  | .zero, chartPoint =>
    refine Or.inl ⟨firstMap chartPoint, ?_⟩
    calc pushout.inl firstMap secondMap (firstMap chartPoint)
        = ((span firstMap secondMap).map WalkingSpan.Hom.fst ≫ colimit.ι (span firstMap secondMap)
          WalkingSpan.left) chartPoint :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = colimit.ι (span firstMap secondMap) WalkingSpan.zero chartPoint := by
          rw [colimit.w (span firstMap secondMap) WalkingSpan.Hom.fst]

instance [CompactSpace firstScheme] [CompactSpace secondScheme] : CompactSpace ↑(pushout firstMap
  secondMap) := by
  constructor
  rw [← range_pushout_inl_union_range_pushout_inr firstMap secondMap]
  exact (isCompact_range (pushout.inl firstMap secondMap).continuous).union
    (isCompact_range (pushout.inr firstMap secondMap).continuous)

/-- The two charts `firstScheme` and `secondScheme` as an open cover of the pushout `firstScheme ⊔_U
  secondScheme`. -/
@[simps! I₀ X f]
def IsOpenImmersion.pushoutCover : (pushout firstMap secondMap).OpenCover :=
  Scheme.Cover.mkOfCovers WalkingPair (fun spanTarget ↦ WalkingPair.casesOn spanTarget firstScheme
    secondScheme)
    (fun spanTarget ↦ WalkingPair.casesOn spanTarget (pushout.inl firstMap secondMap) (pushout.inr
      firstMap secondMap))
    (fun gluedPoint ↦ by
      have hx : gluedPoint ∈ Set.range (pushout.inl firstMap secondMap) ∪ Set.range (pushout.inr firstMap
        secondMap) := by
        rw [range_pushout_inl_union_range_pushout_inr firstMap secondMap]
        trivial
      obtain ⟨chartPoint, hy⟩ | ⟨chartPoint, hy⟩ := hx
      exacts [⟨WalkingPair.left, chartPoint, hy⟩, ⟨WalkingPair.right, chartPoint, hy⟩])
    (fun spanTarget ↦ by cases spanTarget <;> infer_instance)

/-- **Source-local properties descend to a pushout of open immersions**: if `property` is
Zariski-local on the source and holds for `firstStructure : firstScheme ⟶ targetScheme` and
  `secondStructure : secondScheme ⟶ targetScheme`, then it holds
for the glued morphism `pushout.desc firstStructure secondStructure compatible : firstScheme ⊔_U
  secondScheme ⟶ targetScheme`. -/
lemma IsZariskiLocalAtSource.pushout_desc {property : MorphismProperty Scheme.{schemeUniverse}}
    [IsZariskiLocalAtSource property] {targetScheme : Scheme.{schemeUniverse}} {firstStructure :
      firstScheme ⟶ targetScheme} {secondStructure : secondScheme ⟶ targetScheme}
    (compatible : firstMap ≫ firstStructure = secondMap ≫ secondStructure) (hh : property firstStructure)
      (hk : property secondStructure) : property (pushout.desc firstStructure secondStructure compatible)
      := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := property) (IsOpenImmersion.pushoutCover firstMap
    secondMap)]
  intro spanIndex
  cases spanIndex with
  | left => simpa only [IsOpenImmersion.pushoutCover_f, pushout.inl_desc] using hh
  | right => simpa only [IsOpenImmersion.pushoutCover_f, pushout.inr_desc] using hk


section PointsAndMap

/-!
### Points of the pushout, and morphisms of pushouts

The point-level description of the glued scheme: `inl firstPoint = inr secondPoint` if and only if
  `firstPoint` and
`secondPoint` have a common preimage in `intersectionScheme`. From this we deduce that the preimage of
  one chart
under the other chart's inclusion is exactly the image of `intersectionScheme`, and that for a morphism
of spans of open immersions with one cartesian component square, the corresponding
component square of the induced morphism of pushouts is cartesian as well.
-/

lemma pushout_inl_eq_inr_iff (firstPoint : firstScheme) (secondPoint : secondScheme) :
    pushout.inl firstMap secondMap firstPoint = pushout.inr firstMap secondMap secondPoint ↔ ∃
      intersectionPoint : intersectionScheme, firstMap intersectionPoint = firstPoint ∧ secondMap
      intersectionPoint = secondPoint := by
  rw [show pushout.inl firstMap secondMap firstPoint = pushout.inr firstMap secondMap secondPoint ↔
      colimit.ι (span firstMap secondMap) WalkingSpan.left firstPoint = colimit.ι (span firstMap
        secondMap) WalkingSpan.right secondPoint from
    Iff.rfl, Scheme.IsLocallyDirected.ι_eq_ι_iff]
  constructor
  · rintro ⟨spanIndex, toFirst, toSecond, intersectionPoint, hx, hy⟩
    obtain (_ | ⟨_ | _⟩) := spanIndex
    · rw [Subsingleton.elim toFirst WalkingSpan.Hom.fst] at hx
      rw [Subsingleton.elim toSecond WalkingSpan.Hom.snd] at hy
      exact ⟨intersectionPoint, hx, hy⟩
    · exact nomatch toSecond
    · exact nomatch toFirst
  · rintro ⟨intersectionPoint, hx, hy⟩
    exact ⟨WalkingSpan.zero, WalkingSpan.Hom.fst, WalkingSpan.Hom.snd, intersectionPoint, hx, hy⟩

lemma opensRange_pushout_inl_sup_opensRange_pushout_inr :
    (pushout.inl firstMap secondMap).opensRange ⊔ (pushout.inr firstMap secondMap).opensRange = ⊤ := by
  rw [eq_top_iff]
  rintro firstPoint -
  rw [TopologicalSpace.Opens.mem_sup]
  exact Set.eq_univ_iff_forall.mp (range_pushout_inl_union_range_pushout_inr firstMap secondMap)
    firstPoint

lemma preimage_opensRange_pushout_inl :
    pushout.inr firstMap secondMap ⁻¹ᵁ (pushout.inl firstMap secondMap).opensRange = secondMap.opensRange
      := by
  ext targetPoint
  constructor
  · rintro ⟨secondPoint, hy⟩
    obtain ⟨intersectionPoint, -, rfl⟩ := (pushout_inl_eq_inr_iff firstMap secondMap secondPoint
      targetPoint).mp hy
    exact ⟨intersectionPoint, rfl⟩
  · rintro ⟨intersectionPoint, rfl⟩
    exact ⟨firstMap intersectionPoint, (pushout_inl_eq_inr_iff firstMap secondMap _ _).mpr
      ⟨intersectionPoint, rfl, rfl⟩⟩

lemma preimage_opensRange_pushout_inr :
    pushout.inl firstMap secondMap ⁻¹ᵁ (pushout.inr firstMap secondMap).opensRange = firstMap.opensRange
      := by
  ext secondPoint
  constructor
  · rintro ⟨targetPoint, hz⟩
    obtain ⟨intersectionPoint, rfl, -⟩ := (pushout_inl_eq_inr_iff firstMap secondMap secondPoint
      targetPoint).mp hz.symm
    exact ⟨intersectionPoint, rfl⟩
  · rintro ⟨intersectionPoint, rfl⟩
    exact ⟨secondMap intersectionPoint, ((pushout_inl_eq_inr_iff firstMap secondMap _ _).mpr
      ⟨intersectionPoint, rfl, rfl⟩).symm⟩

variable {sourceIntersection sourceFirstScheme sourceSecondScheme : Scheme.{schemeUniverse}}
  (sourceFirstMap : sourceIntersection ⟶ sourceFirstScheme) (sourceSecondMap : sourceIntersection ⟶
  sourceSecondScheme)
  [IsOpenImmersion sourceFirstMap] [IsOpenImmersion sourceSecondMap]
  (firstComparison : sourceFirstScheme ⟶ firstScheme) (secondComparison : sourceSecondScheme ⟶
    secondScheme) (intersectionComparison : sourceIntersection ⟶ intersectionScheme)
  (hf : intersectionComparison ≫ firstMap = sourceFirstMap ≫ firstComparison) (hg :
    intersectionComparison ≫ secondMap = sourceSecondMap ≫ secondComparison)

include hf hg in
lemma preimage_opensRange_pushout_inl_of_isPullback (square : IsPullback intersectionComparison
    sourceSecondMap secondMap secondComparison) :
    pushout.map sourceFirstMap sourceSecondMap firstMap secondMap firstComparison secondComparison
      intersectionComparison hf.symm hg.symm ⁻¹ᵁ (pushout.inl firstMap secondMap).opensRange =
      (pushout.inl sourceFirstMap sourceSecondMap).opensRange := by
  apply le_antisymm
  · rintro gluedPoint hp
    have : gluedPoint ∈ (pushout.inl sourceFirstMap sourceSecondMap).opensRange ⊔ (pushout.inr
      sourceFirstMap sourceSecondMap).opensRange := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]; trivial
    obtain (hmem | ⟨sourceSecondPoint, rfl⟩) := this
    · exact hmem
    · replace hp : (pushout.inr sourceFirstMap sourceSecondMap ≫ pushout.map sourceFirstMap
      sourceSecondMap firstMap secondMap firstComparison secondComparison intersectionComparison hf.symm
      hg.symm) sourceSecondPoint ∈
          (pushout.inl firstMap secondMap).opensRange := by rwa [Scheme.Hom.comp_apply]
      rw [pushout.inr_desc] at hp
      obtain ⟨secondPoint, hy⟩ := hp
      obtain ⟨intersectionPoint, -, hu⟩ := (pushout_inl_eq_inr_iff firstMap secondMap secondPoint
        (secondComparison sourceSecondPoint)).mp
        (by rwa [Scheme.Hom.comp_apply] at hy)
      obtain ⟨sourceIntersectionPoint, -, rfl⟩ := Scheme.exists_preimage_of_isPullback square
        intersectionPoint sourceSecondPoint hu
      change pushout.inr sourceFirstMap sourceSecondMap (sourceSecondMap sourceIntersectionPoint) ∈
        (pushout.inl sourceFirstMap sourceSecondMap).opensRange
      exact ⟨sourceFirstMap sourceIntersectionPoint, (pushout_inl_eq_inr_iff sourceFirstMap
        sourceSecondMap _ _).mpr ⟨sourceIntersectionPoint, rfl, rfl⟩⟩
  · rintro gluedPoint ⟨sourceFirstPoint, rfl⟩
    change (pushout.inl sourceFirstMap sourceSecondMap ≫ pushout.map sourceFirstMap sourceSecondMap
      firstMap secondMap firstComparison secondComparison intersectionComparison hf.symm hg.symm)
      sourceFirstPoint ∈
      (pushout.inl firstMap secondMap).opensRange
    rw [pushout.inl_desc, Scheme.Hom.comp_apply]
    exact ⟨firstComparison sourceFirstPoint, rfl⟩

include hf hg in
/-- Given a morphism of spans of open immersions whose `secondScheme`-component square is cartesian,
the `firstScheme`-component square of the induced morphism of pushouts is cartesian. -/
lemma isPullback_pushout_map_inl_of_isPullback (square : IsPullback intersectionComparison
    sourceSecondMap secondMap secondComparison) :
    IsPullback firstComparison (pushout.inl sourceFirstMap sourceSecondMap) (pushout.inl firstMap
      secondMap)
      (pushout.map sourceFirstMap sourceSecondMap firstMap secondMap firstComparison secondComparison
        intersectionComparison hf.symm hg.symm) :=
  IsOpenImmersion.isPullback _ _ _ _ (pushout.inl_desc _ _ _)
    (preimage_opensRange_pushout_inl_of_isPullback firstMap secondMap sourceFirstMap sourceSecondMap
      firstComparison secondComparison intersectionComparison hf hg square)

include hf hg in
lemma preimage_opensRange_pushout_inr_of_isPullback (square : IsPullback intersectionComparison
    sourceFirstMap firstMap firstComparison) :
    pushout.map sourceFirstMap sourceSecondMap firstMap secondMap firstComparison secondComparison
      intersectionComparison hf.symm hg.symm ⁻¹ᵁ (pushout.inr firstMap secondMap).opensRange =
      (pushout.inr sourceFirstMap sourceSecondMap).opensRange := by
  apply le_antisymm
  · rintro gluedPoint hp
    have : gluedPoint ∈ (pushout.inl sourceFirstMap sourceSecondMap).opensRange ⊔ (pushout.inr
      sourceFirstMap sourceSecondMap).opensRange := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]; trivial
    obtain (⟨sourceFirstPoint, rfl⟩ | hmem) := this
    · replace hp : (pushout.inl sourceFirstMap sourceSecondMap ≫ pushout.map sourceFirstMap
      sourceSecondMap firstMap secondMap firstComparison secondComparison intersectionComparison hf.symm
      hg.symm) sourceFirstPoint ∈
          (pushout.inr firstMap secondMap).opensRange := by rwa [Scheme.Hom.comp_apply]
      rw [pushout.inl_desc] at hp
      obtain ⟨secondPoint, hz⟩ := hp
      obtain ⟨intersectionPoint, hu, -⟩ := (pushout_inl_eq_inr_iff firstMap secondMap (firstComparison
        sourceFirstPoint) secondPoint).mp
        (by rw [Scheme.Hom.comp_apply] at hz; exact hz.symm)
      obtain ⟨sourceIntersectionPoint, -, rfl⟩ := Scheme.exists_preimage_of_isPullback square
        intersectionPoint sourceFirstPoint hu
      change pushout.inl sourceFirstMap sourceSecondMap (sourceFirstMap sourceIntersectionPoint) ∈
        (pushout.inr sourceFirstMap sourceSecondMap).opensRange
      exact ⟨sourceSecondMap sourceIntersectionPoint, ((pushout_inl_eq_inr_iff sourceFirstMap
        sourceSecondMap _ _).mpr ⟨sourceIntersectionPoint, rfl, rfl⟩).symm⟩
    · exact hmem
  · rintro gluedPoint ⟨sourceSecondPoint, rfl⟩
    change (pushout.inr sourceFirstMap sourceSecondMap ≫ pushout.map sourceFirstMap sourceSecondMap
      firstMap secondMap firstComparison secondComparison intersectionComparison hf.symm hg.symm)
      sourceSecondPoint ∈
      (pushout.inr firstMap secondMap).opensRange
    rw [pushout.inr_desc, Scheme.Hom.comp_apply]
    exact ⟨secondComparison sourceSecondPoint, rfl⟩

include hf hg in
/-- Given a morphism of spans of open immersions whose `firstScheme`-component square is cartesian,
the `secondScheme`-component square of the induced morphism of pushouts is cartesian. -/
lemma isPullback_pushout_map_inr_of_isPullback (square : IsPullback intersectionComparison sourceFirstMap
    firstMap firstComparison) :
    IsPullback secondComparison (pushout.inr sourceFirstMap sourceSecondMap) (pushout.inr firstMap
      secondMap)
      (pushout.map sourceFirstMap sourceSecondMap firstMap secondMap firstComparison secondComparison
        intersectionComparison hf.symm hg.symm) :=
  IsOpenImmersion.isPullback _ _ _ _ (pushout.inr_desc _ _ _)
    (preimage_opensRange_pushout_inr_of_isPullback firstMap secondMap sourceFirstMap sourceSecondMap
      firstComparison secondComparison intersectionComparison hf hg square)

end PointsAndMap

section QuasiSeparated

lemma image_inl_inter_image_inr (firstSubset : Set firstScheme) (secondSubset : Set secondScheme) :
    (pushout.inl firstMap secondMap '' firstSubset) ∩ (pushout.inr firstMap secondMap '' secondSubset) =
      pushout.inl firstMap secondMap '' (firstSubset ∩ firstMap '' (secondMap ⁻¹' secondSubset)) := by
  apply subset_antisymm
  · rintro - ⟨⟨firstPoint, hx, rfl⟩, ⟨secondPoint, hy, hxy⟩⟩
    obtain ⟨intersectionPoint, hu, rfl⟩ := (pushout_inl_eq_inr_iff firstMap secondMap firstPoint
      secondPoint).mp hxy.symm
    exact ⟨firstPoint, ⟨hx, ⟨intersectionPoint, hy, hu⟩⟩, rfl⟩
  · rintro - ⟨firstPoint, ⟨hx, ⟨intersectionPoint, hu, rfl⟩⟩, rfl⟩
    exact ⟨⟨firstMap intersectionPoint, hx, rfl⟩, ⟨secondMap intersectionPoint, hu,
      ((pushout_inl_eq_inr_iff firstMap secondMap _ _).mpr ⟨intersectionPoint, rfl, rfl⟩).symm⟩⟩

/-- **The pushout of two quasi-separated schemes along a quasi-compact common open is
quasi-separated.** -/
lemma quasiSeparatedSpace_pushout [QuasiSeparatedSpace firstScheme] [QuasiSeparatedSpace secondScheme]
    [CompactSpace intersectionScheme] : QuasiSeparatedSpace ↑(pushout firstMap secondMap) := by
  have hgc : IsCompact (Set.range secondMap) := isCompact_range secondMap.continuous

  have key : ∀ (firstSubset : Set firstScheme) (secondSubset : Set secondScheme), IsOpen firstSubset →
    IsCompact firstSubset → IsOpen secondSubset → IsCompact secondSubset →
      IsCompact ((pushout.inl firstMap secondMap '' firstSubset) ∩ (pushout.inr firstMap secondMap ''
        secondSubset)) := by
    intro firstSubset secondSubset hAo hAc hBo hBc
    rw [image_inl_inter_image_inr]
    refine IsCompact.image ?_ (pushout.inl firstMap secondMap).continuous
    have preimage_compact : IsCompact (secondMap ⁻¹' secondSubset) := by
      have he : secondMap ⁻¹' secondSubset = secondMap ⁻¹' (secondSubset ∩ Set.range secondMap) := by
        rw [Set.preimage_inter, Set.preimage_range, Set.inter_univ]
      rw [he]
      exact secondMap.isOpenEmbedding.isInducing.isCompact_preimage'
        (hBc.inter_of_isOpen hgc hBo secondMap.isOpenEmbedding.isOpen_range) Set.inter_subset_right
    exact hAc.inter_of_isOpen (preimage_compact.image firstMap.continuous) hAo
      (firstMap.isOpenEmbedding.isOpenMap _ (hBo.preimage secondMap.continuous))
  refine QuasiSeparatedSpace.of_isTopologicalBasis
    (b := fun chartIndex : {firstSubset : firstScheme.Opens // IsCompact (firstSubset : Set firstScheme)}
      ⊕
      {secondSubset : secondScheme.Opens // IsCompact (secondSubset : Set secondScheme)} ↦
      match chartIndex with
      | Sum.inl firstSubset => pushout.inl firstMap secondMap '' (firstSubset.1 : Set firstScheme)
      | Sum.inr secondSubset => pushout.inr firstMap secondMap '' (secondSubset.1 : Set secondScheme))
    ?_ ?_
  · refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro - ⟨(⟨firstSubset, hA⟩ | ⟨secondSubset, hB⟩), rfl⟩
      · exact (pushout.inl firstMap secondMap).isOpenEmbedding.isOpenMap _ firstSubset.2
      · exact (pushout.inr firstMap secondMap).isOpenEmbedding.isOpenMap _ secondSubset.2
    · intro gluedPoint neighborhood hp hO
      have hcov : gluedPoint ∈ Set.range (pushout.inl firstMap secondMap) ∪ Set.range (pushout.inr
        firstMap secondMap) := by
        rw [range_pushout_inl_union_range_pushout_inr firstMap secondMap]; trivial
      obtain (⟨firstPoint, rfl⟩ | ⟨secondPoint, rfl⟩) := hcov
      · have hmem : firstPoint ∈ (⟨_, hO.preimage (pushout.inl firstMap secondMap).continuous⟩ :
        firstScheme.Opens) := hp
        obtain ⟨A₀, hA₀, hxA, hAO⟩ :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp firstScheme.isBasis_affineOpens hmem
        exact ⟨_, ⟨Sum.inl ⟨A₀, hA₀.isCompact⟩, rfl⟩, ⟨firstPoint, hxA, rfl⟩,
          Set.image_subset_iff.mpr hAO⟩
      · have hmem : secondPoint ∈ (⟨_, hO.preimage (pushout.inr firstMap secondMap).continuous⟩ :
        secondScheme.Opens) := hp
        obtain ⟨B₀, hB₀, hyB, hBO⟩ :=
          TopologicalSpace.Opens.isBasis_iff_nbhd.mp secondScheme.isBasis_affineOpens hmem
        exact ⟨_, ⟨Sum.inr ⟨B₀, hB₀.isCompact⟩, rfl⟩, ⟨secondPoint, hyB, rfl⟩,
          Set.image_subset_iff.mpr hBO⟩
  · rintro (⟨firstSubset, hA⟩ | ⟨secondSubset, hB⟩) (⟨otherFirstOpen, hA'⟩ | ⟨otherSecondOpen, hB'⟩)
    · rw [← Set.image_inter (pushout.inl firstMap secondMap).isOpenEmbedding.injective]
      exact (hA.inter_of_isOpen hA' firstSubset.2 otherFirstOpen.2).image (pushout.inl firstMap
        secondMap).continuous
    · exact key _ _ firstSubset.2 hA otherSecondOpen.2 hB'
    · rw [Set.inter_comm]
      exact key _ _ otherFirstOpen.2 hA' secondSubset.2 hB
    · rw [← Set.image_inter (pushout.inr firstMap secondMap).isOpenEmbedding.injective]
      exact (hB.inter_of_isOpen hB' secondSubset.2 otherSecondOpen.2).image (pushout.inr firstMap
        secondMap).continuous

end QuasiSeparated

section TwoOpens

variable {ambientScheme : Scheme.{schemeUniverse}} (firstOpen secondOpen : ambientScheme.Opens)

/-- The morphism from the pushout of two opens of `ambientScheme` along their intersection to
  `ambientScheme`. -/
def pushoutOpensDesc :
    pushout ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)))
      ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen))) ⟶ ambientScheme :=
  pushout.desc firstOpen.ι secondOpen.ι (by simp)

@[reassoc (attr := simp)]
lemma inl_pushoutOpensDesc :
    pushout.inl ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)))
      ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen))) ≫
      pushoutOpensDesc firstOpen secondOpen = firstOpen.ι :=
  pushout.inl_desc ..

@[reassoc (attr := simp)]
lemma inr_pushoutOpensDesc :
    pushout.inr ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)))
      ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen))) ≫
      pushoutOpensDesc firstOpen secondOpen = secondOpen.ι :=
  pushout.inr_desc ..

lemma preimage_opensRange_inl_pushoutOpensDesc :
    pushoutOpensDesc firstOpen secondOpen ⁻¹ᵁ firstOpen.ι.opensRange =
      (pushout.inl ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)))
        ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)))).opensRange := by
  apply le_antisymm
  · intro gluedPoint hx
    have hcov : gluedPoint ∈ (pushout.inl ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤
      firstOpen)))
        ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)))).opensRange ⊔
        (pushout.inr ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)))
          ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)))).opensRange
          := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]; trivial
    obtain (hmem | ⟨secondPoint, rfl⟩) := hcov
    · exact hmem
    · replace hx : (pushout.inr ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤
      firstOpen))) ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen))) ≫
          pushoutOpensDesc firstOpen secondOpen) secondPoint ∈ firstOpen.ι.opensRange := hx
      rw [inr_pushoutOpensDesc] at hx
      obtain ⟨firstPoint, hu⟩ := hx
      change secondPoint ∈ pushout.inr ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤
        firstOpen))) ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen))) ⁻¹ᵁ
        (pushout.inl ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)))
          ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)))).opensRange
      rw [preimage_opensRange_pushout_inl, Scheme.opensRange_homOfLE]
      exact ⟨show secondOpen.ι secondPoint ∈ firstOpen from hu ▸ firstPoint.2, secondPoint.2⟩
  · rintro gluedPoint ⟨firstPoint, rfl⟩
    change (pushout.inl ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)))
      ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen))) ≫
      pushoutOpensDesc firstOpen secondOpen) firstPoint ∈ firstOpen.ι.opensRange
    rw [inl_pushoutOpensDesc]
    exact ⟨firstPoint, rfl⟩

lemma preimage_opensRange_inr_pushoutOpensDesc :
    pushoutOpensDesc firstOpen secondOpen ⁻¹ᵁ secondOpen.ι.opensRange =
      (pushout.inr ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)))
        ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)))).opensRange := by
  apply le_antisymm
  · intro gluedPoint hx
    have hcov : gluedPoint ∈ (pushout.inl ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤
      firstOpen)))
        ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)))).opensRange ⊔
        (pushout.inr ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)))
          ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)))).opensRange
          := by
      rw [opensRange_pushout_inl_sup_opensRange_pushout_inr]; trivial
    obtain (⟨firstPoint, rfl⟩ | hmem) := hcov
    · replace hx : (pushout.inl ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤
      firstOpen))) ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen))) ≫
          pushoutOpensDesc firstOpen secondOpen) firstPoint ∈ secondOpen.ι.opensRange := hx
      rw [inl_pushoutOpensDesc] at hx
      obtain ⟨secondPoint, hv⟩ := hx
      change firstPoint ∈ pushout.inl ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤
        firstOpen))) ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen))) ⁻¹ᵁ
        (pushout.inr ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)))
          ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)))).opensRange
      rw [preimage_opensRange_pushout_inr, Scheme.opensRange_homOfLE]
      exact ⟨firstPoint.2, show firstOpen.ι firstPoint ∈ secondOpen from hv ▸ secondPoint.2⟩
    · exact hmem
  · rintro gluedPoint ⟨secondPoint, rfl⟩
    change (pushout.inr ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)))
      ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen))) ≫
      pushoutOpensDesc firstOpen secondOpen) secondPoint ∈ secondOpen.ι.opensRange
    rw [inr_pushoutOpensDesc]
    exact ⟨secondPoint, rfl⟩

/-- The first chart of the pushout presentation of a two-open cover is cartesian. -/
lemma isPullback_inl_pushoutOpensDesc :
    IsPullback (𝟙 firstOpen.toScheme)
      (pushout.inl ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)))
        ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)))) firstOpen.ι
      (pushoutOpensDesc firstOpen secondOpen) :=
  IsOpenImmersion.isPullback _ _ _ _ (by simp) (preimage_opensRange_inl_pushoutOpensDesc firstOpen
    secondOpen)

/-- The second chart of the pushout presentation of a two-open cover is cartesian. -/
lemma isPullback_inr_pushoutOpensDesc :
    IsPullback (𝟙 secondOpen.toScheme)
      (pushout.inr ((ambientScheme.homOfLE (inf_le_left : firstOpen ⊓ secondOpen ≤ firstOpen)))
        ((ambientScheme.homOfLE (inf_le_right : firstOpen ⊓ secondOpen ≤ secondOpen)))) secondOpen.ι
      (pushoutOpensDesc firstOpen secondOpen) :=
  IsOpenImmersion.isPullback _ _ _ _ (by simp) (preimage_opensRange_inr_pushoutOpensDesc firstOpen
    secondOpen)

/-- **A scheme covered by two open subschemes is the pushout of the two along their
intersection.** -/
lemma isIso_pushoutOpensDesc (hUV : firstOpen ⊔ secondOpen = ⊤) : IsIso (pushoutOpensDesc firstOpen
    secondOpen) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_openCover
    (ambientScheme.openCoverOfIsOpenCover (fun chartIndex : Bool ↦ cond chartIndex firstOpen secondOpen)
      ?_) fun chartIndex ↦ ?_
  · change iSup _ = ⊤
    rw [iSup_bool_eq]
    exact hUV
  · rw [MorphismProperty.isomorphisms.iff]
    match chartIndex with
    | true =>
      change IsIso (pullback.snd (pushoutOpensDesc firstOpen secondOpen) firstOpen.ι)
      have square := (isPullback_inl_pushoutOpensDesc firstOpen secondOpen).flip
      have projection_eq : pullback.snd (pushoutOpensDesc firstOpen secondOpen) firstOpen.ι =
        square.isoPullback.inv := by
        rw [← Category.id_comp (pullback.snd (pushoutOpensDesc firstOpen secondOpen) firstOpen.ι),
          ← square.isoPullback.inv_hom_id, Category.assoc, IsPullback.isoPullback_hom_snd,
          Category.comp_id]
      rw [projection_eq]; infer_instance
    | false =>
      change IsIso (pullback.snd (pushoutOpensDesc firstOpen secondOpen) secondOpen.ι)
      have square := (isPullback_inr_pushoutOpensDesc firstOpen secondOpen).flip
      have projection_eq : pullback.snd (pushoutOpensDesc firstOpen secondOpen) secondOpen.ι =
        square.isoPullback.inv := by
        rw [← Category.id_comp (pullback.snd (pushoutOpensDesc firstOpen secondOpen) secondOpen.ι),
          ← square.isoPullback.inv_hom_id, Category.assoc, IsPullback.isoPullback_hom_snd,
          Category.comp_id]
      rw [projection_eq]; infer_instance

end TwoOpens

end AlgebraicGeometry
