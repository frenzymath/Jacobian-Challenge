import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocusOfRank

/-!
# Universal cohomology rank loci over arbitrary bases

For a proper finitely presented family with finitely presented relatively flat
coefficients, single-degree fibre cohomology of prescribed rank defines an open
subset of the base. A Cartesian base change factors through this subset exactly
when its higher direct images are finite locally free of the prescribed rank
in that degree and zero in all other degrees.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {sourceScheme baseScheme : Scheme.{u}} (sourceMap : sourceScheme ⟶ baseScheme)
  [IsProper sourceMap] [LocallyOfFinitePresentation sourceMap]
  (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsFinitePresentation]
  (flat : moduleSheaf.IsFlatOver sourceMap)

include flat

/-- The fixed-rank single-degree fibre-cohomology locus is open over an
arbitrary base. -/
theorem isOpen_perfectLocusOfRank (degree rank : ℕ) :
    IsOpen (moduleSheaf.perfectLocusOfRank sourceMap degree rank) := by
  refine isOpen_iff_forall_mem_open.mpr fun point membership ↦ ?_
  obtain ⟨modelOpen, complex, bound, point_mem, finiteFree, comparison⟩ :=
    exists_isFiniteFreeComplex_higherDirectImage sourceMap moduleSheaf flat point
  let rankOpen : modelOpen.toScheme.Opens :=
    ⟨homologyRankLocus complex degree rank, finiteFree.isOpen_homologyRankLocus degree rank⟩
  have locusComparison := homologyRankLocus_eq_preimage_perfectLocusOfRank sourceMap moduleSheaf
    finiteFree comparison degree rank
  refine ⟨modelOpen.ι '' (rankOpen : Set modelOpen.toScheme), ?_,
    modelOpen.ι.isOpenMap _ rankOpen.isOpen, ?_⟩
  · rintro imagePoint ⟨localPoint, localMembership, rfl⟩
    exact (Set.ext_iff.mp locusComparison localPoint).mp localMembership
  · exact ⟨⟨point, point_mem⟩,
      (Set.ext_iff.mp locusComparison ⟨point, point_mem⟩).mpr membership, rfl⟩

private theorem exists_mem_isFiniteLocallyFreeInDegree_restrict
    {degree rank : ℕ} {targetScheme pulledScheme : Scheme.{u}}
    (baseChange : targetScheme ⟶ baseScheme) (pullbackMap : pulledScheme ⟶ sourceScheme)
    (pulledMap : pulledScheme ⟶ targetScheme) [HasInjectiveResolutions pulledScheme.Modules]
    (square : IsPullback pullbackMap pulledMap sourceMap baseChange) (point : targetScheme)
    (membership : baseChange point ∈ moduleSheaf.perfectLocusOfRank sourceMap degree rank) :
    ∃ targetOpen : targetScheme.Opens, point ∈ targetOpen ∧
      IsFiniteLocallyFreeInDegree
        (fun homologyDegree ↦ ((higherDirectImage pulledMap homologyDegree).obj
          ((pullback pullbackMap).obj moduleSheaf)).restrict targetOpen.ι) degree rank := by
  obtain ⟨modelOpen, complex, bound, point_mem, finiteFree, comparison⟩ :=
    exists_isFiniteFreeComplex_higherDirectImage sourceMap moduleSheaf flat (baseChange point)
  let rankOpen : modelOpen.toScheme.Opens :=
    ⟨homologyRankLocus complex degree rank, finiteFree.isOpen_homologyRankLocus degree rank⟩
  have locusComparison := homologyRankLocus_eq_preimage_perfectLocusOfRank sourceMap moduleSheaf
    finiteFree comparison degree rank
  let targetOpen := baseChange ⁻¹ᵁ (modelOpen.ι ''ᵁ rankOpen)
  have targetMembership : point ∈ targetOpen :=
    ⟨⟨baseChange point, point_mem⟩,
      (Set.ext_iff.mp locusComparison ⟨baseChange point, point_mem⟩).mpr membership, rfl⟩
  have localRange : Set.range (targetOpen.ι ≫ baseChange) ⊆ Set.range modelOpen.ι := by
    rintro imagePoint ⟨localPoint, rfl⟩
    obtain ⟨modelPoint, _, equality⟩ := localPoint.2
    exact ⟨modelPoint, by simpa using equality⟩
  let localBaseChange := IsOpenImmersion.lift modelOpen.ι (targetOpen.ι ≫ baseChange) localRange
  have factorization : localBaseChange ≫ modelOpen.ι = targetOpen.ι ≫ baseChange :=
    IsOpenImmersion.lift_fac _ _ _
  have rankRange : Set.range localBaseChange ⊆ rankOpen := by
    rintro imagePoint ⟨localPoint, rfl⟩
    obtain ⟨modelPoint, modelMembership, equality⟩ := localPoint.2
    have sameImage : modelOpen.ι (localBaseChange localPoint) = modelOpen.ι modelPoint := by
      rw [← Scheme.Hom.comp_apply, factorization, Scheme.Hom.comp_apply]
      exact equality.symm
    rwa [modelOpen.ι.isOpenEmbedding.injective sameImage]
  have finiteLocallyFree := finiteFree.isFiniteLocallyFreeInDegree_of_range_subset degree rank
    localBaseChange rankRange
  refine ⟨targetOpen, targetMembership, finiteLocallyFree.of_iso fun homologyDegree ↦ ?_⟩
  exact (nonempty_restrict_higherDirectImage_iso_homology sourceMap moduleSheaf comparison
    baseChange pullbackMap pulledMap square targetOpen localBaseChange factorization
      homologyDegree).some.symm

private theorem isFiniteLocallyFreeInDegree_of_range_subset
    {degree rank : ℕ} {targetScheme pulledScheme : Scheme.{u}}
    (baseChange : targetScheme ⟶ baseScheme) (pullbackMap : pulledScheme ⟶ sourceScheme)
    (pulledMap : pulledScheme ⟶ targetScheme) [HasInjectiveResolutions pulledScheme.Modules]
    (square : IsPullback pullbackMap pulledMap sourceMap baseChange)
    (rangeSubset : Set.range baseChange ⊆ moduleSheaf.perfectLocusOfRank sourceMap degree rank) :
    IsFiniteLocallyFreeInDegree (fun homologyDegree ↦ (higherDirectImage pulledMap homologyDegree).obj
      ((pullback pullbackMap).obj moduleSheaf)) degree rank := by
  choose targetOpen point_mem localFreeness using fun point ↦
    exists_mem_isFiniteLocallyFreeInDegree_restrict sourceMap moduleSheaf flat baseChange
      pullbackMap pulledMap square point (rangeSubset ⟨point, rfl⟩)
  refine ⟨fun homologyDegree unequal ↦ ?_, ?_⟩
  · exact isZero_of_forall_exists_isZero_restrict _ fun point ↦
      ⟨targetOpen point, point_mem point, (localFreeness point).isZero homologyDegree unequal⟩
  · exact isFiniteLocallyFreeOfRank_of_iSup_eq_top _ targetOpen
      (eq_top_iff.mpr fun point _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨point, point_mem point⟩)
      fun point ↦ (localFreeness point).isFiniteLocallyFreeOfRank

private theorem range_subset_perfectLocusOfRank_of_isPullback
    {degree rank : ℕ} {targetScheme pulledScheme : Scheme.{u}}
    (baseChange : targetScheme ⟶ baseScheme) (pullbackMap : pulledScheme ⟶ sourceScheme)
    (pulledMap : pulledScheme ⟶ targetScheme) [HasInjectiveResolutions pulledScheme.Modules]
    (square : IsPullback pullbackMap pulledMap sourceMap baseChange)
    (singleDegree : IsFiniteLocallyFreeInDegree (fun homologyDegree ↦
      (higherDirectImage pulledMap homologyDegree).obj ((pullback pullbackMap).obj moduleSheaf))
        degree rank) :
    Set.range baseChange ⊆ moduleSheaf.perfectLocusOfRank sourceMap degree rank := by
  rintro imagePoint ⟨point, rfl⟩
  obtain ⟨modelOpen, complex, bound, point_mem, finiteFree, comparison⟩ :=
    exists_isFiniteFreeComplex_higherDirectImage sourceMap moduleSheaf flat (baseChange point)
  let targetOpen := baseChange ⁻¹ᵁ modelOpen
  have localRange : Set.range (targetOpen.ι ≫ baseChange) ⊆ Set.range modelOpen.ι := by
    rintro localImage ⟨localPoint, rfl⟩
    exact ⟨⟨_, localPoint.2⟩, rfl⟩
  let localBaseChange := IsOpenImmersion.lift modelOpen.ι (targetOpen.ι ≫ baseChange) localRange
  have factorization : localBaseChange ≫ modelOpen.ι = targetOpen.ι ≫ baseChange :=
    IsOpenImmersion.lift_fac _ _ _
  let homologyComparison (homologyDegree : ℕ) :=
    (nonempty_restrict_higherDirectImage_iso_homology sourceMap moduleSheaf comparison
      baseChange pullbackMap pulledMap square targetOpen localBaseChange factorization
        homologyDegree).some
  letI := singleDegree.isFiniteLocallyFreeOfRank
  have localCondition : IsFiniteLocallyFreeInDegree (fun homologyDegree : ℕ ↦
      (((pullback localBaseChange).mapHomologicalComplex _).obj complex).homology homologyDegree)
        degree rank :=
    ⟨fun homologyDegree unequal ↦ ((restrictFunctor targetOpen.ι).map_isZero
      (singleDegree.isZero homologyDegree unequal)).of_iso (homologyComparison homologyDegree).symm,
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (homologyComparison degree)⟩
  have rankMembership := finiteFree.range_subset_homologyRankLocus degree rank localBaseChange
    localCondition ⟨⟨point, point_mem⟩, rfl⟩
  have locusComparison := homologyRankLocus_eq_preimage_perfectLocusOfRank sourceMap moduleSheaf
    finiteFree comparison degree rank
  have membership := (Set.ext_iff.mp locusComparison (localBaseChange ⟨point, point_mem⟩)).mp
    rankMembership
  change modelOpen.ι (localBaseChange ⟨point, point_mem⟩) ∈
    moduleSheaf.perfectLocusOfRank sourceMap degree rank at membership
  have imageEquation : modelOpen.ι (localBaseChange ⟨point, point_mem⟩) = baseChange point := by
    rw [← Scheme.Hom.comp_apply, factorization, Scheme.Hom.comp_apply]
    rfl
  rwa [imageEquation] at membership

/-- A proper finitely presented family with finitely presented relatively flat
coefficients has a universal open single-degree cohomology locus of every rank.
In degree zero and rank one, the right side is invertibility of the direct
image together with vanishing of every positive higher direct image. -/
theorem exists_opens_range_subset_iff_isFiniteLocallyFreeInDegree (degree rank : ℕ) :
    ∃ openSubset : baseScheme.Opens,
      (openSubset : Set baseScheme) = moduleSheaf.perfectLocusOfRank sourceMap degree rank ∧
      ∀ {targetScheme pulledScheme : Scheme.{u}}
        (baseChange : targetScheme ⟶ baseScheme) (pullbackMap : pulledScheme ⟶ sourceScheme)
        (pulledMap : pulledScheme ⟶ targetScheme) [HasInjectiveResolutions pulledScheme.Modules],
        IsPullback pullbackMap pulledMap sourceMap baseChange →
        (Set.range baseChange ⊆ openSubset ↔
          IsFiniteLocallyFreeInDegree (fun homologyDegree ↦
            (higherDirectImage pulledMap homologyDegree).obj ((pullback pullbackMap).obj moduleSheaf))
            degree rank) := by
  refine ⟨⟨_, isOpen_perfectLocusOfRank sourceMap moduleSheaf flat degree rank⟩, rfl,
    fun baseChange pullbackMap pulledMap _ square ↦ ?_⟩
  exact ⟨isFiniteLocallyFreeInDegree_of_range_subset sourceMap moduleSheaf flat
    baseChange pullbackMap pulledMap square,
    range_subset_perfectLocusOfRank_of_isPullback sourceMap moduleSheaf flat
      baseChange pullbackMap pulledMap square⟩

end AlgebraicGeometry.Scheme.Modules
