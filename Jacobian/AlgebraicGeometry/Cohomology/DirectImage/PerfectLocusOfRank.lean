import Jacobian.AlgebraicGeometry.Cohomology.PerfectLocus
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeModelBaseChange
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Restrict
import Jacobian.AlgebraicGeometry.Modules.FiniteFreeComplexRank

/-!
# Fixed-rank cohomology loci over Noetherian spectra

For a proper family over a Noetherian spectrum with finitely presented flat
coefficients, the locus where fibre cohomology is concentrated in one degree
with prescribed dimension is open. Every base change into this locus has
finite locally free higher direct image of that rank in the specified degree
and zero higher direct images in the other degrees.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {baseScheme sourceScheme : Scheme.{u}}

/-- A field-valued point detects the rank locus through the dimensions of the
homology of the pulled-back complex. -/
lemma IsFiniteFreeComplex.mem_homologyRankLocus_iff_finrank_pullback
    {complex : CochainComplex baseScheme.Modules ℤ} {bound : ℕ}
    (finiteFree : IsFiniteFreeComplex complex bound) {fieldRing : CommRingCat.{u}}
    (field : IsField fieldRing) (baseChange : Spec fieldRing ⟶ baseScheme)
    (point : Spec fieldRing) (degree rank : ℕ) :
    baseChange point ∈ homologyRankLocus complex degree rank ↔
      ∀ homologyDegree : ℤ, Module.finrank fieldRing
        ((moduleSpecΓFunctor (R := fieldRing)).obj
          ((((pullback baseChange).mapHomologicalComplex _).obj complex).homology
            homologyDegree)) = if homologyDegree = (degree : ℤ) then rank else 0 := by
  classical
  obtain ⟨termRank, _, ⟨trivialization⟩⟩ := finiteFree.exists_iso_free_of_rank_eq_zero
  obtain ⟨residuePoint⟩ : Nonempty (Spec (baseScheme.residueField (baseChange point))) :=
    inferInstance
  have matrixRank (sourceDegree targetDegree : ℤ) :
      ((freeMatrix ((trivialization sourceDegree).inv ≫ complex.d sourceDegree targetDegree ≫
          (trivialization targetDegree).hom)).map
        (baseScheme.fromSpecResidueField (baseChange point)).appTop).rank =
      ((freeMatrix ((trivialization sourceDegree).inv ≫ complex.d sourceDegree targetDegree ≫
          (trivialization targetDegree).hom)).map baseChange.appTop).rank :=
    rank_map_appTop_eq_of_base_eq (isField_Γ_Spec_residueField (baseChange point))
      (isField_Γ_Spec field) _ baseChange residuePoint point
      (fromSpecResidueField_base_apply _ _) _
  rw [mem_homologyRankLocus_iff_rankCondition trivialization]
  constructor
  · intro rankCondition homologyDegree
    have dimensions := finrank_homology_pullback_add_rank_add_rank trivialization field
      baseChange homologyDegree
    have rankEquation := rankCondition homologyDegree
    rw [matrixRank, matrixRank] at rankEquation
    simp only [Fintype.card_ulift, Fintype.card_fin] at rankEquation
    omega
  · intro dimensions homologyDegree
    have homologyDimension := dimensions homologyDegree
    have rankEquation := finrank_homology_pullback_add_rank_add_rank trivialization field
      baseChange homologyDegree
    rw [matrixRank, matrixRank]
    simp only [Fintype.card_ulift, Fintype.card_fin]
    omega

/-- Over a field-valued point, the fixed-rank fibre condition is equivalent to
finite local freeness in one degree. -/
theorem IsFiniteFreeComplex.isFiniteLocallyFreeInDegree_pullback_iff_of_isField
    {complex : CochainComplex baseScheme.Modules ℤ} {bound : ℕ}
    (finiteFree : IsFiniteFreeComplex complex bound) {fieldRing : CommRingCat.{u}}
    (field : IsField fieldRing) (baseChange : Spec fieldRing ⟶ baseScheme)
    (point : Spec fieldRing) (degree rank : ℕ) :
    IsFiniteLocallyFreeInDegree
        (fun homologyDegree : ℕ ↦
          (((pullback baseChange).mapHomologicalComplex _).obj complex).homology homologyDegree)
        degree rank ↔ baseChange point ∈ homologyRankLocus complex degree rank := by
  let pulledComplex : CochainComplex (Spec fieldRing).Modules ℤ :=
    ((pullback baseChange).mapHomologicalComplex _).obj complex
  letI : complex.IsStrictlyGE 0 := finiteFree.isStrictlyGE
  haveI : pulledComplex.IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro homologyDegree negative
    exact (pullback baseChange).map_isZero
      (complex.isZero_of_isStrictlyGE 0 homologyDegree negative)
  letI (homologyDegree : ℤ) : Module.Finite fieldRing
      ((moduleSpecΓFunctor (R := fieldRing)).obj (pulledComplex.homology homologyDegree)) :=
    finite_moduleSpecΓFunctor_obj_homology_pullback finiteFree.exists_iso_free field baseChange
      homologyDegree
  rw [finiteFree.mem_homologyRankLocus_iff_finrank_pullback field baseChange point]
  constructor
  · intro singleDegree homologyDegree
    by_cases nonnegative : 0 ≤ homologyDegree
    · obtain ⟨naturalDegree, rfl⟩ := Int.eq_ofNat_of_zero_le nonnegative
      by_cases equalDegree : naturalDegree = degree
      · subst naturalDegree
        simpa only [if_pos rfl, ite_true] using
          (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj field
            (pulledComplex.homology degree) rank).mp singleDegree.isFiniteLocallyFreeOfRank
      · rw [if_neg (by exact_mod_cast equalDegree)]
        exact (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero field _).mp
          (singleDegree.isZero naturalDegree equalDegree)
    · rw [if_neg (by omega)]
      exact (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero field _).mp
        (pulledComplex.isZero_of_isGE 0 homologyDegree (by omega))
  · intro dimensions
    refine ⟨fun homologyDegree unequal ↦ ?_, ?_⟩
    · apply (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero field _).mpr
      simpa only [if_neg (show (homologyDegree : ℤ) ≠ degree by exact_mod_cast unequal)] using
        dimensions homologyDegree
    · apply (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj field _ rank).mpr
      simpa only [if_pos rfl, ite_true] using dimensions degree

section Model

variable (sourceMap : sourceScheme ⟶ baseScheme) [QuasiCompact sourceMap] [IsSeparated sourceMap]
  (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsQuasicoherent]
  {openSubset : baseScheme.Opens} {complex : CochainComplex openSubset.toScheme.Modules ℤ}
  {bound : ℕ} (finiteFree : IsFiniteFreeComplex complex bound)
  (baseChangeComparison : ∀ {targetScheme pulledScheme : Scheme.{u}}
    (baseChange : targetScheme ⟶ openSubset.toScheme) (pullbackMap : pulledScheme ⟶ sourceScheme)
    (pulledMap : pulledScheme ⟶ targetScheme) [HasInjectiveResolutions pulledScheme.Modules],
    IsPullback pullbackMap pulledMap sourceMap (baseChange ≫ openSubset.ι) →
    ∀ homologyDegree : ℕ,
      Nonempty ((((pullback baseChange).mapHomologicalComplex _).obj complex).homology
          homologyDegree ≅
        (higherDirectImage pulledMap homologyDegree).obj ((pullback pullbackMap).obj moduleSheaf)))

include finiteFree baseChangeComparison in
/-- A universal finite free model identifies its rank locus with the inverse
image of the actual fibre-cohomology locus. -/
theorem homologyRankLocus_eq_preimage_perfectLocusOfRank (degree rank : ℕ) :
    homologyRankLocus complex degree rank =
      openSubset.ι ⁻¹' moduleSheaf.perfectLocusOfRank sourceMap degree rank := by
  ext point
  let basePoint := openSubset.ι point
  change point ∈ homologyRankLocus complex degree rank ↔
    basePoint ∈ moduleSheaf.perfectLocusOfRank sourceMap degree rank
  let residueMap := baseScheme.fromSpecResidueField basePoint
  have residueRange : Set.range residueMap ⊆ Set.range openSubset.ι := by
    rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]
    exact Set.singleton_subset_iff.mpr point.2
  let residueLift := IsOpenImmersion.lift openSubset.ι residueMap residueRange
  have factorization : residueLift ≫ openSubset.ι = residueMap :=
    IsOpenImmersion.lift_fac _ _ _
  obtain ⟨residuePoint⟩ : Nonempty (Spec (baseScheme.residueField basePoint)) := inferInstance
  have imagePoint : residueLift residuePoint = point := by
    apply openSubset.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, factorization]
    exact fromSpecResidueField_base_apply _ _
  simpa only [imagePoint] using
    (finiteFree.isFiniteLocallyFreeInDegree_pullback_iff_of_isField
      (Field.toIsField _) residueLift residuePoint degree rank).symm.trans
        (isFiniteLocallyFreeInDegree_homology_pullback_iff sourceMap moduleSheaf finiteFree
          baseChangeComparison residueLift factorization degree rank)

end Model

section Noetherian

variable (baseRing : Type u) [CommRing baseRing] [IsNoetherianRing baseRing]
  (sourceMap : sourceScheme ⟶ Spec (.of baseRing))
  [IsProper sourceMap] (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsFinitePresentation]
  (flat : moduleSheaf.IsFlatOver sourceMap)

include flat

/-- Over a Noetherian spectrum, the fixed-rank single-degree fibre-cohomology
locus of a proper family with finitely presented flat coefficients is open. -/
theorem isOpen_perfectLocusOfRank_of_isProper (degree rank : ℕ) :
    IsOpen (moduleSheaf.perfectLocusOfRank sourceMap degree rank) := by
  refine isOpen_iff_forall_mem_open.mpr fun point membership ↦ ?_
  obtain ⟨denominator, complex, bound, point_mem, finiteFree, comparison⟩ :=
    exists_isFiniteFreeComplex_higherDirectImage_of_isProper baseRing sourceMap moduleSheaf flat
      point
  let modelOpen := (Spec (.of baseRing)).basicOpen denominator
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

private theorem exists_mem_isFiniteLocallyFreeInDegree_restrict_of_isProper
    {degree rank : ℕ} {targetScheme pulledScheme : Scheme.{u}}
    (baseChange : targetScheme ⟶ Spec (.of baseRing)) (pullbackMap : pulledScheme ⟶ sourceScheme)
    (pulledMap : pulledScheme ⟶ targetScheme) [HasInjectiveResolutions pulledScheme.Modules]
    (square : IsPullback pullbackMap pulledMap sourceMap baseChange) (point : targetScheme)
    (membership : baseChange point ∈ moduleSheaf.perfectLocusOfRank sourceMap degree rank) :
    ∃ targetOpen : targetScheme.Opens, point ∈ targetOpen ∧
      IsFiniteLocallyFreeInDegree
        (fun homologyDegree ↦ ((higherDirectImage pulledMap homologyDegree).obj
          ((pullback pullbackMap).obj moduleSheaf)).restrict targetOpen.ι) degree rank := by
  obtain ⟨denominator, complex, bound, point_mem, finiteFree, comparison⟩ :=
    exists_isFiniteFreeComplex_higherDirectImage_of_isProper baseRing sourceMap moduleSheaf flat
      (baseChange point)
  let modelOpen := (Spec (.of baseRing)).basicOpen denominator
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

/-- Every base change into the open fixed-rank cohomology locus has higher
direct images finite locally free in the prescribed degree and zero elsewhere. -/
theorem exists_opens_higherDirectImage_isFiniteLocallyFreeInDegree_of_isProper (degree rank : ℕ) :
    ∃ openSubset : (Spec (.of baseRing)).Opens,
      (openSubset : Set (Spec (.of baseRing))) =
        moduleSheaf.perfectLocusOfRank sourceMap degree rank ∧
      ∀ {targetScheme pulledScheme : Scheme.{u}}
        (baseChange : targetScheme ⟶ Spec (.of baseRing)) (pullbackMap : pulledScheme ⟶ sourceScheme)
        (pulledMap : pulledScheme ⟶ targetScheme) [HasInjectiveResolutions pulledScheme.Modules],
        IsPullback pullbackMap pulledMap sourceMap baseChange → Set.range baseChange ⊆ openSubset →
        IsFiniteLocallyFreeInDegree (fun homologyDegree ↦ (higherDirectImage pulledMap homologyDegree).obj
          ((pullback pullbackMap).obj moduleSheaf)) degree rank := by
  refine ⟨⟨_, isOpen_perfectLocusOfRank_of_isProper baseRing sourceMap moduleSheaf flat degree rank⟩,
    rfl, fun baseChange pullbackMap pulledMap _ square rangeSubset ↦ ?_⟩
  choose targetOpen point_mem localFreeness using fun point ↦
    exists_mem_isFiniteLocallyFreeInDegree_restrict_of_isProper baseRing sourceMap moduleSheaf
      flat baseChange pullbackMap pulledMap square point (rangeSubset ⟨point, rfl⟩)
  refine ⟨fun homologyDegree unequal ↦ ?_, ?_⟩
  · exact isZero_of_forall_exists_isZero_restrict _ fun point ↦
      ⟨targetOpen point, point_mem point, (localFreeness point).isZero homologyDegree unequal⟩
  · exact isFiniteLocallyFreeOfRank_of_iSup_eq_top _ targetOpen
      (eq_top_iff.mpr fun point _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨point, point_mem point⟩)
      fun point ↦ (localFreeness point).isFiniteLocallyFreeOfRank

/-- Single-degree locally free higher direct images after base change force
the image to lie in the fixed-rank fibre-cohomology locus. -/
theorem range_subset_perfectLocusOfRank_of_isPullback_of_isProper
    {degree rank : ℕ} {targetScheme pulledScheme : Scheme.{u}}
    (baseChange : targetScheme ⟶ Spec (.of baseRing)) (pullbackMap : pulledScheme ⟶ sourceScheme)
    (pulledMap : pulledScheme ⟶ targetScheme) [HasInjectiveResolutions pulledScheme.Modules]
    (square : IsPullback pullbackMap pulledMap sourceMap baseChange)
    (singleDegree : IsFiniteLocallyFreeInDegree (fun homologyDegree ↦
      (higherDirectImage pulledMap homologyDegree).obj ((pullback pullbackMap).obj moduleSheaf))
        degree rank) :
    Set.range baseChange ⊆ moduleSheaf.perfectLocusOfRank sourceMap degree rank := by
  rintro _ ⟨point, rfl⟩
  obtain ⟨denominator, complex, bound, point_mem, finiteFree, comparison⟩ :=
    exists_isFiniteFreeComplex_higherDirectImage_of_isProper baseRing sourceMap moduleSheaf flat
      (baseChange point)
  let modelOpen := (Spec (.of baseRing)).basicOpen denominator
  let targetOpen := baseChange ⁻¹ᵁ modelOpen
  have local_range : Set.range (targetOpen.ι ≫ baseChange) ⊆ Set.range modelOpen.ι := by
    rintro _ ⟨localPoint, rfl⟩
    exact ⟨⟨_, localPoint.2⟩, rfl⟩
  let localBaseChange := IsOpenImmersion.lift modelOpen.ι (targetOpen.ι ≫ baseChange) local_range
  have factorization : localBaseChange ≫ modelOpen.ι = targetOpen.ι ≫ baseChange :=
    IsOpenImmersion.lift_fac _ _ _
  let homologyComparison (homologyDegree : ℕ) :=
    (nonempty_restrict_higherDirectImage_iso_homology sourceMap moduleSheaf comparison
      baseChange pullbackMap pulledMap square targetOpen localBaseChange factorization
        homologyDegree).some
  have := singleDegree.isFiniteLocallyFreeOfRank
  have local_condition : IsFiniteLocallyFreeInDegree (fun homologyDegree : ℕ ↦
      (((pullback localBaseChange).mapHomologicalComplex _).obj complex).homology homologyDegree)
        degree rank :=
    ⟨fun homologyDegree unequal ↦ ((restrictFunctor targetOpen.ι).map_isZero
      (singleDegree.isZero homologyDegree unequal)).of_iso (homologyComparison homologyDegree).symm,
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (homologyComparison degree)⟩
  have rankMembership := finiteFree.range_subset_homologyRankLocus degree rank localBaseChange
    local_condition ⟨⟨point, point_mem⟩, rfl⟩
  have locusComparison := homologyRankLocus_eq_preimage_perfectLocusOfRank sourceMap moduleSheaf
    finiteFree comparison degree rank
  have membership := (Set.ext_iff.mp locusComparison (localBaseChange ⟨point, point_mem⟩)).mp
    rankMembership
  change modelOpen.ι (localBaseChange ⟨point, point_mem⟩) ∈
    moduleSheaf.perfectLocusOfRank sourceMap degree rank at membership
  have image_eq : modelOpen.ι (localBaseChange ⟨point, point_mem⟩) = baseChange point := by
    rw [← Scheme.Hom.comp_apply, factorization, Scheme.Hom.comp_apply]
    rfl
  rwa [image_eq] at membership

/-- Over a Noetherian spectrum, the fixed-rank fibre-cohomology locus
represents single-degree locally free higher direct image under arbitrary
Cartesian base change. -/
theorem exists_opens_range_subset_iff_isFiniteLocallyFreeInDegree_of_isProper
    (degree rank : ℕ) :
    ∃ openSubset : (Spec (.of baseRing)).Opens,
      (openSubset : Set (Spec (.of baseRing))) =
        moduleSheaf.perfectLocusOfRank sourceMap degree rank ∧
      ∀ {targetScheme pulledScheme : Scheme.{u}}
        (baseChange : targetScheme ⟶ Spec (.of baseRing)) (pullbackMap : pulledScheme ⟶ sourceScheme)
        (pulledMap : pulledScheme ⟶ targetScheme) [HasInjectiveResolutions pulledScheme.Modules],
        IsPullback pullbackMap pulledMap sourceMap baseChange →
          (Set.range baseChange ⊆ openSubset ↔
            IsFiniteLocallyFreeInDegree (fun homologyDegree ↦
              (higherDirectImage pulledMap homologyDegree).obj
                ((pullback pullbackMap).obj moduleSheaf)) degree rank) := by
  obtain ⟨openSubset, locus_eq, universal⟩ :=
    exists_opens_higherDirectImage_isFiniteLocallyFreeInDegree_of_isProper baseRing sourceMap
      moduleSheaf flat degree rank
  refine ⟨openSubset, locus_eq, fun baseChange pullbackMap pulledMap _ square ↦
    ⟨universal baseChange pullbackMap pulledMap square, fun singleDegree ↦ ?_⟩⟩
  rw [locus_eq]
  exact range_subset_perfectLocusOfRank_of_isPullback_of_isProper baseRing sourceMap moduleSheaf
    flat baseChange pullbackMap pulledMap square singleDegree

end Noetherian

end AlgebraicGeometry.Scheme.Modules
