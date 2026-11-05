import Jacobian.AlgebraicGeometry.Morphisms.FlatStalk
import Jacobian.AlgebraicGeometry.Modules.FiniteFreeComplex
import Jacobian.AlgebraicGeometry.Modules.FlatPullback
import Jacobian.AlgebraicGeometry.Modules.FreeComplexLocal

/-!
# Universal rank loci of finite free complexes

The homology of the pullback of a bounded finite free complex is finite locally
free in one degree exactly when the base-change morphism has image in its
homology rank locus. The converse is checked over the local rings of the source.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Single-degree locally free homology after base change forces every image
point to belong to the homology rank locus. -/
theorem IsFiniteFreeComplex.range_subset_homologyRankLocus
    {baseScheme targetScheme : Scheme.{u}} {complex : CochainComplex baseScheme.Modules ℤ}
    {bound : ℕ} (finiteFree : IsFiniteFreeComplex complex bound) (degree rank : ℕ)
    (baseChange : targetScheme ⟶ baseScheme)
    (singleDegree : IsFiniteLocallyFreeInDegree (fun homologyDegree : ℕ ↦
      (((pullback baseChange).mapHomologicalComplex _).obj complex).homology homologyDegree)
        degree rank) : Set.range baseChange ⊆ homologyRankLocus complex degree rank := by
  classical
  obtain ⟨termRank, bounded, ⟨trivialization⟩⟩ := finiteFree.exists_iso_free_of_rank_eq_zero
  let matrices := fun sourceDegree targetDegree : ℤ ↦
    freeMatrix ((trivialization sourceDegree).inv ≫ complex.d sourceDegree targetDegree ≫
      (trivialization targetDegree).hom)
  let pulledComplex : CochainComplex targetScheme.Modules ℤ :=
    ((pullback baseChange).mapHomologicalComplex _).obj complex
  let pulledTrivialization (homologyDegree : ℤ) : pulledComplex.X homologyDegree ≅
      SheafOfModules.free (ULift.{u} (Fin (termRank homologyDegree))) :=
    (pullback baseChange).mapIso (trivialization homologyDegree) ≪≫ pullbackFreeIso baseChange _
  have matrix_pullback (sourceDegree targetDegree : ℤ) {localScheme : Scheme.{u}}
      (localMap : localScheme ⟶ targetScheme) :
      freeMatrix ((((pullback localMap).mapIso (pulledTrivialization sourceDegree) ≪≫
        pullbackFreeIso localMap _).inv ≫
        (((pullback localMap).mapHomologicalComplex _).obj pulledComplex).d sourceDegree targetDegree ≫
        ((pullback localMap).mapIso (pulledTrivialization targetDegree) ≪≫
          pullbackFreeIso localMap _).hom)) =
        (matrices sourceDegree targetDegree).map (localMap ≫ baseChange).appTop := by
    rw [freeMatrix_pullback_d, freeMatrix_pullback_d, map_appTop_comp]
  rintro _ ⟨point, rfl⟩
  rw [mem_homologyRankLocus_iff_rankCondition trivialization]
  let localMap := targetScheme.fromSpecStalk point
  let localPoint := IsLocalRing.closedPoint (targetScheme.presheaf.stalk point)
  have local_neighbourhood (openSubset : (Spec (targetScheme.presheaf.stalk point)).Opens)
      (membership : localPoint ∈ openSubset) : openSubset = ⊤ :=
    IsLocalRing.closed_point_mem_iff.mp membership
  let localComplex : CochainComplex (Spec (targetScheme.presheaf.stalk point)).Modules ℤ :=
    ((pullback localMap).mapHomologicalComplex _).obj pulledComplex
  let localTrivialization (homologyDegree : ℤ) :=
    (pullback localMap).mapIso (pulledTrivialization homologyDegree) ≪≫
      pullbackFreeIso localMap (ULift.{u} (Fin (termRank homologyDegree)))
  let homologyComparison (homologyDegree : ℤ) : localComplex.homology homologyDegree ≅
      (pullback localMap).obj (pulledComplex.homology homologyDegree) :=
    (pulledComplex.sc homologyDegree).mapHomologyIso (pullback localMap)
  have local_vanishing (homologyDegree : ℤ) (unequal : homologyDegree ≠ degree)
      (nonempty : Nonempty (ULift.{u} (Fin (termRank homologyDegree)))) :
      IsZero (localComplex.homology homologyDegree) := by
    have nonnegative : 0 ≤ homologyDegree := by
      obtain ⟨⟨index⟩⟩ := nonempty
      have positive := index.pos
      by_contra negative
      have zero_rank := bounded homologyDegree (Or.inl (by omega))
      omega
    obtain ⟨naturalDegree, rfl⟩ := Int.eq_ofNat_of_zero_le nonnegative
    exact ((pullback localMap).map_isZero
      (singleDegree.isZero naturalDegree (by exact_mod_cast unequal))).of_iso
        (homologyComparison naturalDegree)
  have := singleDegree.isFiniteLocallyFreeOfRank
  obtain ⟨coverIndex, cover, covers, freeHomology⟩ :=
    IsFiniteLocallyFreeOfRank.exists_restrict_iso_free (pulledComplex.homology degree) (r := rank)
  obtain ⟨index, membership⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (by rw [covers]; trivial : point ∈ ⨆ index, cover index)
  have local_range : Set.range localMap ⊆ Set.range (cover index).ι := by
    rw [Scheme.range_fromSpecStalk, Scheme.Opens.range_ι]
    exact fun otherPoint generization ↦ generization.mem_open (cover index).isOpen membership
  let localLift := IsOpenImmersion.lift (cover index).ι localMap local_range
  have factorization : localLift ≫ (cover index).ι = localMap :=
    IsOpenImmersion.lift_fac _ _ _
  let freeComparison : (pullback localMap).obj (pulledComplex.homology degree) ≅
      SheafOfModules.free (ULift.{u} (Fin rank)) :=
    ((pullbackCongr factorization).app _).symm ≪≫
      ((pullbackComp localLift (cover index).ι).app _).symm ≪≫
        (pullback localLift).mapIso (((restrictFunctorIsoPullback (cover index).ι).app _).symm ≪≫
          (freeHomology index).some) ≪≫ pullbackFreeIso localLift _
  have rankCondition := rankCondition_of_homology local_neighbourhood localComplex
    localTrivialization bound (fun homologyDegree above_bound ↦ by
      have zero_rank := bounded homologyDegree (Or.inr (by exact_mod_cast above_bound))
      rw [zero_rank]
      infer_instance) degree local_vanishing (homologyComparison degree ≪≫ freeComparison)
  have matrix_eq : (fun sourceDegree targetDegree ↦
      freeMatrix ((localTrivialization sourceDegree).inv ≫
        localComplex.d sourceDegree targetDegree ≫ (localTrivialization targetDegree).hom)) =
      fun sourceDegree targetDegree ↦
        (matrices sourceDegree targetDegree).map (localMap ≫ baseChange).appTop := by
    funext sourceDegree targetDegree
    exact matrix_pullback sourceDegree targetDegree localMap
  rw [matrix_eq, Fintype.card_ulift, Fintype.card_fin] at rankCondition
  have image_rank := Scheme.RankCondition.of_map (localMap ≫ baseChange) rankCondition
  rwa [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at image_rank

/-- The homology rank locus represents single-degree locally free homology
under every scheme-valued base change. -/
theorem IsFiniteFreeComplex.range_subset_homologyRankLocus_iff
    {baseScheme targetScheme : Scheme.{u}} {complex : CochainComplex baseScheme.Modules ℤ}
    {bound : ℕ} (finiteFree : IsFiniteFreeComplex complex bound) (degree rank : ℕ)
    (baseChange : targetScheme ⟶ baseScheme) :
    Set.range baseChange ⊆ homologyRankLocus complex degree rank ↔
      IsFiniteLocallyFreeInDegree (fun homologyDegree : ℕ ↦
        (((pullback baseChange).mapHomologicalComplex _).obj complex).homology homologyDegree)
          degree rank :=
  ⟨finiteFree.isFiniteLocallyFreeInDegree_of_range_subset degree rank baseChange,
    finiteFree.range_subset_homologyRankLocus degree rank baseChange⟩

/-- There is an open subscheme classifying single-degree locally free
homology of every pullback of a bounded finite free complex. -/
theorem IsFiniteFreeComplex.exists_opens_range_subset_iff
    {baseScheme : Scheme.{u}} {complex : CochainComplex baseScheme.Modules ℤ}
    {bound : ℕ} (finiteFree : IsFiniteFreeComplex complex bound) (degree rank : ℕ) :
    ∃ openSubset : baseScheme.Opens, ∀ {targetScheme : Scheme.{u}}
      (baseChange : targetScheme ⟶ baseScheme), Set.range baseChange ⊆ openSubset ↔
        IsFiniteLocallyFreeInDegree (fun homologyDegree : ℕ ↦
          (((pullback baseChange).mapHomologicalComplex _).obj complex).homology homologyDegree)
            degree rank :=
  ⟨⟨_, finiteFree.isOpen_homologyRankLocus degree rank⟩,
    fun baseChange ↦ finiteFree.range_subset_homologyRankLocus_iff degree rank baseChange⟩

end AlgebraicGeometry.Scheme.Modules
