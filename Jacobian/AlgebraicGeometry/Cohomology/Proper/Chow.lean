import Jacobian.AlgebraicGeometry.ChowLemma
import Jacobian.AlgebraicGeometry.Cohomology.Proper.Approximation
import Jacobian.AlgebraicGeometry.Cohomology.PushforwardAcyclic
import Jacobian.AlgebraicGeometry.Cohomology.RelativeSerre

/-!
# Generic coherent approximations from Chow's lemma

A coherent module on a nonempty proper scheme admits a generically isomorphic
map to a coherent module with finite cohomology. On a projective modification,
twist its pullback until the positive higher direct images vanish, then push
forward. A coordinate power gives the comparison on a nonempty open.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module on a nonempty proper scheme over a Noetherian ring has
a generically isomorphic coherent approximation with finite cohomology. -/
theorem exists_hasFiniteH_hom_isIso_restrict
    {baseRing : Type u} [CommRing baseRing] [IsNoetherianRing baseRing]
    {sourceScheme : Scheme.{u}} (baseMap : sourceScheme ⟶ Spec (.of baseRing))
    [IsProper baseMap] [Nonempty sourceScheme]
    (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsFinitePresentation] :
    ∃ (approximation : sourceScheme.Modules) (_ : approximation.IsQuasicoherent)
      (_ : approximation.IsFinitePresentation) (comparison : moduleSheaf ⟶ approximation)
      (openSubset : sourceScheme.Opens),
      (openSubset : Set sourceScheme).Nonempty ∧
        IsIso ((restrictFunctor openSubset.ι).map comparison) ∧
        HasFiniteH baseMap approximation := by
  classical
  letI : IsLocallyNoetherian sourceScheme := LocallyOfFiniteType.isLocallyNoetherian baseMap
  letI : CompactSpace sourceScheme := QuasiCompact.compactSpace_of_compactSpace baseMap
  letI : IsNoetherian sourceScheme := {}
  obtain ⟨model, modification, coordinates, finiteCoordinates, embedding, properModification,
    surjectiveModification, closedEmbedding, commutes, denseOpen, dense, isoRestriction⟩ :=
    exists_projectiveModification_of_finite_irreducibleComponents baseMap
      NoetherianSpace.finite_irreducibleComponents
  letI := finiteCoordinates
  letI := properModification
  letI := surjectiveModification
  letI := closedEmbedding
  letI := isoRestriction
  letI := isGrothendieckAbelian model
  let relativeEmbedding := ProjectiveSpace.liftBaseChange modification embedding commutes.symm
  have relativeOver : relativeEmbedding ≫ ℙ(coordinates; sourceScheme) ↘ sourceScheme =
      modification := ProjectiveSpace.liftBaseChange_over modification embedding commutes.symm
  let pulledModule := (pullback modification).obj moduleSheaf
  obtain ⟨bound, vanishing⟩ :=
    exists_isZero_higherDirectImage_tensorObj_twistRestrict relativeOver pulledModule
  let twistDegree := bound.toNat
  have degreeBound : bound ≤ (twistDegree : ℤ) := Int.self_le_toNat bound
  let lineBundle := ProjectiveSpace.twistRestrict relativeEmbedding twistDegree
  letI : lineBundle.IsInvertible := inferInstance
  letI : (pulledModule ⊗ lineBundle).IsFinitePresentation :=
    isFinitePresentation_tensorObj_of_isInvertible pulledModule lineBundle
  obtain ⟨coordinate, openSubset, nonemptyOpen, _, comparisonIsIso⟩ :=
    exists_nonempty_open_isIso_twistedModificationComparison modification modification.surjective
      relativeEmbedding moduleSheaf denseOpen dense.nonempty
  let approximation := (pushforward modification).obj (pulledModule ⊗ lineBundle)
  let zeroComparison := (pushforward modification).rightDerivedZeroIsoSelf.app
    (pulledModule ⊗ lineBundle)
  have quasicoherentApproximation : approximation.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent sourceScheme.ringCatSheaf).prop_of_iso zeroComparison
      (isQuasicoherent_higherDirectImage modification (pulledModule ⊗ lineBundle) 0)
  have finitePresentationApproximation : approximation.IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation sourceScheme.ringCatSheaf).prop_of_iso zeroComparison
      (isFinitePresentation_higherDirectImage_zero_of_projectiveSpace relativeOver
        (pulledModule ⊗ lineBundle))
  refine ⟨approximation, quasicoherentApproximation, finitePresentationApproximation,
    twistedModificationComparison modification relativeEmbedding moduleSheaf coordinate twistDegree,
    openSubset, nonemptyOpen, comparisonIsIso twistDegree, ?_⟩
  apply (hasFiniteH_pushforward_iff_of_isZero modification baseMap (pulledModule ⊗ lineBundle)
    (vanishing twistDegree degreeBound)).2
  have finiteCohomology := hasFiniteH_of_isFinite_relativeProjectiveSpace coordinates
    (CommRingCat.of baseRing) embedding (pulledModule ⊗ lineBundle)
  rwa [commutes] at finiteCohomology

end AlgebraicGeometry.Scheme.Modules
