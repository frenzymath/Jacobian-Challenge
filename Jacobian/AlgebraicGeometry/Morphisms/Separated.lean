import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Rigidity of morphisms over a separated base

Two morphisms into a separated scheme that agree on a scheme-theoretically dense source are equal.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Morphisms over a separated base are determined by a scheme-theoretically dense source. -/
theorem ext_of_isSchemeTheoreticallyDominant {denseSource sourceScheme targetScheme baseScheme : Scheme.{u}} (structureMap : targetScheme ⟶ baseScheme)
    [IsSeparated structureMap] {firstMap secondMap : sourceScheme ⟶ targetScheme} (baseEq : firstMap ≫ structureMap = secondMap ≫ structureMap) (denseMap : denseSource ⟶ sourceScheme)
    [IsSchemeTheoreticallyDominant denseMap] (denseEq : denseMap ≫ firstMap = denseMap ≫ secondMap) : firstMap = secondMap := by
  set pairMap : sourceScheme ⟶ pullback structureMap structureMap := pullback.lift firstMap secondMap baseEq with pairMap_def
  set equalizerMap : pullback pairMap (pullback.diagonal structureMap) ⟶ sourceScheme := pullback.fst pairMap (pullback.diagonal structureMap) with equalizerMap_def
  have : IsClosedImmersion equalizerMap := by rw [equalizerMap_def]; infer_instance
  have first_equalizer : equalizerMap ≫ firstMap = pullback.snd pairMap (pullback.diagonal structureMap) := by
    rw [show firstMap = pairMap ≫ pullback.fst structureMap structureMap from (pullback.lift_fst _ _ _).symm, ← Category.assoc,
      equalizerMap_def, pullback.condition, Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have second_equalizer : equalizerMap ≫ secondMap = pullback.snd pairMap (pullback.diagonal structureMap) := by
    rw [show secondMap = pairMap ≫ pullback.snd structureMap structureMap from (pullback.lift_snd _ _ _).symm, ← Category.assoc,
      equalizerMap_def, pullback.condition, Category.assoc, pullback.diagonal_snd, Category.comp_id]
  have comparisonEq : denseMap ≫ pairMap = (denseMap ≫ firstMap) ≫ pullback.diagonal structureMap :=
    pullback.hom_ext
      (by rw [pairMap_def, Category.assoc, pullback.lift_fst, Category.assoc,
        pullback.diagonal_fst, Category.comp_id])
      (by rw [pairMap_def, Category.assoc, pullback.lift_snd, Category.assoc,
        pullback.diagonal_snd, Category.comp_id, denseEq])
  have factorization : pullback.lift _ _ comparisonEq ≫ equalizerMap = denseMap := pullback.lift_fst _ _ _
  have : IsIso equalizerMap := by
    rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
    refine le_bot_iff.mp ?_
    rw [← denseMap.ker_eq_bot, ← factorization]
    exact Scheme.Hom.le_ker_comp _ _
  rw [← cancel_epi equalizerMap, first_equalizer, second_equalizer]

end AlgebraicGeometry
