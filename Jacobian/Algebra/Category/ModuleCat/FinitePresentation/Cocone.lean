import Jacobian.Algebra.Category.ModuleCat.FinitePresentation.Descent
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Morphism descent for an arbitrary directed ring colimit cocone

Finite-presentation descent applies to any chosen colimit cocone, in particular
to the cocone of sections of an affine inverse limit. The composition comparisons
are normalized on unit tensors, so the descended maps can be compared with
geometric pullback maps.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe ringUniverse

open CategoryTheory Limits TensorProduct
open scoped ChangeOfRings

namespace ModuleCat

private def scalarExtensionFactorization
    {sourceRing middleRing targetRing : Type ringUniverse}
    [CommRing sourceRing] [CommRing middleRing] [CommRing targetRing]
    (firstMap : sourceRing →+* middleRing) (secondMap : middleRing →+* targetRing)
    (composite : sourceRing →+* targetRing)
    (factorization : secondMap.comp firstMap = composite) :
    extendScalars composite ≅ extendScalars firstMap ⋙ extendScalars secondMap :=
  eqToIso (congrArg extendScalars factorization.symm) ≪≫
    extendScalarsComp firstMap secondMap

private lemma scalarExtensionFactorization_one_tmul
    {sourceRing middleRing targetRing : Type ringUniverse}
    [CommRing sourceRing] [CommRing middleRing] [CommRing targetRing]
    (firstMap : sourceRing →+* middleRing) (secondMap : middleRing →+* targetRing)
    (composite : sourceRing →+* targetRing)
    (factorization : secondMap.comp firstMap = composite)
    (moduleObject : ModuleCat.{ringUniverse} sourceRing) (moduleElement : moduleObject) :
    ((scalarExtensionFactorization firstMap secondMap composite factorization).app
      moduleObject).hom ((1 : targetRing) ⊗ₜ[sourceRing, composite] moduleElement) =
        (1 : targetRing) ⊗ₜ[middleRing, secondMap]
          ((1 : middleRing) ⊗ₜ[sourceRing, firstMap] moduleElement) := by
  subst composite
  exact extendScalarsComp_hom_app_one_tmul firstMap secondMap moduleObject moduleElement

private def fullyFaithfulExtendScalarsOfIso
    {sourceRing targetRing : CommRingCat.{ringUniverse}} (ringIso : sourceRing ≅ targetRing) :
    (extendScalars ringIso.hom.hom).FullyFaithful := by
  let restrictionEquivalence :=
    restrictScalarsEquivalenceOfRingEquiv ringIso.commRingCatIsoToRingEquiv
  let comparison : extendScalars ringIso.hom.hom ≅ restrictionEquivalence.inverse :=
    (extendRestrictScalarsAdj ringIso.hom.hom).leftAdjointUniq
      restrictionEquivalence.symm.toAdjunction
  exact (Functor.FullyFaithful.ofFullyFaithful restrictionEquivalence.inverse).ofIso
    comparison.symm

/-- A map after scalar extension to a directed colimit descends when its source is finitely
presented. This version uses an arbitrary colimit cocone. -/
theorem exists_hom_at_stage_of_isColimit
    {Index : Type ringUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] (diagram : Index ⥤ CommRingCat.{ringUniverse})
    (cocone : Cocone diagram) (colimitWitness : IsColimit cocone)
    (initialIndex : Index) (sourceModule targetModule : ModuleCat.{ringUniverse}
      (diagram.obj initialIndex))
    [Module.FinitePresentation (diagram.obj initialIndex) sourceModule]
    (coefficientMap : (extendScalars (cocone.ι.app initialIndex).hom).obj sourceModule ⟶
      (extendScalars (cocone.ι.app initialIndex).hom).obj targetModule) :
    ∃ (stageIndex : Index) (initialLe : initialIndex ≤ stageIndex),
      let transition : diagram.obj initialIndex →+* diagram.obj stageIndex :=
        (diagram.map (homOfLE initialLe)).hom
      let initialMap : diagram.obj initialIndex →+* cocone.pt :=
        (cocone.ι.app initialIndex).hom
      let stageMap : diagram.obj stageIndex →+* cocone.pt :=
        (cocone.ι.app stageIndex).hom
      ∃ (liftedMap : (extendScalars transition).obj sourceModule ⟶
          (extendScalars transition).obj targetModule)
        (sourceComparison : (extendScalars initialMap).obj sourceModule ≅
          (extendScalars stageMap).obj ((extendScalars transition).obj sourceModule))
        (targetComparison : (extendScalars initialMap).obj targetModule ≅
          (extendScalars stageMap).obj ((extendScalars transition).obj targetModule)),
        (∀ moduleElement : sourceModule,
          sourceComparison.hom ((1 : cocone.pt) ⊗ₜ[diagram.obj initialIndex, initialMap]
            moduleElement) = (1 : cocone.pt) ⊗ₜ[diagram.obj stageIndex, stageMap]
              ((1 : diagram.obj stageIndex) ⊗ₜ[diagram.obj initialIndex, transition]
                moduleElement)) ∧
        (∀ moduleElement : targetModule,
          targetComparison.hom ((1 : cocone.pt) ⊗ₜ[diagram.obj initialIndex, initialMap]
            moduleElement) = (1 : cocone.pt) ⊗ₜ[diagram.obj stageIndex, stageMap]
              ((1 : diagram.obj stageIndex) ⊗ₜ[diagram.obj initialIndex, transition]
                moduleElement)) ∧
        coefficientMap ≫ targetComparison.hom = sourceComparison.hom ≫
          (extendScalars stageMap).map liftedMap := by
  classical
  let ringIso : colimit diagram ≅ cocone.pt :=
    (colimit.isColimit diagram).coconePointUniqueUpToIso colimitWitness
  let extension : ModuleCat.{ringUniverse} ↑(colimit diagram : CommRingCat.{ringUniverse}) ⥤
      ModuleCat.{ringUniverse} cocone.pt := extendScalars ringIso.hom.hom
  let fullyFaithful := fullyFaithfulExtendScalarsOfIso ringIso
  have factorization (stageIndex : Index) :
      ringIso.hom.hom.comp (colimit.ι diagram stageIndex).hom =
        (cocone.ι.app stageIndex).hom :=
    congrArg CommRingCat.Hom.hom
      ((colimit.isColimit diagram).comp_coconePointUniqueUpToIso_hom
        colimitWitness stageIndex)
  let comparison (stageIndex : Index) := scalarExtensionFactorization
    (colimit.ι diagram stageIndex).hom ringIso.hom.hom
    (cocone.ι.app stageIndex).hom (factorization stageIndex)
  let canonicalMap := fullyFaithful.preimage
    ((comparison initialIndex).inv.app sourceModule ≫ coefficientMap ≫
      (comparison initialIndex).hom.app targetModule)
  have recover : coefficientMap ≫ (comparison initialIndex).hom.app targetModule =
      (comparison initialIndex).hom.app sourceModule ≫ extension.map canonicalMap := by
    rw [fullyFaithful.map_preimage]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  obtain ⟨stageIndex, initialLe, liftedMap, sourceComparison, targetComparison,
      sourceNormalization, targetNormalization, square⟩ :=
    exists_hom_at_stage diagram initialIndex sourceModule targetModule canonicalMap
  let stageSource := (extendScalars (diagram.map (homOfLE initialLe)).hom).obj sourceModule
  let stageTarget := (extendScalars (diagram.map (homOfLE initialLe)).hom).obj targetModule
  let transferredComparison (moduleObject : ModuleCat.{ringUniverse}
      (diagram.obj initialIndex))
      (stageObject : ModuleCat.{ringUniverse} (diagram.obj stageIndex))
      (canonicalComparison :
        (extendScalars (colimit.ι diagram initialIndex).hom).obj moduleObject ≅
          (extendScalars (colimit.ι diagram stageIndex).hom).obj stageObject) :=
    (comparison initialIndex).app moduleObject ≪≫
      extension.mapIso canonicalComparison ≪≫ ((comparison stageIndex).app stageObject).symm
  let sourceIso := transferredComparison sourceModule stageSource sourceComparison
  let targetIso := transferredComparison targetModule stageTarget targetComparison
  have normalization (moduleObject : ModuleCat.{ringUniverse} (diagram.obj initialIndex))
      (canonicalComparison :
        (extendScalars (colimit.ι diagram initialIndex).hom).obj moduleObject ≅
          (extendScalars (colimit.ι diagram stageIndex).hom).obj
            ((extendScalars (diagram.map (homOfLE initialLe)).hom).obj moduleObject))
      (unitNormalization : ∀ moduleElement : moduleObject,
        canonicalComparison.hom
          ((1 : ↑(colimit diagram : CommRingCat.{ringUniverse})) ⊗ₜ[diagram.obj initialIndex,
            (colimit.ι diagram initialIndex).hom] moduleElement) =
              (1 : ↑(colimit diagram : CommRingCat.{ringUniverse})) ⊗ₜ[diagram.obj stageIndex,
                (colimit.ι diagram stageIndex).hom]
                  ((1 : diagram.obj stageIndex) ⊗ₜ[diagram.obj initialIndex,
                    (diagram.map (homOfLE initialLe)).hom] moduleElement))
      (moduleElement : moduleObject) :
      (transferredComparison moduleObject _ canonicalComparison).hom
        ((1 : cocone.pt) ⊗ₜ[diagram.obj initialIndex,
          (show diagram.obj initialIndex →+* cocone.pt from
            (cocone.ι.app initialIndex).hom)] moduleElement) =
            (1 : cocone.pt) ⊗ₜ[diagram.obj stageIndex,
              (show diagram.obj stageIndex →+* cocone.pt from
                (cocone.ι.app stageIndex).hom)]
              ((1 : diagram.obj stageIndex) ⊗ₜ[diagram.obj initialIndex,
                (diagram.map (homOfLE initialLe)).hom] moduleElement) := by
    apply (ConcreteCategory.bijective_of_isIso
      (((comparison stageIndex).app _).hom)).injective
    change ((comparison stageIndex).app _).hom
      (((comparison stageIndex).app _).inv
        (extension.map canonicalComparison.hom
          (((comparison initialIndex).app moduleObject).hom _))) = _
    rw [Iso.inv_hom_id_apply, scalarExtensionFactorization_one_tmul,
      ExtendScalars.map_tmul, unitNormalization, scalarExtensionFactorization_one_tmul]
  refine ⟨stageIndex, initialLe, liftedMap, sourceIso, targetIso,
    normalization sourceModule sourceComparison sourceNormalization,
    normalization targetModule targetComparison targetNormalization, ?_⟩
  apply (cancel_mono ((comparison stageIndex).hom.app stageTarget)).mp
  dsimp only [sourceIso, targetIso, transferredComparison, Iso.trans_hom, Iso.symm_hom]
  simp only [Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  rw [← Category.assoc, recover, Category.assoc, ← extension.map_comp_assoc, square,
    extension.map_comp_assoc]
  have stageNaturality :=
    congrArg (fun stageMap ↦ (comparison initialIndex).hom.app sourceModule ≫
      extension.map sourceComparison.hom ≫ stageMap)
      (NatIso.naturality_1 (comparison stageIndex) liftedMap).symm
  dsimp only [extension, stageSource, stageTarget, Functor.comp_obj, Functor.comp_map]
    at stageNaturality ⊢
  erw [Category.comp_id]
  exact stageNaturality

/-- Equality after extension to a chosen directed colimit is detected at a stage for a finite
source module. -/
theorem exists_map_eq_of_map_cocone_eq
    {Index : Type ringUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] (diagram : Index ⥤ CommRingCat.{ringUniverse})
    (cocone : Cocone diagram) (colimitWitness : IsColimit cocone)
    (initialIndex : Index) (sourceModule targetModule : ModuleCat.{ringUniverse}
      (diagram.obj initialIndex))
    [Module.Finite (diagram.obj initialIndex) sourceModule]
    (firstMap secondMap : sourceModule ⟶ targetModule)
    (equality : (extendScalars (cocone.ι.app initialIndex).hom).map firstMap =
      (extendScalars (cocone.ι.app initialIndex).hom).map secondMap) :
    ∃ (stageIndex : Index) (initialLe : initialIndex ≤ stageIndex),
      (extendScalars (diagram.map (homOfLE initialLe)).hom).map firstMap =
        (extendScalars (diagram.map (homOfLE initialLe)).hom).map secondMap := by
  let ringIso : colimit diagram ≅ cocone.pt :=
    (colimit.isColimit diagram).coconePointUniqueUpToIso colimitWitness
  let fullyFaithful := fullyFaithfulExtendScalarsOfIso ringIso
  have factorization : ringIso.hom.hom.comp (colimit.ι diagram initialIndex).hom =
      (cocone.ι.app initialIndex).hom :=
    congrArg CommRingCat.Hom.hom
      ((colimit.isColimit diagram).comp_coconePointUniqueUpToIso_hom
        colimitWitness initialIndex)
  let comparison := scalarExtensionFactorization (colimit.ι diagram initialIndex).hom
    ringIso.hom.hom (cocone.ι.app initialIndex).hom factorization
  have canonicalEquality :
      (extendScalars (colimit.ι diagram initialIndex).hom).map firstMap =
        (extendScalars (colimit.ι diagram initialIndex).hom).map secondMap := by
    apply fullyFaithful.map_injective
    apply (cancel_epi (comparison.hom.app sourceModule)).mp
    have firstNaturality := comparison.hom.naturality firstMap
    have secondNaturality := comparison.hom.naturality secondMap
    simp only [Functor.comp_map] at firstNaturality secondNaturality
    rw [← firstNaturality, ← secondNaturality, equality]
  exact exists_map_eq_of_map_colimit_eq diagram initialIndex sourceModule targetModule
    firstMap secondMap canonicalEquality

end ModuleCat
