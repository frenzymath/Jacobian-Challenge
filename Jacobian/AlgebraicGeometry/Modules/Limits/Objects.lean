import Jacobian.AlgebraicGeometry.Modules.Limits.AffineOverlaps
import Jacobian.AlgebraicGeometry.Modules.Limits.OpenCover
import Jacobian.AlgebraicGeometry.Modules.FinitePresentation.Descent
import Mathlib.CategoryTheory.Filtered.Connected

/-!
# Finitely presented coefficient objects on directed inverse limits

Local affine models of a finitely presented module sheaf descend to a common
stage. Transition morphisms and their identity and cocycle equations descend
on affine intersections. Effective Zariski descent then constructs the stage
module and its actual pullback isomorphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits Opposite
open CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

set_option maxHeartbeats 800000 in
/-- Descent of coefficient objects over a finite affine cover of a separated base.
The transition morphisms, their overlap equations, stage coefficients and
pullback isomorphism are constructed from the sheaf on the limit. -/
theorem exists_isFinitePresentation_model_of_finite_affine_cover
    {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] (diagram : Indexᵒᵖ ⥤ Scheme.{schemeUniverse})
    {baseScheme : Scheme.{schemeUniverse}} [baseScheme.IsSeparated]
    (structureMap : diagram ⟶ (Functor.const Indexᵒᵖ).obj baseScheme)
    [∀ stageIndex, IsAffineHom (structureMap.app stageIndex)]
    (cone : Cone diagram) (limit : IsLimit cone) (limitMap : cone.pt ⟶ baseScheme)
    (factorization : ∀ stageIndex, cone.π.app stageIndex ≫ structureMap.app stageIndex = limitMap)
    {Chart : Type schemeUniverse} [Fintype Chart] (opens : Chart → baseScheme.Opens)
    (affineOpens : ∀ chartIndex, IsAffineOpen (opens chartIndex))
    (cover : ⨆ chartIndex, opens chartIndex = ⊤)
    (moduleSheaf : cone.pt.Modules) [moduleSheaf.IsFinitePresentation] :
    ∃ (stageIndex : Indexᵒᵖ) (stageModule : (diagram.obj stageIndex).Modules),
      stageModule.IsFinitePresentation ∧
        Nonempty ((pullback (cone.π.app stageIndex)).obj stageModule ≅ moduleSheaf) := by
  classical
  letI : IsConnected Indexᵒᵖ := IsCofiltered.isConnected _
  have affinePreimages (baseOpen : baseScheme.Opens) (affineOpen : IsAffineOpen baseOpen) (localIndex : Indexᵒᵖ) :
      IsAffine ((preimageDiagram diagram structureMap baseOpen).obj localIndex) :=
    affineOpen.preimage (structureMap.app localIndex)
  have affinePairs (chartIndex secondIndex : Chart) : IsAffineOpen (opens chartIndex ⊓ opens secondIndex) := (affineOpens chartIndex).inf (affineOpens secondIndex)
  have affineTriples (chartIndex secondIndex thirdIndex : Chart) : IsAffineOpen (opens chartIndex ⊓ opens secondIndex ⊓ opens thirdIndex) := (affinePairs chartIndex secondIndex).inf (affineOpens thirdIndex)
  have localModels (chartIndex : Chart) :
      ∃ (stageIndex : Indexᵒᵖ)
        (stageSheaf : ((preimageDiagram diagram structureMap (opens chartIndex)).obj stageIndex).Modules),
        stageSheaf.IsFinitePresentation ∧
          Nonempty ((pullback ((preimageCone diagram structureMap cone limitMap factorization
            (opens chartIndex)).π.app stageIndex)).obj stageSheaf ≅
              (pullback (limitMap ⁻¹ᵁ opens chartIndex).ι).obj moduleSheaf) := by
    letI := affinePreimages (opens chartIndex) (affineOpens chartIndex)
    let restrictedCone := preimageCone diagram structureMap cone limitMap factorization (opens chartIndex)
    let restrictedLimit := isLimit_preimageCone diagram structureMap cone limitMap factorization limit (opens chartIndex)
    letI : IsAffine restrictedCone.pt := Scheme.isAffine_of_isLimit _ restrictedLimit
    obtain ⟨stageIndex, stageSheaf, finiteStage, comparison⟩ :=
      exists_finitePresentation_model_of_affine_limit
        (preimageDiagram diagram structureMap (opens chartIndex)) restrictedCone restrictedLimit
        ((pullback (limitMap ⁻¹ᵁ opens chartIndex).ι).obj moduleSheaf)
    exact ⟨op stageIndex, stageSheaf, finiteStage, comparison⟩
  choose localIndex coefficients finiteCoefficients localComparisons using localModels
  letI : ∀ chartIndex, (coefficients chartIndex).IsFinitePresentation := finiteCoefficients
  letI : ∀ chartIndex, (coefficients chartIndex).IsQuasicoherent := fun chartIndex ↦
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (coefficients chartIndex)).choose.isQuasicoherent
  let coefficientSchemes (chartIndex : Chart) := (preimageDiagram diagram structureMap (opens chartIndex)).obj (localIndex chartIndex)
  let limitCoefficientMaps (chartIndex : Chart) : (limitMap ⁻¹ᵁ opens chartIndex).toScheme ⟶ coefficientSchemes chartIndex :=
    restrictPreimage (cone.π.app (localIndex chartIndex)) (factorization (localIndex chartIndex)) (le_refl (opens chartIndex))
  let comparisons (chartIndex : Chart) : (modulesPseudofunctor.map (limitCoefficientMaps chartIndex).op.toLoc).toFunctor.obj (coefficients chartIndex) ≅
      (modulesPseudofunctor.map (limitMap ⁻¹ᵁ opens chartIndex).ι.op.toLoc).toFunctor.obj moduleSheaf :=
    (localComparisons chartIndex).some
  let limitTransitions := Gluing.isoGlueHom (preimageChosenPullback opens limitMap) comparisons
  obtain ⟨objectIndex, objectBound⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image localIndex)
  let objectTransitions (chartIndex : Chart) : objectIndex ⟶ localIndex chartIndex := (objectBound (Finset.mem_image_of_mem localIndex (Finset.mem_univ chartIndex))).some
  let objectBaseMap := structureMap.app objectIndex
  let objectCoefficientMaps (chartIndex : Chart) : (objectBaseMap ⁻¹ᵁ opens chartIndex).toScheme ⟶ coefficientSchemes chartIndex :=
    restrictPreimage (diagram.map (objectTransitions chartIndex)) (by simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using structureMap.naturality (objectTransitions chartIndex)) (le_refl (opens chartIndex))
  have localTransitions (pairIndex : Chart × Chart) := by
    letI := affinePreimages (opens pairIndex.1 ⊓ opens pairIndex.2) (affinePairs pairIndex.1 pairIndex.2)
    exact exists_pullHom_of_affine_limit (isLimit_preimageCone diagram structureMap cone limitMap factorization limit (opens pairIndex.1 ⊓ opens pairIndex.2))
      (initialIndex := objectIndex) (firstModule := coefficients pairIndex.1) (secondModule := coefficients pairIndex.2)
      ((preimageChosenPullback opens objectBaseMap pairIndex.1 pairIndex.2).p₁ ≫ objectCoefficientMaps pairIndex.1)
      ((preimageChosenPullback opens objectBaseMap pairIndex.1 pairIndex.2).p₂ ≫ objectCoefficientMaps pairIndex.2)
      (firstLimitMap := (preimageChosenPullback opens limitMap pairIndex.1 pairIndex.2).p₁ ≫ limitCoefficientMaps pairIndex.1)
      (secondLimitMap := (preimageChosenPullback opens limitMap pairIndex.1 pairIndex.2).p₂ ≫ limitCoefficientMaps pairIndex.2)
      (by rw [preimageCone_π_app, ← cancel_mono (Scheme.Opens.ι _)]; simp [objectCoefficientMaps, limitCoefficientMaps, objectBaseMap, factorization])
      (by rw [preimageCone_π_app, ← cancel_mono (Scheme.Opens.ι _)]; simp [objectCoefficientMaps, limitCoefficientMaps, objectBaseMap, factorization])
      (limitTransitions pairIndex.1 pairIndex.2)
  choose overlapIndex overlapTransitions overlapMaps overlapRecovery using localTransitions
  obtain ⟨mapIndex, mapTransition, mapRefinements, mapFactorization⟩ := IsCofiltered.wideCospan overlapTransitions
  have mapFactorizationAssoc (pairIndex : Chart × Chart) {testScheme : Scheme.{schemeUniverse}} (structureArrow : diagram.obj objectIndex ⟶ testScheme) :
      diagram.map (mapRefinements pairIndex) ≫ diagram.map (overlapTransitions pairIndex) ≫ structureArrow = diagram.map mapTransition ≫ structureArrow := by
    rw [← diagram.map_comp_assoc, mapFactorization]
  let mapBaseMap := structureMap.app mapIndex
  let stageCoefficientMaps (chartIndex : Chart) : (mapBaseMap ⁻¹ᵁ opens chartIndex).toScheme ⟶ coefficientSchemes chartIndex :=
    restrictPreimage (diagram.map (mapTransition ≫ objectTransitions chartIndex)) (by simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using structureMap.naturality (mapTransition ≫ objectTransitions chartIndex)) (le_refl (opens chartIndex))
  let stageTransitions (chartIndex secondIndex : Chart) :
      (modulesPseudofunctor.map
        ((preimageChosenPullback opens mapBaseMap chartIndex secondIndex).p₁ ≫ stageCoefficientMaps chartIndex).op.toLoc).toFunctor.obj (coefficients chartIndex) ⟶
      (modulesPseudofunctor.map
        ((preimageChosenPullback opens mapBaseMap chartIndex secondIndex).p₂ ≫ stageCoefficientMaps secondIndex).op.toLoc).toFunctor.obj (coefficients secondIndex) :=
    pullHom (overlapMaps (chartIndex, secondIndex)) ((preimageDiagram diagram structureMap (opens chartIndex ⊓ opens secondIndex)).map (mapRefinements (chartIndex, secondIndex))) _ _
      (by
        simp only [preimageDiagram_map]
        rw [← cancel_mono (Scheme.Opens.ι _)]
        simp [objectCoefficientMaps, stageCoefficientMaps, objectBaseMap, mapBaseMap, mapFactorizationAssoc])
      (by
        simp only [preimageDiagram_map]
        rw [← cancel_mono (Scheme.Opens.ι _)]
        simp [objectCoefficientMaps, stageCoefficientMaps, objectBaseMap, mapBaseMap, mapFactorizationAssoc])
  have limitStageFactorization (chartIndex : Chart) : restrictPreimage (cone.π.app mapIndex) (factorization mapIndex) (le_refl (opens chartIndex)) ≫ stageCoefficientMaps chartIndex = limitCoefficientMaps chartIndex :=
    restrictPreimage_comp _ _ _ _ (cone.w _) _ _ _ _
  have transitionRecovery : Gluing.pullGlue (transitionMaps := stageTransitions) (changedSquares := preimageChosenPullback opens limitMap)
      (fun chartIndex secondIndex ↦ restrictPreimage (cone.π.app mapIndex) (factorization mapIndex) (le_refl (opens chartIndex ⊓ opens secondIndex)))
      (restrictPreimage_p₁ opens (cone.π.app mapIndex) (factorization mapIndex)) (restrictPreimage_p₂ opens (cone.π.app mapIndex) (factorization mapIndex))
      limitStageFactorization = limitTransitions := by
    funext chartIndex secondIndex
    simp only [Gluing.pullGlue, stageTransitions, pullHom_pullHom]
    rw [← overlapRecovery (chartIndex, secondIndex)]
    refine pullHom_congr_left _ ?_ _ _ _ _
    rw [preimageDiagram_map, preimageCone_π_app]
    exact restrictPreimage_comp _ _ _ _ (cone.w _) _ _ _ _
  have limitIdentity : Gluing.GlueSelf (transitionMaps := limitTransitions) (preimageDiagonal opens limitMap) (preimageDiagonal_p₁ opens limitMap)
      (preimageDiagonal_p₂ opens limitMap) :=
    Gluing.glueSelf_isoGlueHom comparisons _ _ _
  have limitCocycle : Gluing.GlueCocycle (preimageChosenPullback₃ opens limitMap) limitTransitions :=
    Gluing.glueCocycle_isoGlueHom comparisons
  have eventualIdentities (chartIndex : Chart) := by
    letI := affinePreimages (opens chartIndex) (affineOpens chartIndex)
    exact exists_pullHom_eq_of_affine_limit_of_projection_eq (isLimit_preimageCone diagram structureMap cone limitMap factorization limit (opens chartIndex))
      (initialIndex := mapIndex) (firstModule := coefficients chartIndex) (secondModule := coefficients chartIndex) (stageCoefficientMaps chartIndex) (stageCoefficientMaps chartIndex) (firstLimitMap := limitCoefficientMaps chartIndex) (secondLimitMap := limitCoefficientMaps chartIndex)
      (restrictPreimage (cone.π.app mapIndex) (factorization mapIndex) (le_refl (opens chartIndex)))
      (preimageCone_π_app diagram structureMap cone limitMap factorization _ mapIndex)
      (limitStageFactorization chartIndex) (limitStageFactorization chartIndex)
      (Gluing.glueSelfLHS stageTransitions (preimageDiagonal opens mapBaseMap) (preimageDiagonal_p₁ opens mapBaseMap)
        (preimageDiagonal_p₂ opens mapBaseMap) chartIndex) (𝟙 _)
      (by
        rw [Gluing.pullHom_glueSelfLHS (transitionMaps := stageTransitions) (changedSquares := preimageChosenPullback opens limitMap)
            (fun chartIndex secondIndex ↦ restrictPreimage (cone.π.app mapIndex) (factorization mapIndex) (le_refl (opens chartIndex ⊓ opens secondIndex)))
            (restrictPreimage_p₁ opens (cone.π.app mapIndex) (factorization mapIndex))
            (restrictPreimage_p₂ opens (cone.π.app mapIndex) (factorization mapIndex)) limitStageFactorization (preimageDiagonal opens limitMap)
            (preimageDiagonal_p₁ opens limitMap) (preimageDiagonal_p₂ opens limitMap)
            (preimageDiagonal_restrictPreimage opens (cone.π.app mapIndex) (factorization mapIndex)), transitionRecovery, limitIdentity chartIndex]
        exact (pullHom_id_eq_id (F := modulesPseudofunctor)
          (X₁ := coefficientSchemes chartIndex) (M₁ := coefficients chartIndex)
          (Y := (mapBaseMap ⁻¹ᵁ opens chartIndex).toScheme)
          (f₁ := stageCoefficientMaps chartIndex)
          (Y' := (limitMap ⁻¹ᵁ opens chartIndex).toScheme)
          (restrictPreimage (cone.π.app mapIndex) (factorization mapIndex) (le_refl (opens chartIndex)))
          (limitCoefficientMaps chartIndex) (limitStageFactorization chartIndex)).symm)
  choose identityIndex identityTransition identityEquality using eventualIdentities
  have eventualCocycles (tripleIndex : Chart × Chart × Chart) := by
    letI := affinePreimages (opens tripleIndex.1 ⊓ opens tripleIndex.2.1 ⊓ opens tripleIndex.2.2) (affineTriples tripleIndex.1 tripleIndex.2.1 tripleIndex.2.2)
    exact exists_pullHom_eq_of_affine_limit_of_projection_eq
      (isLimit_preimageCone diagram structureMap cone limitMap factorization limit (opens tripleIndex.1 ⊓ opens tripleIndex.2.1 ⊓ opens tripleIndex.2.2)) (initialIndex := mapIndex) (firstModule := coefficients tripleIndex.1)
      (secondModule := coefficients tripleIndex.2.2) ((preimageChosenPullback₃ opens mapBaseMap tripleIndex.1 tripleIndex.2.1 tripleIndex.2.2).p₁ ≫ stageCoefficientMaps tripleIndex.1)
      ((preimageChosenPullback₃ opens mapBaseMap tripleIndex.1 tripleIndex.2.1 tripleIndex.2.2).p₃ ≫ stageCoefficientMaps tripleIndex.2.2)
      (firstLimitMap := (preimageChosenPullback₃ opens limitMap tripleIndex.1 tripleIndex.2.1 tripleIndex.2.2).p₁ ≫ limitCoefficientMaps tripleIndex.1)
      (secondLimitMap := (preimageChosenPullback₃ opens limitMap tripleIndex.1 tripleIndex.2.1 tripleIndex.2.2).p₃ ≫ limitCoefficientMaps tripleIndex.2.2)
      (restrictPreimage (cone.π.app mapIndex) (factorization mapIndex) (le_refl (opens tripleIndex.1 ⊓ opens tripleIndex.2.1 ⊓ opens tripleIndex.2.2)))
      (preimageCone_π_app diagram structureMap cone limitMap factorization _ mapIndex)
      (by rw [← cancel_mono (Scheme.Opens.ι _)]; simp [stageCoefficientMaps, limitCoefficientMaps, mapBaseMap, factorization])
      (by rw [← cancel_mono (Scheme.Opens.ι _)]; simp [stageCoefficientMaps, limitCoefficientMaps, mapBaseMap, factorization])
      (Gluing.glueCocLHS (preimageChosenPullback₃ opens mapBaseMap) stageTransitions tripleIndex.1 tripleIndex.2.1 tripleIndex.2.2)
      (Gluing.glueCocRHS (preimageChosenPullback₃ opens mapBaseMap) stageTransitions tripleIndex.1 tripleIndex.2.1 tripleIndex.2.2)
      (by
        rw [Gluing.pullHom_glueCocLHS (transitionMaps := stageTransitions) (changedSquares := preimageChosenPullback opens limitMap)
            (tripleSquares := preimageChosenPullback₃ opens mapBaseMap) (changedTripleSquares := preimageChosenPullback₃ opens limitMap)
            (secondChange := fun chartIndex secondIndex ↦ restrictPreimage (cone.π.app mapIndex) (factorization mapIndex) (le_refl (opens chartIndex ⊓ opens secondIndex)))
            (hr₂₁ := restrictPreimage_p₁ opens (cone.π.app mapIndex) (factorization mapIndex))
            (hr₂₂ := restrictPreimage_p₂ opens (cone.π.app mapIndex) (factorization mapIndex)) (hμ := limitStageFactorization)
            (r₃ := fun chartIndex secondIndex thirdIndex ↦
              restrictPreimage (cone.π.app mapIndex) (factorization mapIndex) (le_refl (opens chartIndex ⊓ opens secondIndex ⊓ opens thirdIndex)))
            (h₁₂ := restrictPreimage_p₁₂ opens (cone.π.app mapIndex) (factorization mapIndex))
            (h₂₃ := restrictPreimage_p₂₃ opens (cone.π.app mapIndex) (factorization mapIndex))
            (hr₃₁ := restrictPreimage_first opens (cone.π.app mapIndex) (factorization mapIndex))
            (hr₃₂ := restrictPreimage_middle opens (cone.π.app mapIndex) (factorization mapIndex))
            (hr₃₃ := restrictPreimage_last opens (cone.π.app mapIndex) (factorization mapIndex)),
          Gluing.pullHom_glueCocRHS (transitionMaps := stageTransitions) (changedSquares := preimageChosenPullback opens limitMap)
            (tripleSquares := preimageChosenPullback₃ opens mapBaseMap) (changedTripleSquares := preimageChosenPullback₃ opens limitMap)
            (secondChange := fun chartIndex secondIndex ↦ restrictPreimage (cone.π.app mapIndex) (factorization mapIndex) (le_refl (opens chartIndex ⊓ opens secondIndex)))
            (hr₂₁ := restrictPreimage_p₁ opens (cone.π.app mapIndex) (factorization mapIndex))
            (hr₂₂ := restrictPreimage_p₂ opens (cone.π.app mapIndex) (factorization mapIndex)) (hμ := limitStageFactorization)
            (r₃ := fun chartIndex secondIndex thirdIndex ↦
              restrictPreimage (cone.π.app mapIndex) (factorization mapIndex) (le_refl (opens chartIndex ⊓ opens secondIndex ⊓ opens thirdIndex)))
            (h₁₃ := restrictPreimage_p₁₃ opens (cone.π.app mapIndex) (factorization mapIndex))
            (hr₃₁ := restrictPreimage_first opens (cone.π.app mapIndex) (factorization mapIndex))
            (hr₃₃ := restrictPreimage_last opens (cone.π.app mapIndex) (factorization mapIndex)), transitionRecovery]
        exact limitCocycle tripleIndex.1 tripleIndex.2.1 tripleIndex.2.2)
  choose cocycleIndex cocycleTransition cocycleEquality using eventualCocycles
  obtain ⟨finalIndex, finalTransition, finalRefinements, finalFactorization⟩ := IsCofiltered.wideCospan (I := Chart ⊕ (Chart × Chart × Chart))
    (j := Sum.elim identityIndex cocycleIndex) (fun structureArrow ↦ match structureArrow with
      | .inl chartIndex => identityTransition chartIndex
      | .inr tripleIndex => cocycleTransition tripleIndex)
  let finalBaseMap := structureMap.app finalIndex
  have finalBaseFactorization : diagram.map finalTransition ≫ mapBaseMap = finalBaseMap := by simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using structureMap.naturality finalTransition
  let finalCoefficientMaps (chartIndex : Chart) : (finalBaseMap ⁻¹ᵁ opens chartIndex).toScheme ⟶ coefficientSchemes chartIndex :=
    restrictPreimage (diagram.map (finalTransition ≫ mapTransition ≫ objectTransitions chartIndex)) (by simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using structureMap.naturality (finalTransition ≫ mapTransition ≫ objectTransitions chartIndex))
      (le_refl (opens chartIndex))
  have finalStageFactorization (chartIndex : Chart) : restrictPreimage (diagram.map finalTransition) finalBaseFactorization (le_refl (opens chartIndex)) ≫ stageCoefficientMaps chartIndex = finalCoefficientMaps chartIndex :=
    restrictPreimage_comp _ _ _ _ (by rw [← diagram.map_comp]) _ _ _ _
  let finalTransitions := Gluing.pullGlue (transitionMaps := stageTransitions) (changedSquares := preimageChosenPullback opens finalBaseMap)
    (fun chartIndex secondIndex ↦ restrictPreimage (diagram.map finalTransition) finalBaseFactorization (le_refl (opens chartIndex ⊓ opens secondIndex))) (restrictPreimage_p₁ opens _ finalBaseFactorization)
    (restrictPreimage_p₂ opens _ finalBaseFactorization) finalStageFactorization
  have finalIdentity : Gluing.GlueSelf (transitionMaps := finalTransitions) (preimageDiagonal opens finalBaseMap) (preimageDiagonal_p₁ opens finalBaseMap)
      (preimageDiagonal_p₂ opens finalBaseMap) := fun chartIndex ↦ by
    rw [← Gluing.pullHom_glueSelfLHS (transitionMaps := stageTransitions) (changedSquares := preimageChosenPullback opens finalBaseMap)
      (diagonals := preimageDiagonal opens mapBaseMap) (hd₁ := preimageDiagonal_p₁ opens mapBaseMap) (hd₂ := preimageDiagonal_p₂ opens mapBaseMap)
      (fun chartIndex secondIndex ↦ restrictPreimage (diagram.map finalTransition) finalBaseFactorization (le_refl (opens chartIndex ⊓ opens secondIndex))) (restrictPreimage_p₁ opens _ finalBaseFactorization)
      (restrictPreimage_p₂ opens _ finalBaseFactorization) finalStageFactorization (preimageDiagonal opens finalBaseMap) (preimageDiagonal_p₁ opens finalBaseMap) (preimageDiagonal_p₂ opens finalBaseMap)
      (preimageDiagonal_restrictPreimage opens (diagram.map finalTransition) finalBaseFactorization)]
    have restrictionFactorization : restrictPreimage (diagram.map finalTransition) finalBaseFactorization (le_refl (opens chartIndex)) =
        restrictPreimage (diagram.map (finalRefinements (.inl chartIndex)))
          (by simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using structureMap.naturality (finalRefinements (.inl chartIndex))) (le_refl (opens chartIndex)) ≫
        (preimageDiagram diagram structureMap (opens chartIndex)).map (identityTransition chartIndex) := by
      rw [preimageDiagram_map]
      exact (restrictPreimage_comp _ _ _ _ (by rw [← diagram.map_comp, ← finalFactorization (.inl chartIndex)])
        _ _ _ _).symm
    rw [pullHom_congr_left _ restrictionFactorization, ← pullHom_pullHom (g := (preimageDiagram diagram structureMap (opens chartIndex)).map (identityTransition chartIndex))
      (gf₁ := (preimageDiagram diagram structureMap (opens chartIndex)).map (identityTransition chartIndex) ≫ stageCoefficientMaps chartIndex)
      (gf₂ := (preimageDiagram diagram structureMap (opens chartIndex)).map (identityTransition chartIndex) ≫ stageCoefficientMaps chartIndex) (hgf₁ := rfl) (hgf₂ := rfl)
      (g'f₁ := finalCoefficientMaps chartIndex) (g'f₂ := finalCoefficientMaps chartIndex) (hg'f₁ := by rw [← Category.assoc, ← restrictionFactorization, finalStageFactorization])
      (hg'f₂ := by rw [← Category.assoc, ← restrictionFactorization, finalStageFactorization]), identityEquality chartIndex,
      pullHom_pullHom]
    exact pullHom_id_eq_id (F := modulesPseudofunctor)
      (X₁ := coefficientSchemes chartIndex) (M₁ := coefficients chartIndex)
      (Y := (mapBaseMap ⁻¹ᵁ opens chartIndex).toScheme)
      (f₁ := stageCoefficientMaps chartIndex)
      (Y' := (finalBaseMap ⁻¹ᵁ opens chartIndex).toScheme)
      (restrictPreimage (diagram.map (finalRefinements (.inl chartIndex)))
        (by simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using structureMap.naturality (finalRefinements (.inl chartIndex)))
        (le_refl (opens chartIndex)) ≫
        (preimageDiagram diagram structureMap (opens chartIndex)).map (identityTransition chartIndex))
      (finalCoefficientMaps chartIndex)
      (by rw [← restrictionFactorization, finalStageFactorization])
  have finalCocycle : Gluing.GlueCocycle (preimageChosenPullback₃ opens finalBaseMap) finalTransitions := fun chartIndex secondIndex thirdIndex ↦ by
    have restrictionFactorization : restrictPreimage (diagram.map finalTransition) finalBaseFactorization (le_refl (opens chartIndex ⊓ opens secondIndex ⊓ opens thirdIndex)) =
        restrictPreimage (diagram.map (finalRefinements (.inr (chartIndex, secondIndex, thirdIndex))))
          (by simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using structureMap.naturality (finalRefinements (.inr (chartIndex, secondIndex, thirdIndex)))) (le_refl (opens chartIndex ⊓ opens secondIndex ⊓ opens thirdIndex)) ≫
        (preimageDiagram diagram structureMap (opens chartIndex ⊓ opens secondIndex ⊓ opens thirdIndex)).map (cocycleTransition (chartIndex, secondIndex, thirdIndex)) := by
      rw [preimageDiagram_map]
      exact (restrictPreimage_comp _ _ _ _
        (by rw [← diagram.map_comp, ← finalFactorization (.inr (chartIndex, secondIndex, thirdIndex))]) _ _ _ _).symm
    have equation := cocycleEquality (chartIndex, secondIndex, thirdIndex)
    dsimp only at equation
    rw [← Gluing.pullHom_glueCocLHS (transitionMaps := stageTransitions) (changedSquares := preimageChosenPullback opens finalBaseMap)
        (tripleSquares := preimageChosenPullback₃ opens mapBaseMap) (changedTripleSquares := preimageChosenPullback₃ opens finalBaseMap)
        (secondChange := fun chartIndex secondIndex ↦ restrictPreimage (diagram.map finalTransition) finalBaseFactorization (le_refl (opens chartIndex ⊓ opens secondIndex)))
        (hr₂₁ := restrictPreimage_p₁ opens _ finalBaseFactorization) (hr₂₂ := restrictPreimage_p₂ opens _ finalBaseFactorization) (hμ := finalStageFactorization)
        (r₃ := fun chartIndex secondIndex thirdIndex ↦ restrictPreimage (diagram.map finalTransition) finalBaseFactorization (le_refl (opens chartIndex ⊓ opens secondIndex ⊓ opens thirdIndex)))
        (h₁₂ := restrictPreimage_p₁₂ opens _ finalBaseFactorization) (h₂₃ := restrictPreimage_p₂₃ opens _ finalBaseFactorization) (hr₃₁ := restrictPreimage_first opens _ finalBaseFactorization)
        (hr₃₂ := restrictPreimage_middle opens _ finalBaseFactorization) (hr₃₃ := restrictPreimage_last opens _ finalBaseFactorization),
      ← Gluing.pullHom_glueCocRHS (transitionMaps := stageTransitions) (changedSquares := preimageChosenPullback opens finalBaseMap)
        (tripleSquares := preimageChosenPullback₃ opens mapBaseMap) (changedTripleSquares := preimageChosenPullback₃ opens finalBaseMap)
        (secondChange := fun chartIndex secondIndex ↦ restrictPreimage (diagram.map finalTransition) finalBaseFactorization (le_refl (opens chartIndex ⊓ opens secondIndex)))
        (hr₂₁ := restrictPreimage_p₁ opens _ finalBaseFactorization) (hr₂₂ := restrictPreimage_p₂ opens _ finalBaseFactorization) (hμ := finalStageFactorization)
        (r₃ := fun chartIndex secondIndex thirdIndex ↦ restrictPreimage (diagram.map finalTransition) finalBaseFactorization (le_refl (opens chartIndex ⊓ opens secondIndex ⊓ opens thirdIndex)))
        (h₁₃ := restrictPreimage_p₁₃ opens _ finalBaseFactorization) (hr₃₁ := restrictPreimage_first opens _ finalBaseFactorization) (hr₃₃ := restrictPreimage_last opens _ finalBaseFactorization),
      pullHom_congr_left _ restrictionFactorization, pullHom_congr_left _ restrictionFactorization]
    have firstFactorization : restrictPreimage (diagram.map (finalRefinements (.inr (chartIndex, secondIndex, thirdIndex))))
        (by simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using structureMap.naturality (finalRefinements (.inr (chartIndex, secondIndex, thirdIndex)))) (le_refl (opens chartIndex ⊓ opens secondIndex ⊓ opens thirdIndex)) ≫
        ((preimageDiagram diagram structureMap (opens chartIndex ⊓ opens secondIndex ⊓ opens thirdIndex)).map (cocycleTransition (chartIndex, secondIndex, thirdIndex)) ≫
          (preimageChosenPullback₃ opens mapBaseMap chartIndex secondIndex thirdIndex).p₁ ≫ stageCoefficientMaps chartIndex) =
        (preimageChosenPullback₃ opens finalBaseMap chartIndex secondIndex thirdIndex).p₁ ≫ finalCoefficientMaps chartIndex := by
      rw [← Category.assoc, ← restrictionFactorization, ← finalStageFactorization, ← Category.assoc, ← Category.assoc,
        restrictPreimage_first opens _ finalBaseFactorization]
    have thirdFactorization : restrictPreimage (diagram.map (finalRefinements (.inr (chartIndex, secondIndex, thirdIndex))))
        (by simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using structureMap.naturality (finalRefinements (.inr (chartIndex, secondIndex, thirdIndex)))) (le_refl (opens chartIndex ⊓ opens secondIndex ⊓ opens thirdIndex)) ≫
        ((preimageDiagram diagram structureMap (opens chartIndex ⊓ opens secondIndex ⊓ opens thirdIndex)).map (cocycleTransition (chartIndex, secondIndex, thirdIndex)) ≫
          (preimageChosenPullback₃ opens mapBaseMap chartIndex secondIndex thirdIndex).p₃ ≫ stageCoefficientMaps thirdIndex) =
        (preimageChosenPullback₃ opens finalBaseMap chartIndex secondIndex thirdIndex).p₃ ≫ finalCoefficientMaps thirdIndex := by
      rw [← Category.assoc, ← restrictionFactorization, ← finalStageFactorization, ← Category.assoc, ← Category.assoc,
        restrictPreimage_last opens _ finalBaseFactorization]
    rw [← pullHom_pullHom (g := (preimageDiagram diagram structureMap (opens chartIndex ⊓ opens secondIndex ⊓ opens thirdIndex)).map (cocycleTransition (chartIndex, secondIndex, thirdIndex)))
        (hgf₁ := rfl) (hgf₂ := rfl) (hg'f₁ := firstFactorization) (hg'f₂ := thirdFactorization),
      ← pullHom_pullHom (g := (preimageDiagram diagram structureMap (opens chartIndex ⊓ opens secondIndex ⊓ opens thirdIndex)).map (cocycleTransition (chartIndex, secondIndex, thirdIndex)))
        (hgf₁ := rfl) (hgf₂ := rfl) (hg'f₁ := firstFactorization) (hg'f₂ := thirdFactorization), equation]
  have finalCover : ⨆ chartIndex : Chart, (finalBaseMap ⁻¹ᵁ opens chartIndex).ι.opensRange = ⊤ := by
    simp only [Scheme.Opens.opensRange_ι, ← Scheme.Hom.preimage_iSup, cover,
      Scheme.Hom.preimage_top]
  have limitCover : ⨆ chartIndex : Chart, (limitMap ⁻¹ᵁ opens chartIndex).ι.opensRange = ⊤ := by
    simp only [Scheme.Opens.opensRange_ι, ← Scheme.Hom.preimage_iSup, cover,
      Scheme.Hom.preimage_top]
  obtain ⟨stageModule, -, ⟨descentComparison⟩⟩ := exists_isQuasicoherent_toDescentData_iso_of_mem_fpqcTopology
    (fun chartIndex : Chart ↦ (finalBaseMap ⁻¹ᵁ opens chartIndex).ι) (ofArrows_mem_fpqcTopology_of_isOpenImmersion _ finalCover)
    (Gluing.ofGlue (preimageChosenPullback₃ opens finalBaseMap) finalCoefficientMaps coefficients finalTransitions finalIdentity finalCocycle).descentData
    (fun chartIndex ↦ by
      change ((Modules.pullback (finalCoefficientMaps chartIndex)).obj (coefficients chartIndex)).IsQuasicoherent
      infer_instance)
  have finiteStageModule : (stageModule : (diagram.obj finalIndex).Modules).IsFinitePresentation := by
    refine isFinitePresentation_of_isOpenImmersion _ (fun chartIndex : Chart ↦ (finalBaseMap ⁻¹ᵁ opens chartIndex).ι) finalCover
      fun chartIndex ↦ ?_
    have chartComparison : (Modules.pullback (finalBaseMap ⁻¹ᵁ opens chartIndex).ι).obj (stageModule : (diagram.obj finalIndex).Modules) ≅
        (Modules.pullback (finalCoefficientMaps chartIndex)).obj (coefficients chartIndex) :=
      { hom := descentComparison.hom.hom chartIndex
        inv := descentComparison.inv.hom chartIndex
        hom_inv_id := by rw [← DescentData.comp_hom, descentComparison.hom_inv_id]; rfl
        inv_hom_id := by rw [← DescentData.comp_hom, descentComparison.inv_hom_id]; rfl }
    exact (SheafOfModules.isFinitePresentation
      (finalBaseMap ⁻¹ᵁ opens chartIndex).toScheme.ringCatSheaf).prop_of_iso
        chartComparison.symm inferInstance
  have limitFinalFactorization (chartIndex : Chart) : restrictPreimage (cone.π.app finalIndex) (factorization finalIndex) (le_refl (opens chartIndex)) ≫ finalCoefficientMaps chartIndex = limitCoefficientMaps chartIndex :=
    restrictPreimage_comp _ _ _ _ (cone.w _) _ _ _ _
  have finalRecovery (chartIndex secondIndex : Chart) : pullHom (finalTransitions chartIndex secondIndex)
      (restrictPreimage (cone.π.app finalIndex) (factorization finalIndex) (le_refl (opens chartIndex ⊓ opens secondIndex)))
      ((preimageChosenPullback opens limitMap chartIndex secondIndex).p₁ ≫ limitCoefficientMaps chartIndex) ((preimageChosenPullback opens limitMap chartIndex secondIndex).p₂ ≫ limitCoefficientMaps secondIndex)
      (by rw [reassoc_of% (restrictPreimage_p₁ opens _ (factorization finalIndex) chartIndex secondIndex), limitFinalFactorization])
      (by rw [reassoc_of% (restrictPreimage_p₂ opens _ (factorization finalIndex) chartIndex secondIndex), limitFinalFactorization]) = limitTransitions chartIndex secondIndex := by
    have equation := congrFun (congrFun transitionRecovery chartIndex) secondIndex
    refine Eq.trans ?_ equation
    simp only [finalTransitions, Gluing.pullGlue, pullHom_pullHom]
    exact pullHom_congr_left _ (restrictPreimage_comp _ _ _ _ (cone.w finalTransition) _ _ _ _) _ _ _ _
  obtain ⟨comparison⟩ := Gluing.nonempty_map_iso_of_ofGlue descentComparison (preimageChosenPullback opens limitMap)
    (fun sourceModule coefficients ↦ bijective_toDescentData_map_of_isOpenImmersion _ limitCover sourceModule coefficients) (cone.π.app finalIndex)
    (fun chartIndex ↦ restrictPreimage (cone.π.app finalIndex) (factorization finalIndex) (le_refl (opens chartIndex))) (fun chartIndex ↦ restrictPreimage_ι _ _ _)
    (fun chartIndex secondIndex ↦ restrictPreimage (cone.π.app finalIndex) (factorization finalIndex) (le_refl (opens chartIndex ⊓ opens secondIndex)))
    (restrictPreimage_p₁ opens _ (factorization finalIndex)) (restrictPreimage_p₂ opens _ (factorization finalIndex)) limitCoefficientMaps limitFinalFactorization moduleSheaf comparisons finalRecovery
  exact ⟨finalIndex, stageModule, finiteStageModule, ⟨comparison⟩⟩

/-- Finitely presented coefficient objects descend along directed inverse limits of
quasi-compact separated schemes with affine transition morphisms. No stage
coefficient object or overlap compatibility is assumed. -/
theorem exists_isFinitePresentation_pullback_iso_of_isLimit
    {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] (diagram : Indexᵒᵖ ⥤ Scheme.{schemeUniverse})
    [∀ {sourceIndex targetIndex : Indexᵒᵖ} (transition : sourceIndex ⟶ targetIndex),
      IsAffineHom (diagram.map transition)]
    [∀ stageIndex, CompactSpace (diagram.obj stageIndex)]
    [∀ stageIndex, (diagram.obj stageIndex).IsSeparated]
    (cone : Cone diagram) (limit : IsLimit cone)
    (moduleSheaf : cone.pt.Modules) [moduleSheaf.IsFinitePresentation] :
    ∃ (stageIndex : Index) (stageModule : (diagram.obj (op stageIndex)).Modules),
      stageModule.IsFinitePresentation ∧
        Nonempty ((pullback (cone.π.app (op stageIndex))).obj stageModule ≅ moduleSheaf) := by
  classical
  let initialIndex : Index := Classical.arbitrary Index
  let baseScheme := diagram.obj (op initialIndex)
  letI : CompactSpace baseScheme :=
    inferInstanceAs (CompactSpace (diagram.obj (op initialIndex)))
  letI : baseScheme.IsSeparated :=
    inferInstanceAs ((diagram.obj (op initialIndex)).IsSeparated)
  obtain ⟨coverMembers, finiteCover⟩ := (isCompact_univ (X := baseScheme)).elim_finite_subcover
    (fun affineOpen : baseScheme.affineOpens ↦ ((affineOpen : baseScheme.Opens) : Set baseScheme))
    (fun affineOpen ↦ affineOpen.1.2) (fun point _ ↦ by
      obtain ⟨affineOpen, pointInOpen⟩ := TopologicalSpace.Opens.mem_iSup.mp
        ((iSup_affineOpens_eq_top baseScheme).ge (Set.mem_univ point) :
          point ∈ ⨆ affineOpen : baseScheme.affineOpens, (affineOpen : baseScheme.Opens))
      exact Set.mem_iUnion.mpr ⟨affineOpen, pointInOpen⟩)
  let opens (chartIndex : coverMembers) : baseScheme.Opens := chartIndex.val.val
  have affineOpens (chartIndex : coverMembers) : IsAffineOpen (opens chartIndex) :=
    chartIndex.val.property
  have cover : ⨆ chartIndex, opens chartIndex = ⊤ := eq_top_iff.mpr fun point _ ↦ by
    obtain ⟨affineOpen, member, pointInOpen⟩ :=
      Set.mem_iUnion₂.mp (finiteCover (Set.mem_univ point))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨affineOpen, member⟩, pointInOpen⟩
  let Tail := {stageIndex : Index // initialIndex ≤ stageIndex}
  letI : Nonempty Tail := ⟨⟨initialIndex, le_rfl⟩⟩
  letI : IsDirectedOrder Tail := ⟨by
    intro firstIndex secondIndex
    obtain ⟨commonIndex, firstLe, secondLe⟩ := exists_ge_ge firstIndex.val secondIndex.val
    exact ⟨⟨commonIndex, firstIndex.property.trans firstLe⟩, firstLe, secondLe⟩⟩
  let inclusion : Tail ⥤ Index :=
    (Subtype.mono_coe (fun stageIndex : Index ↦ initialIndex ≤ stageIndex)).functor
  letI : inclusion.Final := (Monotone.final_functor_iff _).mpr (by
    intro stageIndex
    obtain ⟨commonIndex, initialLe, stageLe⟩ := exists_ge_ge initialIndex stageIndex
    exact ⟨⟨commonIndex, initialLe⟩, stageLe⟩)
  let stageDiagram : Tailᵒᵖ ⥤ Scheme.{schemeUniverse} := inclusion.op ⋙ diagram
  let stageCone : Cone stageDiagram := cone.whisker inclusion.op
  have stageLimit : IsLimit stageCone :=
    (Functor.Initial.isLimitWhiskerEquiv inclusion.op cone).symm limit
  let structureMap : stageDiagram ⟶ (Functor.const Tailᵒᵖ).obj baseScheme :=
    { app := fun stageIndex ↦ diagram.map (homOfLE stageIndex.unop.property).op
      naturality := by
        intro sourceIndex targetIndex transition
        change diagram.map (inclusion.op.map transition) ≫ diagram.map _ =
          diagram.map _ ≫ 𝟙 _
        rw [Category.comp_id, ← diagram.map_comp]
        rfl }
  letI : ∀ stageIndex, IsAffineHom (structureMap.app stageIndex) := fun stageIndex ↦ by
    change IsAffineHom (diagram.map (homOfLE stageIndex.unop.property).op)
    infer_instance
  have factorization (stageIndex : Tailᵒᵖ) :
      stageCone.π.app stageIndex ≫ structureMap.app stageIndex =
        cone.π.app (op initialIndex) := cone.w (homOfLE stageIndex.unop.property).op
  obtain ⟨stageIndex, stageModule, finiteStageModule, comparison⟩ :=
    exists_isFinitePresentation_model_of_finite_affine_cover stageDiagram structureMap
      stageCone stageLimit (cone.π.app (op initialIndex)) factorization
      opens affineOpens cover moduleSheaf
  exact ⟨stageIndex.unop.val, stageModule, finiteStageModule, comparison⟩

end AlgebraicGeometry.Scheme.Modules
