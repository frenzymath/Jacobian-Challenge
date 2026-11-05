import Jacobian.Algebra.Category.Ring.FinitePresentation
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Descent of affine finitely presented schemes

An affine scheme of finite presentation over a cofiltered limit of affine schemes
is the base change of an affine scheme of finite presentation at a finite stage.
The proof reduces to descent of finitely presented algebras along filtered
colimits of commutative rings.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {Index : Type schemeUniverse} [Category.{schemeUniverse} Index]
  (diagram : Index ⥤ Scheme.{schemeUniverse}) (cone : Cone diagram) (limit : IsLimit cone)

include limit in
/-- An affine scheme of finite presentation over a cofiltered limit of affine
schemes is obtained by base change from a finitely presented affine stage. -/
lemma Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine [IsCofiltered Index]
    [∀ {sourceIndex targetIndex} (transition : sourceIndex ⟶ targetIndex),
      IsAffineHom (diagram.map transition)] [∀ index, IsAffine (diagram.obj index)]
    {sourceScheme : Scheme.{schemeUniverse}} [IsAffine sourceScheme]
    (sourceMap : sourceScheme ⟶ cone.pt) [LocallyOfFinitePresentation sourceMap] :
    ∃ (stage : Index) (stageScheme : Scheme.{schemeUniverse}) (_ : IsAffine stageScheme)
      (stageMap : stageScheme ⟶ diagram.obj stage) (_ : LocallyOfFinitePresentation stageMap)
      (comparison : sourceScheme ⟶ stageScheme),
      IsPullback comparison sourceMap stageMap (cone.π.app stage) := by
  have limitAffine : IsAffine cone.pt := Scheme.isAffine_of_isLimit cone limit
  wlog sourceIsSpectrum : ∃ sourceRing, sourceScheme = Spec sourceRing generalizing sourceScheme
  · obtain ⟨stage, stageScheme, stageAffine, stageMap, stage_finitePresentation,
        comparison, square⟩ :=
      this (sourceScheme := Spec Γ(sourceScheme, ⊤))
        (sourceScheme.isoSpec.inv ≫ sourceMap) ⟨_, rfl⟩
    refine ⟨stage, stageScheme, stageAffine, stageMap, stage_finitePresentation,
      sourceScheme.isoSpec.hom ≫ comparison, ?_⟩
    simpa using (IsPullback.of_horiz_isIso (fst := sourceScheme.isoSpec.hom) (snd := sourceMap)
      (f := sourceScheme.isoSpec.inv ≫ sourceMap) (g := 𝟙 cone.pt) ⟨by simp⟩).paste_horiz square
  obtain ⟨sourceRing, rfl⟩ := sourceIsSpectrum
  wlog diagramIsSpec : ∃ ringDiagram : Index ⥤ CommRingCatᵒᵖ,
      diagram = ringDiagram ⋙ Scheme.Spec generalizing diagram
  · let affinization : diagram ⟶ diagram ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec :=
      diagram.whiskerLeft ΓSpec.adjunction.unit
    haveI componentIsomorphisms : ∀ index : Index, IsIso (affinization.app index) :=
      fun index ↦ IsAffine.affine
    haveI affinizationIsomorphism : IsIso affinization := NatIso.isIso_of_isIso_app affinization
    haveI affineStages : ∀ index : Index,
        IsAffine ((diagram ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec).obj index) :=
      fun index ↦ inferInstanceAs (IsAffine (Spec _))
    haveI affineTransitions : ∀ {sourceIndex targetIndex : Index}
        (transition : sourceIndex ⟶ targetIndex),
        IsAffineHom ((diagram ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec).map transition) := by
      intro sourceIndex targetIndex transition
      change IsAffineHom (Spec.map (Scheme.Γ.map ((diagram.map transition).op)))
      infer_instance
    have source_finitePresentation : @LocallyOfFinitePresentation (Spec sourceRing)
        ((Cone.postcompose (asIso affinization).hom).obj cone).pt sourceMap := ‹_›
    obtain ⟨stage, stageScheme, stageAffine, stageMap, stage_finitePresentation,
        comparison, square⟩ :=
      this _ _ ((IsLimit.postcomposeHomEquiv (asIso affinization) cone).symm limit)
        limitAffine sourceMap ⟨diagram ⋙ Scheme.Γ.rightOp, rfl⟩
    have : LocallyOfFinitePresentation (stageMap ≫ inv (affinization.app stage)) := by
      have := stage_finitePresentation
      infer_instance
    refine ⟨stage, stageScheme, stageAffine, stageMap ≫ inv (affinization.app stage),
      this, comparison, ?_⟩
    refine square.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (asIso (affinization.app stage)).symm
      (by simp) (Category.comp_id sourceMap) (by simp) ?_
    change (cone.π.app stage ≫ affinization.app stage) ≫ inv (affinization.app stage) =
      𝟙 _ ≫ cone.π.app stage
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    exact (Category.id_comp (cone.π.app stage)).symm
  obtain ⟨diagram, rfl⟩ := diagramIsSpec
  wlog coneIsSpec : ∃ ringCocone : Cocone diagram.leftOp,
      cone = Scheme.Spec.mapCone (coneOfCoconeLeftOp ringCocone) generalizing cone
  · let limitSpecIso : cone.pt ≅ Spec Γ(cone.pt, ⊤) := cone.pt.isoSpec
    let projections : ∀ index : Indexᵒᵖ, diagram.leftOp.obj index ⟶ Γ(cone.pt, ⊤) :=
      fun index ↦ (Scheme.Spec.preimage (limitSpecIso.inv ≫ cone.π.app index.unop)).unop
    have projections_eq : ∀ index : Indexᵒᵖ,
        Spec.map (projections index) = limitSpecIso.inv ≫ cone.π.app index.unop :=
      fun index ↦ Scheme.Spec.map_preimage _
    let ringCocone : Cocone diagram.leftOp :=
      { pt := Γ(cone.pt, ⊤)
        ι :=
          { app := projections
            naturality sourceIndex targetIndex transition := by
              apply Quiver.Hom.op_inj
              apply Scheme.Spec.map_injective
              change Spec.map (diagram.leftOp.map transition ≫ projections targetIndex) =
                Spec.map (projections sourceIndex ≫ 𝟙 _)
              rw [Spec.map_comp, Spec.map_comp, projections_eq, projections_eq,
                Spec.map_id, Category.id_comp]
              exact (Category.assoc _ _ _).trans
                (congrArg (limitSpecIso.inv ≫ ·) (cone.w transition.unop)) } }
    have coneIso : cone ≅ Scheme.Spec.mapCone (coneOfCoconeLeftOp ringCocone) :=
      Cone.ext limitSpecIso fun index ↦ by
        change cone.π.app index = limitSpecIso.hom ≫ Spec.map (projections (Opposite.op index))
        rw [projections_eq]
        exact (Iso.hom_inv_id_assoc limitSpecIso (cone.π.app index)).symm
    obtain ⟨stage, stageScheme, stageAffine, stageMap, stage_finitePresentation,
        comparison, square⟩ :=
      this (Scheme.Spec.mapCone (coneOfCoconeLeftOp ringCocone))
        (IsLimit.ofIsoLimit limit coneIso) (inferInstanceAs (IsAffine (Spec Γ(cone.pt, ⊤))))
        (sourceMap ≫ limitSpecIso.hom) ⟨ringCocone, rfl⟩
    refine ⟨stage, stageScheme, stageAffine, stageMap, stage_finitePresentation, comparison, ?_⟩
    refine square.of_iso (Iso.refl _) (Iso.refl _) limitSpecIso.symm (Iso.refl _)
      (by simp) (by simp) (by simp) ?_
    change Spec.map (projections (Opposite.op stage)) ≫ 𝟙 _ =
      limitSpecIso.inv ≫ cone.π.app stage
    rw [Category.comp_id]
    exact projections_eq (Opposite.op stage)
  obtain ⟨ringCocone, rfl⟩ := coneIsSpec
  obtain ⟨ringMap, rfl⟩ := Spec.map_surjective sourceMap
  replace limit := isColimitOfConeOfCoconeLeftOp _ (isLimitOfReflects Scheme.Spec limit)
  obtain ⟨stage, stageRing, stageMap, stage_finitePresentation, comparison, pushout⟩ :=
    CommRingCat.exists_isPushout_of_finitePresentation diagram.leftOp ringCocone limit ringMap
      (HasRingHomProperty.Spec_iff.mp ‹LocallyOfFinitePresentation (Spec.map ringMap)›)
  refine ⟨stage.unop, Spec stageRing, inferInstance, Spec.map stageMap,
    HasRingHomProperty.Spec_iff.mpr stage_finitePresentation, Spec.map comparison, ?_⟩
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ pushout).flip

end AlgebraicGeometry
