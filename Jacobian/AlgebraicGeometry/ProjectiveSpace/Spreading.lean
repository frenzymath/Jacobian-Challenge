import Jacobian.AlgebraicGeometry.ProjectiveSpace.Charts
import Jacobian.Algebra.Category.Ring.FGSubalgebras
import Jacobian.AlgebraicGeometry.Limits.AffineOpens
import Jacobian.AlgebraicGeometry.Limits.BaseChange
import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Spreading affine projective charts to a finite field extension

Finite-presentation limit arguments descend the morphism and affineness of
its finitely many chart preimages, then specialization yields a finite field extension.
-/

set_option backward.isDefEq.respectTransparency false

set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

section
universe schemeUniverse

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

open CommRingCat

lemma ProjectiveSpace.map_preimage_standardOpen {exponent : Type schemeUniverse} {base testScheme : Scheme.{schemeUniverse}} (compatibility : base ⟶ testScheme)
    (index : exponent) : ProjectiveSpace.map exponent compatibility ⁻¹ᵁ ProjectiveSpace.standardOpen exponent testScheme index =
      ProjectiveSpace.standardOpen exponent base index := by
  rw [ProjectiveSpace.standardOpen, ← Scheme.Hom.comp_preimage, ProjectiveSpace.map_toIntegralModel]
  rfl

lemma ProjectiveSpace.liftBaseChange_preimage_standardOpen {exponent : Type schemeUniverse} {scheme base testScheme : Scheme.{schemeUniverse}}
    {structureMap : scheme ⟶ base} (coordinate : testScheme ⟶ scheme) (otherCoordinate : testScheme ⟶ ℙ(exponent; base)) (member : coordinate ≫ structureMap = otherCoordinate ≫ ℙ(exponent; base) ↘ base) (index : exponent) :
    ProjectiveSpace.liftBaseChange coordinate otherCoordinate member ⁻¹ᵁ ProjectiveSpace.standardOpen exponent scheme index =
      otherCoordinate ⁻¹ᵁ ProjectiveSpace.standardOpen exponent base index := by
  rw [ProjectiveSpace.standardOpen, ProjectiveSpace.standardOpen, ← Scheme.Hom.comp_preimage,
    ProjectiveSpace.liftBaseChange_toIntegralModel, Scheme.Hom.comp_preimage]

theorem exists_finite_isAffineOpen_preimage_standardOpen {baseField extensionField : Type schemeUniverse} [Field baseField] [Field extensionField]
    [Algebra baseField extensionField] {scheme : Scheme.{schemeUniverse}} (function : scheme ⟶ Spec (.of baseField)) [CompactSpace scheme]
    [QuasiSeparatedSpace scheme] {homogeneousIndex : Type schemeUniverse} [Finite homogeneousIndex]
    (projectiveMap : pullback function (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) ⟶ ℙ(homogeneousIndex; Spec (.of extensionField)))
    (hψo : projectiveMap ≫ ℙ(homogeneousIndex; Spec (.of extensionField)) ↘ Spec (.of extensionField) = pullback.snd _ _)
    (hψ : ∀ chosenIndex, IsAffineOpen (projectiveMap ⁻¹ᵁ ProjectiveSpace.standardOpen homogeneousIndex (Spec (.of extensionField)) chosenIndex)) :
    ∃ (finiteExtension : Type schemeUniverse) (_ : Field finiteExtension) (_ : Algebra baseField finiteExtension) (_ : Module.Finite baseField finiteExtension)
      (source : Scheme.{schemeUniverse}) (projection : source ⟶ scheme) (extensionStructure : source ⟶ Spec (.of finiteExtension))
      (_ : IsPullback projection extensionStructure function (Spec.map (CommRingCat.ofHom (algebraMap baseField finiteExtension))))
      (descendedMap : source ⟶ ℙ(homogeneousIndex; Spec (.of finiteExtension))),
        ∀ chosenIndex, IsAffineOpen (descendedMap ⁻¹ᵁ ProjectiveSpace.standardOpen homogeneousIndex (Spec (.of finiteExtension)) chosenIndex) := by
  classical
  have := Fintype.ofFinite homogeneousIndex
  let stageIndex := {baseRing : Subalgebra baseField extensionField // baseRing.FG}
  have : Nonempty stageIndex := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  have : IsDirectedOrder stageIndex := ⟨fun baseRing extensionRing ↦ ⟨⟨baseRing.1 ⊔ extensionRing.1, baseRing.2.sup extensionRing.2⟩,
    show baseRing.1 ≤ baseRing.1 ⊔ extensionRing.1 from le_sup_left, show extensionRing.1 ≤ baseRing.1 ⊔ extensionRing.1 from le_sup_right⟩⟩
  let D : stageIndexᵒᵖ ⥤ Scheme.{schemeUniverse} := (fgSubalgebraDiagramOf baseField extensionField).op ⋙ Scheme.Spec
  let chosenIndex : Cone D := Scheme.Spec.mapCone (fgSubalgebraCoconeOf baseField extensionField).op
  have hc : IsLimit chosenIndex := isLimitOfPreserves Scheme.Spec (isColimitFGSubalgebraCocone baseField extensionField).op
  have hD {index secondIndex : stageIndexᵒᵖ} (structureMap : index ⟶ secondIndex) : IsAffineHom (D.map structureMap) :=
    inferInstanceAs (IsAffineHom (Spec.map _))
  let i₀ : stageIndexᵒᵖ := Opposite.op ⟨⊥, Subalgebra.fg_bot⟩
  let restriction : CommRingCat.of (⊥ : Subalgebra baseField extensionField) ≅ CommRingCat.of baseField :=
    (Algebra.botEquiv baseField extensionField).toRingEquiv.toCommRingCatIso
  let prime : scheme ⟶ D.obj i₀ := function ≫ Spec.map restriction.hom
  have hring : (CommRingCat.ofHom (⊥ : Subalgebra baseField extensionField).val.toRingHom :
      CommRingCat.of (⊥ : Subalgebra baseField extensionField) ⟶ .of extensionField) =
        restriction.hom ≫ CommRingCat.ofHom (algebraMap baseField extensionField) := by
    ext point
    obtain ⟨element, rfl⟩ := (Algebra.botEquiv baseField extensionField).symm.surjective point
    simp [restriction]
  have hρK : chosenIndex.π.app i₀ = Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)) ≫ Spec.map restriction.hom := by
    rw [← Spec.map_comp, ← hring]
    rfl

  have H1 : IsPullback (pullback.fst function (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))
      (pullback.snd _ _) prime (chosenIndex.π.app i₀) := by
    rw [hρK]
    exact (IsPullback.of_hasPullback _ _).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (asIso (Spec.map restriction.hom)) (by simp) (by simp) (by simp [prime]) (by simp)
  let eX := (IsPullback.of_hasPullback prime (chosenIndex.π.app i₀)).isoIsPullback _ _ H1
  let D' := baseChangeDiagram D prime
  let c' := baseChangeCone D chosenIndex prime
  have hc' : IsLimit c' := isLimitBaseChangeCone D chosenIndex prime hc
  have : IsNoetherianRing (⊥ : Subalgebra baseField extensionField) :=
    isNoetherianRing_of_ringEquiv baseField (Algebra.botEquiv baseField extensionField).symm.toRingEquiv
  have : IsLocallyNoetherian (D.obj i₀) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of (⊥ : Subalgebra baseField extensionField))))
  have : LocallyOfFinitePresentation (ℙ(homogeneousIndex; D.obj i₀) ↘ D.obj i₀) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType).mpr inferInstance
  let coordinate : c'.pt ⟶ ℙ(homogeneousIndex; D.obj i₀) := eX.hom ≫ projectiveMap ≫ ProjectiveSpace.map homogeneousIndex (chosenIndex.π.app i₀)
  have ha : c'.π ≫ baseChangeDiagramStructure D prime =
      (Functor.const _).map (coordinate ≫ ℙ(homogeneousIndex; D.obj i₀) ↘ D.obj i₀) := by
    ext secondIndex
    simp only [NatTrans.comp_app, baseChangeDiagramStructure_app, Functor.const_map_app, coordinate,
      Category.assoc, ProjectiveSpace.map_over, reassoc_of% hψo]
    rw [baseChangeCone_π_app_fst_assoc, pullback.condition, IsPullback.isoIsPullback_hom_snd_assoc]
  obtain ⟨secondIndex, structureMap, hg₁, hg₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D'
    (baseChangeDiagramStructure D prime) (ℙ(homogeneousIndex; D.obj i₀) ↘ D.obj i₀) c' hc' coordinate ha

  have hWaff (cc : homogeneousIndex) : IsAffineOpen
      (c'.π.app secondIndex ⁻¹ᵁ (structureMap ⁻¹ᵁ ProjectiveSpace.standardOpen homogeneousIndex (D.obj i₀) cc)) := by
    rw [← Scheme.Hom.comp_preimage, hg₁]
    simp only [coordinate, Scheme.Hom.comp_preimage, ProjectiveSpace.map_preimage_standardOpen]
    exact (hψ cc).preimage eX.hom
  have : IsAffine (D.obj i₀) := inferInstanceAs (IsAffine (Spec _))
  have : QuasiSeparatedSpace ℙ(homogeneousIndex; D.obj i₀) :=
    quasiSeparatedSpace_of_quasiSeparated (ℙ(homogeneousIndex; D.obj i₀) ↘ D.obj i₀)
  have hWc (cc : homogeneousIndex) :=
    QuasiCompact.isCompact_preimage (f := structureMap) _ (ProjectiveSpace.standardOpen homogeneousIndex _ cc).isOpen
      (ProjectiveSpace.isAffineOpen_standardOpen homogeneousIndex (D.obj i₀) cc).isCompact
  have hlater (cc : homogeneousIndex) := exists_isAffineOpen_preimage hc' (index := secondIndex) (hWc cc) (hWaff cc)
  choose j' hj' using hlater
  have hthin {coordinate otherCoordinate : Over i₀} (schemeUniverse homUniverse : coordinate ⟶ otherCoordinate) : schemeUniverse = homUniverse :=
    Over.OverMorphism.ext (Subsingleton.elim _ _)
  obtain ⟨indexType, hJ⟩ := IsCofiltered.inf_objs_exists
    (insert secondIndex (Finset.univ.image fun cc ↦ (j' cc).left))
  let hJj : indexType ⟶ secondIndex := (hJ (Finset.mem_insert_self _ _)).some
  have hJaff (cc : homogeneousIndex) : IsAffineOpen
      (D'.map hJj ⁻¹ᵁ (structureMap ⁻¹ᵁ ProjectiveSpace.standardOpen homogeneousIndex (D.obj i₀) cc)) := by
    let schemeUniverse : indexType ⟶ (j' cc).left := (hJ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_univ cc)))).some
    rw [hthin hJj (schemeUniverse ≫ (j' cc).hom), Functor.map_comp, Scheme.Hom.comp_preimage]
    exact (hj' cc).preimage _

  let baseRing : Subalgebra baseField extensionField := indexType.left.unop.1
  obtain ⟨otherExponent, hm⟩ := Ideal.exists_maximal baseRing
  let finiteExtension := baseRing ⧸ otherExponent
  let : Field finiteExtension := Ideal.Quotient.field otherExponent
  have : Algebra.FiniteType baseField baseRing := (Subalgebra.fg_iff_finiteType _).mp indexType.left.unop.2
  have : Algebra.FiniteType baseField finiteExtension :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ baseField otherExponent) (Ideal.Quotient.mkₐ_surjective baseField otherExponent)
  have : Module.Finite baseField finiteExtension := finite_of_finite_type_of_isJacobsonRing baseField finiteExtension
  let ringMap : CommRingCat.of baseRing ⟶ CommRingCat.of finiteExtension := CommRingCat.ofHom (Ideal.Quotient.mk otherExponent)
  have hbot : Spec.map ringMap ≫ D.map indexType.hom =
      Spec.map (CommRingCat.ofHom (algebraMap baseField finiteExtension)) ≫ Spec.map restriction.hom := by
    rw [← Spec.map_comp]
    change Spec.map ringMap ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
    ext point
    obtain ⟨element, rfl⟩ := (Algebra.botEquiv baseField extensionField).symm.surjective point
    simp only [restriction, ringMap, Functor.op_obj, Functor.op_map, fgSubalgebraDiagramOf_map,
      AlgHom.toRingHom_eq_coe, Quiver.Hom.unop_op, CommRingCat.hom_comp,
      ConcreteCategory.hom_ofHom, Algebra.botEquiv_symm_apply, RingHom.coe_comp,
      Function.comp_apply]
    erw [(Algebra.botEquiv baseField extensionField).commutes element]
    rfl
  let XJ := pullback prime (D.map indexType.hom)
  let source := pullback (pullback.snd prime (D.map indexType.hom)) (Spec.map ringMap)
  have hpaste := (IsPullback.of_hasPullback (pullback.snd prime (D.map indexType.hom)) (Spec.map ringMap)).paste_horiz
    (IsPullback.of_hasPullback prime (D.map indexType.hom))
  have HY : IsPullback (pullback.fst _ _ ≫ pullback.fst prime (D.map indexType.hom))
      (pullback.snd (pullback.snd prime (D.map indexType.hom)) (Spec.map ringMap)) function
      (Spec.map (CommRingCat.ofHom (algebraMap baseField finiteExtension))) := by
    rw [hbot] at hpaste
    exact hpaste.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (Spec.map restriction.hom)).symm
      (by simp) (by simp) (by simp [prime]) (by simp)

  let gJ : XJ ⟶ ℙ(homogeneousIndex; D.obj i₀) := D'.map hJj ≫ structureMap
  have hw : pullback.snd (pullback.snd prime (D.map indexType.hom)) (Spec.map ringMap) ≫ (Spec.map ringMap ≫ D.map indexType.hom) =
      (pullback.fst _ _ ≫ gJ) ≫ ℙ(homogeneousIndex; D.obj i₀) ↘ D.obj i₀ := by
    simp only [gJ, Category.assoc, hg₂, baseChangeDiagramStructure_app]
    rw [baseChangeDiagram_map_fst_assoc, ← pullback.condition_assoc, pullback.condition]
  refine ⟨finiteExtension, inferInstance, inferInstance, inferInstance, source, _, _, HY,
    ProjectiveSpace.liftBaseChange _ _ hw, fun cc ↦ ?_⟩
  rw [ProjectiveSpace.liftBaseChange_preimage_standardOpen, Scheme.Hom.comp_preimage]
  have : IsAffineHom (pullback.fst (pullback.snd prime (D.map indexType.hom)) (Spec.map ringMap)) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ (isAffineHom_of_isAffine (Spec.map ringMap))
  exact (hJaff cc).preimage _

end AlgebraicGeometry
