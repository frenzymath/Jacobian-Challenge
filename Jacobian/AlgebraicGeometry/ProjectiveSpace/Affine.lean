import Jacobian.AlgebraicGeometry.ProjectiveSpace.Charts
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Polynomial projective space over an affine base

Coefficient homomorphisms induce morphisms of polynomial projective spaces.
On a standard homogeneous chart these are the usual coefficient homomorphisms
of polynomial rings in the coordinate ratios. Over a spectrum, this identifies
the polynomial construction with relative projective space over the same base.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits MvPolynomial
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra Classical.decEq

variable (coordinates : Type u) {sourceRing targetRing : Type u}
  [CommRing sourceRing] [CommRing targetRing]

private def coefficientMap (coefficients : sourceRing →+* targetRing) :
    homogeneousSubmodule coordinates sourceRing →+*ᵍ
      homogeneousSubmodule coordinates targetRing where
  __ := MvPolynomial.map coefficients
  map_mem homogeneous := homogeneous.map coefficients

@[simp]
private lemma coefficientMap_apply (coefficients : sourceRing →+* targetRing)
    (polynomial : MvPolynomial coordinates sourceRing) :
    coefficientMap coordinates coefficients polynomial = MvPolynomial.map coefficients polynomial :=
  rfl

private lemma map_irrelevant_coefficientMap (coefficients : sourceRing →+* targetRing) :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule coordinates sourceRing)).toIdeal.map
        (coefficientMap coordinates coefficients).toRingHom =
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule coordinates targetRing)).toIdeal := by
  rw [toIdeal_irrelevant_homogeneousSubmodule, toIdeal_irrelevant_homogeneousSubmodule,
    Ideal.map_span, ← Set.range_comp]
  congr 1
  ext coordinate
  simp [Function.comp_def]

private def coefficientAwayMap (coefficients : sourceRing →+* targetRing)
    (coordinate : coordinates) :
    HomogeneousLocalization.Away (homogeneousSubmodule coordinates sourceRing) (X coordinate) →+*
      HomogeneousLocalization.Away (homogeneousSubmodule coordinates targetRing) (X coordinate) :=
  HomogeneousLocalization.map (coefficientMap coordinates coefficients) (by
    rintro _ ⟨exponent, rfl⟩
    exact ⟨exponent, by simp⟩)

private lemma coefficientAwayMap_algebraMap (coefficients : sourceRing →+* targetRing)
    (coordinate : coordinates) (coefficient : sourceRing) :
    coefficientAwayMap coordinates coefficients coordinate (algebraMap sourceRing _ coefficient) =
      algebraMap targetRing _ (coefficients coefficient) := by
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.map (coefficientMap coordinates coefficients) _
    (HomogeneousLocalization.fromZeroRingHom _ _
      (algebraMap sourceRing (homogeneousSubmodule coordinates sourceRing 0) coefficient))).val = _
  simp [HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_algebraMap,
    SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]
  exact congrArg (Localization.mk (C (coefficients coefficient))) (Subtype.ext rfl)

private lemma coefficientAwayMap_chartEquiv (coefficients : sourceRing →+* targetRing)
    (coordinate : coordinates) :
    (coefficientAwayMap coordinates coefficients coordinate).comp
        (homogeneousLocalizationAwayXEquiv sourceRing coordinate).symm.toRingHom =
      (homogeneousLocalizationAwayXEquiv targetRing coordinate).symm.toRingHom.comp
        (MvPolynomial.map coefficients) := by
  apply MvPolynomial.ringHom_ext
  · intro coefficient
    change coefficientAwayMap coordinates coefficients coordinate
        ((homogeneousLocalizationAwayXEquiv sourceRing coordinate).symm (C coefficient)) =
      (homogeneousLocalizationAwayXEquiv targetRing coordinate).symm
        (MvPolynomial.map coefficients (C coefficient))
    rw [MvPolynomial.map_C]
    change coefficientAwayMap coordinates coefficients coordinate
        ((homogeneousLocalizationAwayXEquiv sourceRing coordinate).symm
          (algebraMap sourceRing _ coefficient)) =
      (homogeneousLocalizationAwayXEquiv targetRing coordinate).symm
        (algebraMap targetRing _ (coefficients coefficient))
    rw [AlgEquiv.commutes, AlgEquiv.commutes]
    exact coefficientAwayMap_algebraMap coordinates coefficients coordinate coefficient
  · intro index
    change coefficientAwayMap coordinates coefficients coordinate
        ((homogeneousLocalizationAwayXEquiv sourceRing coordinate).symm (X index)) =
      (homogeneousLocalizationAwayXEquiv targetRing coordinate).symm
        (MvPolynomial.map coefficients (X index))
    rw [MvPolynomial.map_X, homogeneousLocalizationAwayXEquiv_symm_X,
      homogeneousLocalizationAwayXEquiv_symm_X]
    apply HomogeneousLocalization.val_injective
    simp [coefficientAwayMap, HomogeneousLocalization.Away.mk,
      HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]

/-- The morphism of polynomial projective spaces induced by a coefficient homomorphism. -/
def projectiveSpaceMap (coefficients : sourceRing →+* targetRing) :
    projectiveSpaceOverAffine coordinates targetRing ⟶
      projectiveSpaceOverAffine coordinates sourceRing :=
  Proj.map (coefficientMap coordinates coefficients)
    (map_irrelevant_coefficientMap coordinates coefficients).ge

/-- A coefficient homomorphism preserves each homogeneous coordinate chart. -/
@[simp]
lemma projectiveSpaceMap_preimage_basicOpen_X (coefficients : sourceRing →+* targetRing)
    (coordinate : coordinates) :
    projectiveSpaceMap coordinates coefficients ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule coordinates sourceRing) (X coordinate) =
      Proj.basicOpen (homogeneousSubmodule coordinates targetRing) (X coordinate) := by
  simp [projectiveSpaceMap]

variable (baseRing : Type u) [CommRing baseRing]

/-- The standard chart of polynomial projective space is the spectrum of its
polynomial ring in coordinate ratios. -/
def standardOpenIso (coordinate : coordinates) :
    (Proj.basicOpen (homogeneousSubmodule coordinates baseRing) (X coordinate)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial {index : coordinates // index ≠ coordinate} baseRing)) :=
  Proj.basicOpenIsoSpec _ _ (X_mem_homogeneousSubmodule_one baseRing coordinate) one_pos ≪≫
    Scheme.Spec.mapIso
      (homogeneousLocalizationAwayXEquiv baseRing coordinate).symm.toRingEquiv.toCommRingCatIso.op

/-- The inverse chart map is the homogeneous localization chart followed by
the coordinate-ratio isomorphism. -/
@[reassoc]
lemma standardOpenIso_inv_ι (coordinate : coordinates) :
    (standardOpenIso coordinates baseRing coordinate).inv ≫
        (Proj.basicOpen (homogeneousSubmodule coordinates baseRing) (X coordinate)).ι =
      Spec.map (CommRingCat.ofHom
        (homogeneousLocalizationAwayXEquiv baseRing coordinate).toRingHom) ≫
        Proj.awayι (homogeneousSubmodule coordinates baseRing) (X coordinate)
          (X_mem_homogeneousSubmodule_one baseRing coordinate) one_pos :=
  rfl

/-- The standard polynomial chart has its usual structure morphism over the
coefficient ring. -/
@[reassoc (attr := simp)]
lemma standardOpenIso_inv_over (coordinate : coordinates) :
    (standardOpenIso coordinates baseRing coordinate).inv ≫
        (Proj.basicOpen (homogeneousSubmodule coordinates baseRing) (X coordinate)).ι ≫
          projectiveSpaceOverAffineToSpec coordinates baseRing =
      Spec.map (CommRingCat.ofHom
        (C : baseRing →+* MvPolynomial {index : coordinates // index ≠ coordinate} baseRing)) := by
  rw [standardOpenIso_inv_ι_assoc, projectiveSpaceOverAffineToSpec,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro coefficient
  change homogeneousLocalizationAwayXEquiv baseRing coordinate
    (algebraMap baseRing _ coefficient) = C coefficient
  exact homogeneousLocalizationAwayXEquiv_algebraMap baseRing coordinate coefficient

/-- On a standard homogeneous chart, a coefficient map is the corresponding
coefficient map of polynomial rings in the coordinate ratios. -/
@[reassoc]
lemma standardOpenIso_inv_ι_projectiveSpaceMap (coefficients : sourceRing →+* targetRing)
    (coordinate : coordinates) :
    (standardOpenIso coordinates targetRing coordinate).inv ≫
        (Proj.basicOpen (homogeneousSubmodule coordinates targetRing) (X coordinate)).ι ≫
          projectiveSpaceMap coordinates coefficients =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.map coefficients :
          MvPolynomial {index : coordinates // index ≠ coordinate} sourceRing →+*
            MvPolynomial {index : coordinates // index ≠ coordinate} targetRing)) ≫
        (standardOpenIso coordinates sourceRing coordinate).inv ≫
          (Proj.basicOpen (homogeneousSubmodule coordinates sourceRing) (X coordinate)).ι := by
  have chartMap :
      Proj.awayι (homogeneousSubmodule coordinates targetRing) (X coordinate)
          (X_mem_homogeneousSubmodule_one targetRing coordinate) one_pos ≫
            projectiveSpaceMap coordinates coefficients =
        Spec.map (CommRingCat.ofHom (coefficientAwayMap coordinates coefficients coordinate)) ≫
          Proj.awayι (homogeneousSubmodule coordinates sourceRing) (X coordinate)
            (X_mem_homogeneousSubmodule_one sourceRing coordinate) one_pos := by
    have transport (image : MvPolynomial coordinates targetRing)
        (imageEq : coefficientMap coordinates coefficients (X coordinate) = image)
        (homogeneous : image ∈ homogeneousSubmodule coordinates targetRing 1)
        (mapPowers : Submonoid.powers (X coordinate : MvPolynomial coordinates sourceRing) ≤
          (Submonoid.powers image).comap (coefficientMap coordinates coefficients)) :
        Proj.awayι (homogeneousSubmodule coordinates targetRing) image homogeneous one_pos ≫
            projectiveSpaceMap coordinates coefficients =
          Spec.map (CommRingCat.ofHom
            (HomogeneousLocalization.map (coefficientMap coordinates coefficients) mapPowers)) ≫
            Proj.awayι (homogeneousSubmodule coordinates sourceRing) (X coordinate)
              (X_mem_homogeneousSubmodule_one sourceRing coordinate) one_pos := by
      subst image
      exact Proj.awayι_comp_map (coefficientMap coordinates coefficients)
        (map_irrelevant_coefficientMap coordinates coefficients).ge one_pos (X coordinate)
        (X_mem_homogeneousSubmodule_one sourceRing coordinate)
    exact transport (X coordinate) (by simp)
      (X_mem_homogeneousSubmodule_one targetRing coordinate) (by
        rintro _ ⟨exponent, rfl⟩
        exact ⟨exponent, by simp⟩)
  rw [standardOpenIso_inv_ι_assoc, standardOpenIso_inv_ι,
    chartMap, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  change (homogeneousLocalizationAwayXEquiv targetRing coordinate).toRingHom.comp
      (coefficientAwayMap coordinates coefficients coordinate) =
    (MvPolynomial.map coefficients).comp
      (homogeneousLocalizationAwayXEquiv sourceRing coordinate).toRingHom
  apply RingHom.ext
  intro fraction
  obtain ⟨polynomial, rfl⟩ :=
    (homogeneousLocalizationAwayXEquiv sourceRing coordinate).symm.surjective fraction
  have comparison := congrArg (fun morphism ↦ morphism polynomial)
    (coefficientAwayMap_chartEquiv coordinates coefficients coordinate)
  change coefficientAwayMap coordinates coefficients coordinate
      ((homogeneousLocalizationAwayXEquiv sourceRing coordinate).symm polynomial) =
    (homogeneousLocalizationAwayXEquiv targetRing coordinate).symm
      (MvPolynomial.map coefficients polynomial) at comparison
  change homogeneousLocalizationAwayXEquiv targetRing coordinate
      (coefficientAwayMap coordinates coefficients coordinate
        ((homogeneousLocalizationAwayXEquiv sourceRing coordinate).symm polynomial)) =
    MvPolynomial.map coefficients (homogeneousLocalizationAwayXEquiv sourceRing coordinate
      ((homogeneousLocalizationAwayXEquiv sourceRing coordinate).symm polynomial))
  rw [comparison, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (coordinates : Type u) (baseRing : CommRingCat.{u})

private def integerCoefficients : ULift.{u} ℤ →+* baseRing :=
  (Int.castRingHom baseRing).comp (ULift.ringEquiv (R := ℤ)).toRingHom

@[reassoc]
private lemma specIso_inv_toSpecMvPoly (affineCoordinates : Type u) :
    (AffineSpace.SpecIso affineCoordinates baseRing).inv ≫
        AffineSpace.toSpecMvPoly affineCoordinates (Spec baseRing) =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.map (integerCoefficients baseRing) :
          MvPolynomial affineCoordinates (ULift.{u} ℤ) →+*
            MvPolynomial affineCoordinates baseRing)) := by
  apply (AffineSpace.toSpecMvPolyIntEquiv affineCoordinates).injective
  ext coordinate
  rw [AffineSpace.toSpecMvPolyIntEquiv_comp, ← AffineSpace.coord,
    AffineSpace.SpecIso_inv_appTop_coord]
  simpa only [Category.id_comp, Scheme.Hom.id_app, CommRingCat.id_apply,
    CommRingCat.hom_ofHom, MvPolynomial.map_X] using
    (AffineSpace.toSpecMvPolyIntEquiv_comp_SpecMap
      (𝟙 (Spec (CommRingCat.of (MvPolynomial affineCoordinates baseRing))))
      (CommRingCat.ofHom (MvPolynomial.map (integerCoefficients baseRing))) coordinate).symm

/-- The canonical morphism from polynomial projective space to relative
projective space over the spectrum of its coefficient ring. -/
def fromProj : Proj.projectiveSpaceOverAffine coordinates baseRing ⟶ ℙ(coordinates; Spec baseRing) :=
  pullback.lift (Proj.projectiveSpaceOverAffineToSpec coordinates baseRing)
    (Proj.projectiveSpaceMap coordinates (integerCoefficients baseRing))
    (terminal.hom_ext _ _)

/-- The canonical comparison is a morphism over the affine base. -/
@[reassoc (attr := simp)]
lemma fromProj_over :
    fromProj coordinates baseRing ≫ ℙ(coordinates; Spec baseRing) ↘ Spec baseRing =
      Proj.projectiveSpaceOverAffineToSpec coordinates baseRing :=
  pullback.lift_fst _ _ _

/-- The canonical comparison induces the coefficient map to the integral model. -/
@[reassoc (attr := simp)]
lemma fromProj_toIntegralModel :
    fromProj coordinates baseRing ≫ toIntegralModel coordinates (Spec baseRing) =
      Proj.projectiveSpaceMap coordinates (integerCoefficients baseRing) :=
  pullback.lift_snd _ _ _

/-- Standard opens agree under the affine-base comparison. -/
@[simp]
lemma fromProj_preimage_standardOpen (coordinate : coordinates) :
    fromProj coordinates baseRing ⁻¹ᵁ standardOpen coordinates (Spec baseRing) coordinate =
      Proj.basicOpen (homogeneousSubmodule coordinates baseRing) (X coordinate) := by
  change fromProj coordinates baseRing ⁻¹ᵁ
      (toIntegralModel coordinates (Spec baseRing) ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ)) (X coordinate)) = _
  rw [← Scheme.Hom.comp_preimage, fromProj_toIntegralModel,
    Proj.projectiveSpaceMap_preimage_basicOpen_X]

private lemma standardOpenIso_inv_toIntegralModel (coordinate : coordinates) :
    (standardOpenIso coordinates (Spec baseRing) coordinate).inv ≫
        (standardOpen coordinates (Spec baseRing) coordinate).ι ≫
          toIntegralModel coordinates (Spec baseRing) =
      AffineSpace.toSpecMvPoly {index : coordinates // index ≠ coordinate} (Spec baseRing) ≫
        (integralStandardOpenIso coordinates coordinate).inv ≫
          (Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ)) (X coordinate)).ι := by
  apply (cancel_epi (standardOpenIso coordinates (Spec baseRing) coordinate).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι] using
    (congrArg (fun morphism ↦ morphism ≫
        (integralStandardOpenIso coordinates coordinate).inv ≫
          (Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ)) (X coordinate)).ι)
      (standardOpenIso_hom_toSpecMvPoly coordinates (Spec baseRing) coordinate)).symm

/-- On a standard chart, the affine comparison is the identity on the base
and the coordinate ratios. -/
@[reassoc]
lemma standardOpenIso_inv_fromProj (coordinate : coordinates) :
    (Proj.standardOpenIso coordinates baseRing coordinate).inv ≫
        (Proj.basicOpen (homogeneousSubmodule coordinates baseRing) (X coordinate)).ι ≫
          fromProj coordinates baseRing =
      (AffineSpace.SpecIso {index : coordinates // index ≠ coordinate} baseRing).inv ≫
        (standardOpenIso coordinates (Spec baseRing) coordinate).inv ≫
          (standardOpen coordinates (Spec baseRing) coordinate).ι := by
  have integralChartEq : Proj.standardOpenIso coordinates (ULift.{u} ℤ) coordinate =
      integralStandardOpenIso coordinates coordinate := rfl
  apply ProjectiveSpace.hom_ext
  · simp only [Category.assoc, fromProj_over, Proj.standardOpenIso_inv_over,
      standardOpenIso_inv_ι_over, AffineSpace.SpecIso_inv_over]
  · simpa only [Category.assoc, fromProj_toIntegralModel,
      Proj.standardOpenIso_inv_ι_projectiveSpaceMap,
      standardOpenIso_inv_toIntegralModel, specIso_inv_toSpecMvPoly_assoc, integralChartEq]

/-- The polynomial construction and relative construction of projective space
over a spectrum agree. -/
instance isIso_fromProj : IsIso (fromProj coordinates baseRing) := by
  change (MorphismProperty.isomorphisms Scheme) (fromProj coordinates baseRing)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme)
    (standardOpen coordinates (Spec baseRing))
    (iSup_standardOpen coordinates (Spec baseRing)) ?_
  intro coordinate
  let sourceIso := (Proj.standardOpenIso coordinates baseRing coordinate).symm ≪≫
    (Proj.projectiveSpaceOverAffine coordinates baseRing).isoOfEq
      (fromProj_preimage_standardOpen coordinates baseRing coordinate).symm
  have chartComparison :
      sourceIso.hom ≫ (fromProj coordinates baseRing ∣_
          standardOpen coordinates (Spec baseRing) coordinate) =
        (AffineSpace.SpecIso {index : coordinates // index ≠ coordinate} baseRing).inv ≫
          (standardOpenIso coordinates (Spec baseRing) coordinate).inv := by
    apply (cancel_mono (standardOpen coordinates (Spec baseRing) coordinate).ι).mp
    simpa only [sourceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc] using
      standardOpenIso_inv_fromProj coordinates baseRing coordinate
  haveI : IsIso (sourceIso.hom ≫ (fromProj coordinates baseRing ∣_
      standardOpen coordinates (Spec baseRing) coordinate)) := by
    rw [chartComparison]
    infer_instance
  exact IsIso.of_isIso_comp_left sourceIso.hom _

/-- Relative projective space over an affine scheme is polynomial projective space. -/
def affineIso : ℙ(coordinates; Spec baseRing) ≅ Proj.projectiveSpaceOverAffine coordinates baseRing :=
  (asIso (fromProj coordinates baseRing)).symm

/-- The affine comparison respects the structure morphisms to the coefficient spectrum. -/
@[reassoc (attr := simp)]
lemma affineIso_hom_over :
    (affineIso coordinates baseRing).hom ≫
        Proj.projectiveSpaceOverAffineToSpec coordinates baseRing =
      ℙ(coordinates; Spec baseRing) ↘ Spec baseRing := by
  rw [← fromProj_over]
  change (asIso (fromProj coordinates baseRing)).inv ≫
    (asIso (fromProj coordinates baseRing)).hom ≫
      (ℙ(coordinates; Spec baseRing) ↘ Spec baseRing) = _
  exact (asIso (fromProj coordinates baseRing)).inv_hom_id_assoc _

end AlgebraicGeometry.ProjectiveSpace
