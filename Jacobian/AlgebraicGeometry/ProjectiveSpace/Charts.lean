import Jacobian.AlgebraicGeometry.AffineSpace.Immersion
import Jacobian.AlgebraicGeometry.ProjectiveSpace.OfSections
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.GlobalSections

/-!
# Standard affine charts of projective space

Each standard open is affine space over the base. A morphism given by
generating functions restricts in this chart to the quotients of its coordinates.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra Classical.decEq

variable (coordinates : Type u) (baseScheme : Scheme.{u}) (coordinate : coordinates)

def integralStandardOpenIso :
    (Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ)) (MvPolynomial.X coordinate)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial {otherCoordinate : coordinates // otherCoordinate ≠ coordinate} (ULift.{u} ℤ))) :=
  Proj.basicOpenIsoSpec _ _ (X_mem_homogeneousSubmodule_one _ coordinate) one_pos ≪≫
    Scheme.Spec.mapIso
      (homogeneousLocalizationAwayXEquiv (ULift.{u} ℤ) coordinate).symm.toRingEquiv.toCommRingCatIso.op

@[simp]
lemma integralStandardOpenIso_hom :
    (integralStandardOpenIso coordinates coordinate).hom =
      (Proj.basicOpenIsoSpec _ _ (X_mem_homogeneousSubmodule_one _ coordinate) one_pos).hom ≫
        Spec.map (CommRingCat.ofHom
          (homogeneousLocalizationAwayXEquiv (ULift.{u} ℤ) coordinate).symm.toRingHom) :=
  rfl

lemma isPullback_standardOpen :
    IsPullback ((toIntegralModel coordinates baseScheme).resLE _ (standardOpen coordinates baseScheme coordinate) le_rfl)
      ((standardOpen coordinates baseScheme coordinate).ι ≫ ℙ(coordinates; baseScheme) ↘ baseScheme)
      (terminal.from _) (terminal.from baseScheme) := by
  have square := (isPullback_morphismRestrict (toIntegralModel coordinates baseScheme)
    (Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ)) (MvPolynomial.X coordinate))).paste_vert
      (isPullback_over_toIntegralModel coordinates baseScheme).flip
  have restrictionEq : (toIntegralModel coordinates baseScheme).resLE
      (Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ)) (MvPolynomial.X coordinate))
        (standardOpen coordinates baseScheme coordinate) le_rfl =
      toIntegralModel coordinates baseScheme ∣_ Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ)) (MvPolynomial.X coordinate) :=
    Scheme.Hom.resLE_eq_morphismRestrict ..
  exact square.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by rw [Iso.refl_hom, Category.comp_id]; exact restrictionEq.symm.trans (Category.id_comp _).symm)
    (by rw [Iso.refl_hom, Category.comp_id]; exact (Category.id_comp _).symm)
    (terminal.hom_ext _ _) (terminal.hom_ext _ _)

lemma isPullback_standardOpen_integralStandardOpenIso :
    IsPullback ((toIntegralModel coordinates baseScheme).resLE _ (standardOpen coordinates baseScheme coordinate) le_rfl ≫
        (integralStandardOpenIso coordinates coordinate).hom)
      ((standardOpen coordinates baseScheme coordinate).ι ≫ ℙ(coordinates; baseScheme) ↘ baseScheme)
      (terminal.from (Spec (CommRingCat.of (MvPolynomial {otherCoordinate : coordinates // otherCoordinate ≠ coordinate} (ULift.{u} ℤ)))))
      (terminal.from baseScheme) :=
  (isPullback_standardOpen coordinates baseScheme coordinate).of_iso (Iso.refl _) (integralStandardOpenIso coordinates coordinate) (Iso.refl _)
    (Iso.refl _) (by simp) (by simp) (terminal.hom_ext _ _) (terminal.hom_ext _ _)

lemma isPullback_toSpecMvPoly (affineCoordinates : Type u) :
    IsPullback (AffineSpace.toSpecMvPoly affineCoordinates baseScheme) (𝔸(affineCoordinates; baseScheme) ↘ baseScheme)
      (terminal.from (Spec (CommRingCat.of (MvPolynomial affineCoordinates (ULift.{u} ℤ))))) (terminal.from baseScheme) :=
  (IsPullback.of_hasPullback _ _).flip

def standardOpenIso : (standardOpen coordinates baseScheme coordinate).toScheme ≅ 𝔸({otherCoordinate : coordinates // otherCoordinate ≠ coordinate}; baseScheme) :=
  (isPullback_standardOpen_integralStandardOpenIso coordinates baseScheme coordinate).isoIsPullback _ _
    (isPullback_toSpecMvPoly baseScheme _)

@[reassoc (attr := simp)]
lemma standardOpenIso_hom_over :
    (standardOpenIso coordinates baseScheme coordinate).hom ≫ 𝔸({otherCoordinate : coordinates // otherCoordinate ≠ coordinate}; baseScheme) ↘ baseScheme =
      (standardOpen coordinates baseScheme coordinate).ι ≫ ℙ(coordinates; baseScheme) ↘ baseScheme :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

@[reassoc (attr := simp)]
lemma standardOpenIso_inv_ι_over :
    (standardOpenIso coordinates baseScheme coordinate).inv ≫ (standardOpen coordinates baseScheme coordinate).ι ≫ ℙ(coordinates; baseScheme) ↘ baseScheme =
      𝔸({otherCoordinate : coordinates // otherCoordinate ≠ coordinate}; baseScheme) ↘ baseScheme :=
  IsPullback.isoIsPullback_inv_snd _ _ _ _

@[reassoc (attr := simp)]
lemma standardOpenIso_hom_toSpecMvPoly :
    (standardOpenIso coordinates baseScheme coordinate).hom ≫ AffineSpace.toSpecMvPoly {otherCoordinate : coordinates // otherCoordinate ≠ coordinate} baseScheme =
      (toIntegralModel coordinates baseScheme).resLE _ (standardOpen coordinates baseScheme coordinate) le_rfl ≫ (integralStandardOpenIso coordinates coordinate).hom :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

lemma isAffineOpen_standardOpen [IsAffine baseScheme] : IsAffineOpen (standardOpen coordinates baseScheme coordinate) :=
  have : IsAffine (standardOpen coordinates baseScheme coordinate).toScheme := .of_isIso (standardOpenIso coordinates baseScheme coordinate).hom
  this

section Sections

variable {sourceScheme : Scheme.{u}} (structureMap : sourceScheme ⟶ baseScheme) (sections : coordinates → Γ(sourceScheme, ⊤)) (generates : Ideal.span (Set.range sections) = ⊤)

variable {coordinates baseScheme} in

lemma powers_X_le_comap_powers (coordinate : coordinates) :
    Submonoid.powers (MvPolynomial.X coordinate : MvPolynomial coordinates (ULift.{u} ℤ)) ≤
      Submonoid.comap (evalSections sections) (Submonoid.powers (sections coordinate)) := by
  rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]
  simp

variable {coordinates baseScheme} in

def evalSectionsAway (coordinate : coordinates) :
    CommRingCat.of (MvPolynomial {otherCoordinate : coordinates // otherCoordinate ≠ coordinate} (ULift.{u} ℤ)) ⟶
      CommRingCat.of (Localization.Away (sections coordinate)) :=
  CommRingCat.ofHom (homogeneousLocalizationAwayXEquiv (ULift.{u} ℤ) coordinate).symm.toRingHom ≫
    CommRingCat.ofHom
      ((IsLocalization.map _ (evalSections sections) (powers_X_le_comap_powers sections coordinate)).comp
        (algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule coordinates (ULift.{u} ℤ))
          (MvPolynomial.X coordinate))
          (Localization.Away (MvPolynomial.X coordinate : MvPolynomial coordinates (ULift.{u} ℤ)))))

variable {coordinates baseScheme} in
@[simp]
lemma evalSectionsAway_X (coordinate : coordinates) (otherCoordinate : {otherCoordinate : coordinates // otherCoordinate ≠ coordinate}) :
    evalSectionsAway sections coordinate (MvPolynomial.X otherCoordinate) =
      IsLocalization.mk' (Localization.Away (sections coordinate)) (sections otherCoordinate.1)
        (⟨sections coordinate, Submonoid.mem_powers _⟩ : Submonoid.powers (sections coordinate)) := by
  rw [evalSectionsAway, CommRingCat.comp_apply]
  change ((IsLocalization.map (Localization.Away (sections coordinate)) (evalSections sections)
      (powers_X_le_comap_powers sections coordinate)).comp (algebraMap _ _))
      ((homogeneousLocalizationAwayXEquiv (ULift.{u} ℤ) coordinate).symm (MvPolynomial.X otherCoordinate)) = _
  rw [homogeneousLocalizationAwayXEquiv_symm_X, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk']
  congr 1
  · exact evalSections_X sections otherCoordinate.1
  · exact Subtype.ext (by simp)

set_option backward.isDefEq.respectTransparency.types false in
variable {coordinates baseScheme} in

lemma homOfSections_resLE_standardOpenIso_hom_toSpecMvPoly (coordinate : coordinates) :
    ((homOfSections structureMap sections generates).resLE (standardOpen coordinates baseScheme coordinate) (sourceScheme.basicOpen (sections coordinate))
        (homOfSections_preimage_standardOpen structureMap sections generates coordinate).ge ≫ (standardOpenIso coordinates baseScheme coordinate).hom) ≫
      AffineSpace.toSpecMvPoly {otherCoordinate : coordinates // otherCoordinate ≠ coordinate} baseScheme =
      sourceScheme.toSpecAway (sections coordinate) ≫ Spec.map (evalSectionsAway sections coordinate) := by
  rw [evalSectionsAway, Spec.map_comp, Category.assoc, standardOpenIso_hom_toSpecMvPoly,
    reassoc_of% homOfSections_resLE_comp_toIntegralModel_resLE structureMap sections generates coordinate, integralStandardOpenIso_hom]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun morphism ↦ morphism ≫ Spec.map (CommRingCat.ofHom
        (homogeneousLocalizationAwayXEquiv (ULift.{u} ℤ) coordinate).symm.toRingHom))
      ((Proj.toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom
          (homogeneousSubmodule coordinates (ULift.{u} ℤ)) (evalSections sections) (evalSections_X sections coordinate)
          Nat.one_pos (X_mem_homogeneousSubmodule_one _ coordinate)
          (powers_X_le_comap_powers sections coordinate)).trans
        (Category.assoc _ _ _).symm)).trans (Category.assoc _ _ _))

variable {coordinates baseScheme} in

theorem homOfSections_resLE_standardOpenIso_hom (coordinate : coordinates) :
    (homOfSections structureMap sections generates).resLE (standardOpen coordinates baseScheme coordinate) (sourceScheme.basicOpen (sections coordinate))
        (homOfSections_preimage_standardOpen structureMap sections generates coordinate).ge ≫ (standardOpenIso coordinates baseScheme coordinate).hom =
      AffineSpace.homOfVector ((sourceScheme.basicOpen (sections coordinate)).ι ≫ structureMap)
        (fun otherCoordinate ↦ sourceScheme.divBasicOpen (sections otherCoordinate.1) (sections coordinate)) := by
  refine AffineSpace.hom_ext ?_ fun otherCoordinate ↦ ?_
  · rw [Category.assoc, standardOpenIso_hom_over, homOfSections_resLE_ι_over,
      AffineSpace.homOfVector_over]
  · rw [AffineSpace.homOfVector_appTop_coord,
      show AffineSpace.coord baseScheme otherCoordinate =
        AffineSpace.toSpecMvPolyIntEquiv _ (AffineSpace.toSpecMvPoly _ baseScheme) otherCoordinate from rfl,
      ← AffineSpace.toSpecMvPolyIntEquiv_comp,
      homOfSections_resLE_standardOpenIso_hom_toSpecMvPoly structureMap sections generates coordinate,
      AffineSpace.toSpecMvPolyIntEquiv_comp_SpecMap, ← Scheme.awayToBasicOpen_apply,
      evalSectionsAway_X, Scheme.awayToBasicOpen_mk']

end Sections

end AlgebraicGeometry.ProjectiveSpace
