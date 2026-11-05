import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.GlobalSections

/-!
# Sections in affine charts of projective spectra

The homogeneous localization map is inverse to restriction along its affine chart.
-/

set_option backward.isDefEq.respectTransparency false

universe gradedUniverse

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {gradedPieces gradedRing : Type gradedUniverse} [CommRing gradedRing]
  [SetLike gradedPieces gradedRing] [AddSubgroupClass gradedPieces gradedRing]
  (grading : ℕ → gradedPieces) [GradedRing grading]

lemma awayToSection_awayι_appLE {homogeneousElement : gradedRing} {degree : ℕ} (homogeneous : homogeneousElement ∈ grading degree) (positive : 0 < degree) :
    awayToSection grading homogeneousElement ≫ (awayι grading homogeneousElement homogeneous positive).appLE (basicOpen grading homogeneousElement) ⊤
      (by rw [← opensRange_awayι grading homogeneousElement homogeneous positive]; exact (Scheme.Hom.preimage_opensRange _).ge) =
      (Scheme.ΓSpecIso _).inv := by
  have key : (basicOpenIsoSpec grading homogeneousElement homogeneous positive).hom.app ⊤ = (Scheme.ΓSpecIso _).hom ≫
      awayToSection grading homogeneousElement ≫ (basicOpen grading homogeneousElement).topIso.inv := by
    rw [basicOpenIsoSpec_hom]
    exact basicOpenToSpec_app_top grading homogeneousElement
  have hι : (basicOpenIsoSpec grading homogeneousElement homogeneous positive).hom ≫ awayι grading homogeneousElement homogeneous positive = (basicOpen grading homogeneousElement).ι := by
    rw [← basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have hcongr : ∀ {firstMap secondMap : (basicOpen grading homogeneousElement).toScheme ⟶ Proj grading} (equality : firstMap = secondMap) (opens) (inclusion),
      firstMap.appLE (basicOpen grading homogeneousElement) opens inclusion = secondMap.appLE (basicOpen grading homogeneousElement) opens (equality ▸ inclusion) := by
    rintro firstMap secondMap rfl opens inclusion
    rfl
  rw [← cancel_mono ((basicOpenIsoSpec grading homogeneousElement homogeneous positive).hom.appTop), Category.assoc,
    Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, hcongr hι,
    ← Scheme.Hom.app_eq_appLE, key, Iso.inv_hom_id_assoc]
  congr 1

end AlgebraicGeometry.Proj
