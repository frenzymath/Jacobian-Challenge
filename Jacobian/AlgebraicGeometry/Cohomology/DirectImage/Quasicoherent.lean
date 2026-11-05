import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.MayerVietoris

/-!
# Quasi-coherence of higher direct images

The higher direct images of a quasi-coherent module under a quasi-compact
quasi-separated morphism are quasi-coherent. Restriction to affine opens
of the base reduces the assertion to finite affine Mayer–Vietoris covers.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules
variable {X T : Scheme.{u}} (f : X ⟶ T) (ℱ : X.Modules)
  [QuasiCompact f] [QuasiSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

/-- Higher direct images of quasi-coherent coefficients are quasi-coherent
under a quasi-compact quasi-separated morphism. -/
theorem isQuasicoherent_higherDirectImage (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsQuasicoherent := by
  refine isQuasicoherent_of_iSup_opensRange_eq_top _
    (fun U : T.affineOpens ↦ U.2.fromSpec)
    (by simpa only [IsAffineOpen.opensRange_fromSpec] using iSup_affineOpens_eq_top T)
    fun U ↦ ?_
  let g := U.2.fromSpec
  have : IsIso (((higherDirectImage f q).obj ℱ).restrict g).fromTildeΓ := by
    have := isGrothendieckAbelian (Limits.pullback f g)
    obtain ⟨n, hn⟩ := exists_higherDirectImageBound_top (pullback.snd f g)
      ((Modules.pullback (pullback.fst f g)).obj ℱ)
    have : SheafOfModules.IsQuasicoherent (R := (Spec Γ(T, U.1)).ringCatSheaf)
        (((higherDirectImage f q).obj ℱ).restrict g) :=
      (SheafOfModules.isQuasicoherent (Spec Γ(T, U.1)).ringCatSheaf).prop_of_iso
        (higherDirectImagePullbackIsoRestrict (IsPullback.of_hasPullback f g) ℱ q)
        (hn.higherDirectImage.1 q)
    exact isIso_fromTildeΓ_of_isQuasicoherent _
  exact presentationOfIsIsoFromTildeΓ _


end AlgebraicGeometry.Scheme.Modules
