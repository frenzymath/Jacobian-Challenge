import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Quasicoherent
import Jacobian.AlgebraicGeometry.Modules.Vanishing

/-!
# Cohomological bounds for higher direct images

A finite affine cover bounds the nonzero higher direct images locally on the
base. For a quasi-compact base, finitely many such bounds give a global bound.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
variable {X T : Scheme.{u}} (f : X ⟶ T) (ℱ : X.Modules)
variable [QuasiCompact f] [IsSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

/-- Higher direct images vanish above a bound on a neighbourhood of every base point. -/
theorem exists_isZero_higherDirectImage_restrict (t : T) :
    ∃ (U : T.Opens) (d : ℕ), t ∈ U ∧
      ∀ q ≥ d, IsZero (((higherDirectImage f q).obj ℱ).restrict U.ι) := by
  obtain ⟨U, hU, htU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens) (show t ∈ ⊤ from trivial)
  have : IsAffine U := hU
  have := isGrothendieckAbelian (Limits.pullback f (Scheme.Opens.ι U))
  obtain ⟨n, hn⟩ := exists_higherDirectImageBound_top (pullback.snd f (Scheme.Opens.ι U))
    ((Modules.pullback (pullback.fst f (Scheme.Opens.ι U))).obj ℱ)
  exact ⟨U, n, htU, fun q hq ↦ IsZero.of_iso (hn.higherDirectImage.2 q hq)
    (higherDirectImagePullbackIsoRestrict (IsPullback.of_hasPullback f (Scheme.Opens.ι U)) ℱ
      q).symm⟩

/-- Over a quasi-compact base, a single bound suffices for all higher direct images. -/
theorem exists_isZero_higherDirectImage [CompactSpace T] :
    ∃ N, ∀ q ≥ N, IsZero ((higherDirectImage f q).obj ℱ) := by
  classical
  choose U d hU hd using exists_isZero_higherDirectImage_restrict f ℱ
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun t ↦ (U t : Set T))
    (fun t ↦ (U t).isOpen) (fun t _ ↦ Set.mem_iUnion.2 ⟨t, hU t⟩)
  refine ⟨s.sup d, fun q hq ↦ isZero_of_forall_exists_isZero_restrict _ fun t ↦ ?_⟩
  obtain ⟨t', ht', htt'⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ t))
  exact ⟨U t', htt', hd t' q ((Finset.le_sup ht').trans hq)⟩

end AlgebraicGeometry.Scheme.Modules
