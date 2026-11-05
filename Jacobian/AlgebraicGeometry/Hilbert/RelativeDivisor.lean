import Jacobian.AlgebraicGeometry.Hilbert.UniversalFamily
import Jacobian.AlgebraicGeometry.IdealSheaf.RelativeCartierPullback

/-!
# Universal divisors on relative curves

A finite flat closed family on a smooth relative curve is an effective Cartier
divisor. The dual ideal of the universal divisor pulls back to the divisor line
bundle of every classified family.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- Finite flat families on a smooth relative curve have invertible ideals. -/
theorem IsHilbertSubscheme.isInvertible {f : X ⟶ S} [SmoothOfRelativeDimension 1 f] {d : ℕ}
    {T : Over S} {I : (Limits.pullback f T.hom).IdealSheafData}
    (hI : IsHilbertSubscheme f d T I) : I.IsInvertible :=
  have : SmoothOfRelativeDimension 1 (Limits.pullback.snd f T.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f T.hom) ‹_›
  Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat _ hI.1 hI.2.1 hI.2.2.1

variable (f : X ⟶ S)


/-- The universal divisor is relative Cartier, and its line bundle classifies all fibers. -/
theorem isRelativeEffectiveCartier_universal_hilbertPresheaf [SmoothOfRelativeDimension 1 f]
    {d : ℕ} {H : Over S} (e : (hilbertPresheaf f d).RepresentableBy H) :
    (e.homEquiv (𝟙 H)).1.IsRelativeEffectiveCartier (pullback.snd f H.hom) ∧
      ∀ (T : Over S) (h : T ⟶ H), Nonempty ((e.homEquiv h).1.toModulesᵛ ≅
        (Scheme.Modules.pullback (baseChangeMap f h)).obj (e.homEquiv (𝟙 H)).1.toModulesᵛ) := by
  obtain ⟨hfin, hflat, hlfp, -⟩ := (e.homEquiv (𝟙 H)).2
  have : SmoothOfRelativeDimension 1 (pullback.snd f H.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f H.hom) ‹_›
  have hD : (e.homEquiv (𝟙 H)).1.IsRelativeEffectiveCartier (pullback.snd f H.hom) :=
    Scheme.IdealSheafData.isRelativeEffectiveCartier_of_isFinite _
  refine ⟨hD, fun T h ↦ ?_⟩
  have := SmoothOfRelativeDimension.smooth 1 f
  have hsq : IsPullback (baseChangeMap f h) (pullback.snd f T.hom) (pullback.snd f H.hom)
      h.left := by
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback f H.hom)
    rw [Over.w h]
    simpa using IsPullback.of_hasPullback f T.hom
  obtain ⟨-, hiso⟩ := hD.comap_of_isPullback hsq
  have hh := hilbertPresheaf_homEquiv_comp_val f e h (𝟙 H)
  rw [Category.comp_id] at hh
  rwa [hh]

end AlgebraicGeometry
