import Jacobian.AlgebraicGeometry.Modules.BaseChangeCounit
import Jacobian.AlgebraicGeometry.Picard.Counit
import Jacobian.AlgebraicGeometry.Picard.Presheaf

/-!
# Base change of Picard evaluation maps

Invertibility of the canonical direct-image base-change morphism identifies
the evaluation arrow of a Picard class with that of its pullback. Consequently
their scheme-theoretic zero loci agree after base change.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {X S : Scheme.{u}} (f : X ⟶ S) {T T' : Over S} (i : T' ⟶ T)
  (L : (pullback f T.hom).Pic)

/-- Canonical direct-image base change identifies evaluation arrows, including
the chosen representatives of the pullback Picard classes. -/
def arrowIsoPullbackDirectImageCounit
    [IsIso ((Modules.pushforwardBaseChange (isPullback_baseChangeMap f i).w.symm).app
      ((fromSkeleton _).obj L.val))] :
    Arrow.mk ((Modules.pullback (baseChangeMap f i)).map (Pic.directImageCounit f T L)) ≅
      Arrow.mk (Pic.directImageCounit f T' (Pic.map (baseChangeMap f i) L)) := by
  let representativeIso : (Modules.pullback (baseChangeMap f i)).obj
      ((fromSkeleton _).obj L.val) ≅
      (fromSkeleton _).obj (Pic.map (baseChangeMap f i) L).val :=
    (fromSkeletonToSkeletonIso _).symm
  let adj := Modules.pullbackPushforwardAdjunction (pullback.snd f T'.hom)
  exact Modules.arrowIsoPullbackCounit (isPullback_baseChangeMap f i).w.symm
      ((fromSkeleton _).obj L.val) ≪≫
    Arrow.isoMk ((Modules.pullback (pullback.snd f T'.hom)).mapIso
      ((Modules.pushforward (pullback.snd f T'.hom)).mapIso representativeIso))
      representativeIso (adj.counit.naturality representativeIso.hom)

/-- The zero locus of evaluation commutes with base change whenever the
canonical direct-image base-change map is invertible. -/
theorem comap_zeroLocus_directImageCounit
    [((Modules.pushforward (pullback.snd f T.hom)).obj
      ((fromSkeleton _).obj L.val)).IsInvertible]
    [((Modules.pushforward (pullback.snd f T'.hom)).obj
      ((fromSkeleton _).obj (Pic.map (baseChangeMap f i) L).val)).IsInvertible]
    [IsIso ((Modules.pushforwardBaseChange (isPullback_baseChangeMap f i).w.symm).app
      ((fromSkeleton _).obj L.val))] :
    (Pic.directImageCounit f T L).zeroLocus.comap (baseChangeMap f i) =
      (Pic.directImageCounit f T' (Pic.map (baseChangeMap f i) L)).zeroLocus := by
  rw [Modules.Hom.comap_zeroLocus]
  exact Modules.Hom.zeroLocus_eq_of_arrowIso _ _ (arrowIsoPullbackDirectImageCounit f i L)

end AlgebraicGeometry
