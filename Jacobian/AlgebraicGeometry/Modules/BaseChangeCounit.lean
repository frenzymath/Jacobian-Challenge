import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Jacobian.CategoryTheory.Adjunction.MatesArrow

/-!
# Base change of evaluation maps

A commutative square of schemes determines the canonical base-change
morphism for direct images of module sheaves, as the mate of the square of
pullback functors. Whenever this canonical morphism is invertible, evaluation
commutes with base change as an arrow.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
  {g : S' ⟶ S} {g' : X' ⟶ X}

/-- The two iterated pullbacks around a commutative square are naturally isomorphic. -/
def pullbackSquareIso (commutes : f' ≫ g = g' ≫ f) :
    pullback g ⋙ pullback f' ≅ pullback f ⋙ pullback g' :=
  pullbackComp f' g ≪≫ pullbackCongr commutes ≪≫ (pullbackComp g' f).symm

/-- The canonical direct-image base-change morphism, obtained by taking a mate. -/
def pushforwardBaseChange (commutes : f' ≫ g = g' ≫ f) :
    pushforward f ⋙ pullback g ⟶ pullback g' ⋙ pushforward f' :=
  (mateEquiv (pullbackPushforwardAdjunction f) (pullbackPushforwardAdjunction f')
    (pullbackSquareIso commutes).hom).natTrans

/-- If canonical base change is invertible, pullback of evaluation is evaluation
for the pulled-back sheaf, up to the canonical arrow isomorphism. -/
def arrowIsoPullbackCounit (commutes : f' ≫ g = g' ≫ f) (M : X.Modules)
    [IsIso ((pushforwardBaseChange commutes).app M)] :
    Arrow.mk ((pullback g').map ((pullbackPushforwardAdjunction f).counit.app M)) ≅
      Arrow.mk ((pullbackPushforwardAdjunction f').counit.app ((pullback g').obj M)) := by
  have : IsIso ((pullbackSquareIso commutes).hom.app ((pushforward f).obj M)) :=
    inferInstanceAs (IsIso ((pullbackSquareIso commutes).app _).hom)
  letI : IsIso ((mateEquiv (pullbackPushforwardAdjunction f)
      (pullbackPushforwardAdjunction f') (pullbackSquareIso commutes).hom).app M) := by
    change IsIso ((pushforwardBaseChange commutes).app M)
    infer_instance
  exact Adjunction.arrowIsoMapCounit (pullbackPushforwardAdjunction f)
    (pullbackPushforwardAdjunction f') (pullbackSquareIso commutes).hom M

end AlgebraicGeometry.Scheme.Modules
