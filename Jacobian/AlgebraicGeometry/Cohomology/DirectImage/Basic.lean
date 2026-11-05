import Jacobian.Algebra.Category.ModuleCat.Sheaf.Grothendieck
import Jacobian.AlgebraicGeometry.Cohomology.Basic
import Jacobian.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Higher direct images of module sheaves

The category of module sheaves on a scheme is Grothendieck abelian, so it has
enough injectives. Higher direct images are the right derived functors of
the native module-sheaf pushforward. Their action on scalar endomorphisms
is induced by the structure morphism on global functions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Module sheaves on a scheme form a Grothendieck abelian category. -/
instance isGrothendieckAbelian (X : Scheme.{u}) : IsGrothendieckAbelian.{u} X.Modules :=
  SheafOfModules.isGrothendieckAbelian X.ringCatSheaf

/-- The `q`-th higher direct image of module sheaves is the `q`-th right
derived functor of pushforward. -/
def higherDirectImage (morphism : X ⟶ Y) [HasInjectiveResolutions X.Modules]
    (degree : ℕ) : X.Modules ⥤ Y.Modules :=
  (pushforward morphism).rightDerived degree

/-- Higher direct image sends multiplication by the pullback of a global
function to multiplication by that function. -/
theorem higherDirectImage_map_smulHom (morphism : X ⟶ Y)
    [HasInjectiveResolutions X.Modules] (degree : ℕ) (M : X.Modules)
    (scalar : Γ(Y, ⊤)) :
    (higherDirectImage morphism degree).map (M.smulHom (morphism.appTop scalar)) =
      ((higherDirectImage morphism degree).obj M).smulHom scalar :=
  (pushforward morphism).rightDerived_map_app_eq
    { app M := M.smulHom (morphism.appTop scalar)
      naturality _ _ coefficientMap := (smulHom_naturality coefficientMap _).symm }
    { app N := N.smulHom scalar
      naturality _ _ coefficientMap := (smulHom_naturality coefficientMap _).symm }
    (fun M ↦ pushforward_map_smulHom morphism M scalar) degree M

end AlgebraicGeometry.Scheme.Modules
