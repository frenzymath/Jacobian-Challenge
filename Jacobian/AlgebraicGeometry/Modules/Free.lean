import Jacobian.AlgebraicGeometry.Modules.Invertible
import Jacobian.Topology.Category.TopCat.OpensPullback

/-!
# Pullback of free module sheaves

Pullback preserves free module sheaves on a fixed set of generators.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
open SheafOfModules
variable {X Y : Scheme.{u}}
/-- Pullback carries a free sheaf on a set to the free sheaf on the same set. -/
noncomputable def pullbackFreeIso (g : Y ⟶ X) (I : Type u) :
    (pullback g).obj (free (R := X.ringCatSheaf) I) ≅ free I :=
  SheafOfModules.pullbackObjFreeIso g.toRingCatSheafHom I

end AlgebraicGeometry.Scheme.Modules
