import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Evaluation of sheaves of modules

Taking sections over an object is additive in the coefficient sheaf.
-/

universe v v' u u'

open CategoryTheory

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (U : Cᵒᵖ)

instance evaluation_additive : (evaluation.{v} R U).Additive where
  map_add := rfl

end SheafOfModules
