import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Dualization of modules as a functor

Taking the linear dual sends a linear map to its transpose and defines a
contravariant functor on modules over a commutative ring.
-/

noncomputable section

universe u v

open CategoryTheory

namespace ModuleCat

/-- The contravariant functor sending a module to its linear dual. -/
@[simps]
def dualFunctor (baseRing : Type u) [CommRing baseRing] :
    (ModuleCat.{v} baseRing)ᵒᵖ ⥤ ModuleCat.{max u v} baseRing where
  obj coefficient := ModuleCat.of baseRing (Module.Dual baseRing coefficient.unop)
  map morphism := ModuleCat.ofHom (Module.Dual.transpose morphism.unop.hom)

end ModuleCat
