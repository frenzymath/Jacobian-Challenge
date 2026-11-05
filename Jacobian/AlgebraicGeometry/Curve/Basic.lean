import Jacobian.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Smooth proper curves

Smooth proper geometrically irreducible curves over a field form a category
whose morphisms are morphisms of schemes over that field. The forgetful functor
retains every such morphism, and scheme isomorphisms induce curve isomorphisms.
-/

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

/-- The category of smooth, proper, geometrically irreducible curves over `k`, with morphisms the
morphisms of `k`-schemes. -/
structure Curve (k : Type u) [Field k] where
  /-- The underlying `k`-scheme. -/
  carrier : Over (Spec (.of k))
  [isProper : IsProper carrier.hom]
  [smoothOfRelativeDimension : SmoothOfRelativeDimension 1 carrier.hom]
  [geometricallyIrreducible : GeometricallyIrreducible carrier.hom]

attribute [instance] Curve.isProper Curve.smoothOfRelativeDimension Curve.geometricallyIrreducible

noncomputable instance (k : Type u) [Field k] : Category (Curve k) where
  Hom X Y := X.carrier ⟶ Y.carrier
  id X := 𝟙 X.carrier
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

namespace Curve

/-- An isomorphism of the underlying schemes over the field is a curve isomorphism. -/
def isoMk {k : Type u} [Field k] {C D : Curve k} (e : C.carrier ≅ D.carrier) :
    C ≅ D where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- Forgetting the geometric properties retains every morphism over the field. -/
def forget (k : Type u) [Field k] : Curve k ⥤ Over (Spec (.of k)) where
  obj C := C.carrier
  map f := f

end Curve
end AlgebraicGeometry
