import Jacobian.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-!
# Abelian varieties as commutative group schemes

An abelian variety carries its actual commutative group scheme, together with
smoothness, properness and geometric irreducibility. Morphisms retain their
commutative-group homomorphism laws.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A smooth proper geometrically irreducible commutative group scheme over a field. -/
structure AbelianVariety (baseField : Type u) [Field baseField] where
  group : CommGrp (Over (Spec (.of baseField)))
  [smooth : Smooth group.X.hom]
  [proper : IsProper group.X.hom]
  [geometricallyIrreducible : GeometricallyIrreducible group.X.hom]

attribute [instance] AbelianVariety.smooth AbelianVariety.proper
  AbelianVariety.geometricallyIrreducible

instance (baseField : Type u) [Field baseField] : Category (AbelianVariety baseField) :=
  inferInstanceAs (Category (InducedCategory _ AbelianVariety.group))

/-- Forget the geometric properties, retaining the commutative group scheme. -/
def AbelianVariety.forget (baseField : Type u) [Field baseField] :
    AbelianVariety baseField ⥤ CommGrp (Over (Spec (.of baseField))) := inducedFunctor _

end AlgebraicGeometry
