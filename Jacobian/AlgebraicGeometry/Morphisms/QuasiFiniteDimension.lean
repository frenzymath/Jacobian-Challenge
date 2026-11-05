import Jacobian.AlgebraicGeometry.Curve.Dimension
import Jacobian.Topology.KrullDimension.Maps
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# Dimension under quasi-finite surjections

A universally closed quasi-finite surjection preserves topological dimension.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Universally closed quasi-finite surjections preserve dimension. -/
theorem Scheme.Hom.topologicalKrullDim_eq_of_surjective (f : X ⟶ Y) [UniversallyClosed f]
    [LocallyQuasiFinite f] [Surjective f] : topologicalKrullDim X = topologicalKrullDim Y :=
  le_antisymm
    (topologicalKrullDim_le_of_continuous f.continuous fun _ _ ↦ f.eq_of_specializes_of_apply_eq)
    (topologicalKrullDim_le_of_specializingMap f.isClosedMap.specializingMap f.surjective)

end AlgebraicGeometry
