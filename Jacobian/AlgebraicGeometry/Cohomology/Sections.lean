import Jacobian.AlgebraicGeometry.Cohomology.Basic
import Jacobian.AlgebraicGeometry.Modules.GlobalSection

/-!
# Structure-module morphisms and zeroth cohomology

Evaluation at one identifies morphisms from the structure module with global
sections, and hence with zeroth sheaf cohomology.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.H

variable {sourceScheme : Scheme.{u}}

/-- A structure-module morphism determines its actual zeroth cohomology class. -/
def unitHomAddEquiv (moduleSheaf : sourceScheme.Modules) :
    (unit sourceScheme ⟶ moduleSheaf) ≃+ moduleSheaf.H 0 :=
  (Modules.unitHomAddEquiv moduleSheaf).trans (zeroLinearEquiv moduleSheaf).symm.toAddEquiv

end AlgebraicGeometry.Scheme.Modules.H
