import Jacobian.AlgebraicGeometry.Cohomology.FiniteScheme
import Jacobian.AlgebraicGeometry.GlobalSections.Proper

/-!
# Structure-sheaf cohomology and constants

For a proper geometrically integral scheme over a field, constants identify
zeroth structure-sheaf cohomology with the ground field. The scalar action is
the one induced by the given structure morphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- Constants identify zeroth structure-sheaf cohomology of a proper
geometrically integral scheme with the ground field. -/
def H.unitZeroFieldLinearEquiv : H (X := X) (SheafOfModules.unit X.ringCatSheaf) 0 ≃ₗ[k] k := by
  letI := (globalSectionsRingHom k (X := X)).toAlgebra
  have constantsBijective : Function.Bijective (globalSectionsRingHom k (X := X)) :=
    (bijective_appTop_of_isProper_of_geometricallyIntegral (X ↘ Spec (.of k))).comp
      (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of k)).inv)
  let constants := LinearEquiv.ofBijective (Algebra.linearMap k Γ(X, ⊤)) constantsBijective
  exact (H.unitZeroLinearEquiv (k := k) (X := X)).trans constants.symm

/-- Zeroth structure-sheaf cohomology is finite-dimensional. -/
theorem finite_H_unit_zero :
    Module.Finite k (H (X := X) (SheafOfModules.unit X.ringCatSheaf) 0) :=
  Module.Finite.equiv (H.unitZeroFieldLinearEquiv (k := k) (X := X)).symm

/-- Constants form a one-dimensional space of zeroth structure-sheaf cohomology. -/
theorem finrankH_unit_zero_eq_one :
    finrankH (X := X) k (SheafOfModules.unit X.ringCatSheaf) 0 = 1 :=
  (H.unitZeroFieldLinearEquiv (k := k) (X := X)).finrank_eq.trans (Module.finrank_self k)

end AlgebraicGeometry.Scheme.Modules
