import Jacobian.AlgebraicGeometry.Cohomology.Basic
import Jacobian.AlgebraicGeometry.Curve.Basic

/-!
# Arithmetic genus and cohomological degree

The arithmetic genus of a scheme over a field is the dimension of its first
structure-sheaf cohomology. The degree of a module sheaf is the difference
between its Euler characteristic and that of the structure sheaf. These
definitions do not require a choice of rational point or projective embedding.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The arithmetic genus, defined by first structure-sheaf cohomology. -/
def arithmeticGenus : ℕ :=
  Modules.finrankH k (SheafOfModules.unit X.ringCatSheaf) 1

namespace Modules

variable {X}

/-- The cohomological degree of a module sheaf over a field. -/
def degree (M : X.Modules) : ℤ :=
  M.eulerChar k - Modules.eulerChar k (SheafOfModules.unit X.ringCatSheaf)

/-- Isomorphic module sheaves have equal cohomological degrees. -/
theorem degree_congr {M N : X.Modules} (e : M ≅ N) : M.degree k = N.degree k := by
  simp only [degree, eulerChar_congr k e]

/-- The structure sheaf has degree zero. -/
@[simp]
theorem degree_unit : degree k (SheafOfModules.unit X.ringCatSheaf) = 0 :=
  sub_self _

end Modules

end AlgebraicGeometry.Scheme
