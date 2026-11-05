import Jacobian.AlgebraicGeometry.Cohomology.Basic
import Mathlib.AlgebraicGeometry.Fiber

/-!
# Cohomological invariants of fibers

For a family of schemes and a module sheaf on its source, the cohomology
dimensions and Euler characteristic on a fiber are computed after pullback
to that fiber, with scalars in the residue field of the parameter point.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}

/-- The dimension of cohomology on the fiber over a point of the base. -/
def hFiber (M : X.Modules) (f : X ⟶ T) (q : ℕ) (t : T) : ℕ :=
  letI := f.fiberOverSpecResidueField t
  ((pullback (f.fiberι t)).obj M).finrankH (T.residueField t) q

/-- The Euler characteristic on the residue-field fiber. -/
def eulerCharFiber (M : X.Modules) (f : X ⟶ T) (t : T) : ℤ :=
  ∑ᶠ q : ℕ, (-1) ^ q * (M.hFiber f q t : ℤ)

/-- Fiber cohomology dimensions depend only on the module-sheaf isomorphism class. -/
lemma hFiber_congr {M N : X.Modules} (e : M ≅ N) (f : X ⟶ T) (q : ℕ) (t : T) :
    M.hFiber f q t = N.hFiber f q t :=
  letI := f.fiberOverSpecResidueField t
  finrankH_congr _ ((pullback (f.fiberι t)).mapIso e) q

/-- Fiber Euler characteristics depend only on the module-sheaf isomorphism class. -/
lemma eulerCharFiber_congr {M N : X.Modules} (e : M ≅ N) (f : X ⟶ T) :
    M.eulerCharFiber f = N.eulerCharFiber f := by
  ext t
  simp only [eulerCharFiber, hFiber_congr e]

end AlgebraicGeometry.Scheme.Modules
