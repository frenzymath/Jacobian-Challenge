import Jacobian.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist
import Jacobian.RingTheory.MvPolynomial.Homogeneous

/-!
# Invertible twisting sheaves on projective space

The variables of a polynomial ring give a degree-one standard cover of its
projective spectrum. Thus every twisting sheaf is invertible, and hence finitely
presented and quasi-coherent, without a noetherian assumption on the base ring.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (coordinates : Type v)

/-- The standard opens `D₊(Tᵢ)` cover `Proj R[Tᵢ]`, and `Tᵢ` has degree `1`. -/
lemma Proj.exists_mem_basicOpen_homogeneousSubmodule (baseRing : Type (max u v)) [CommRing baseRing]
    (element : Proj (MvPolynomial.homogeneousSubmodule coordinates baseRing)) :
    ∃ morphism ∈ MvPolynomial.homogeneousSubmodule coordinates baseRing 1,
      element ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule coordinates baseRing) morphism := by
  have compatibility := Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule coordinates baseRing)
    (MvPolynomial.X : coordinates → MvPolynomial coordinates baseRing) (fun coordinate ↦ ⟨1, MvPolynomial.isHomogeneous_X baseRing coordinate⟩)
    (MvPolynomial.adjoin_range_X_eq_top coordinates baseRing)
  have hx : element ∈ ⨆ coordinate, Proj.basicOpen (MvPolynomial.homogeneousSubmodule coordinates baseRing)
      (MvPolynomial.X coordinate) := by
    rw [compatibility]
    trivial
  obtain ⟨coordinate, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨_, MvPolynomial.isHomogeneous_X baseRing coordinate, hi⟩

/-- **`𝒪(m)` is invertible on `Proj R[Tᵢ]`**: the standard opens `D₊(Tᵢ)` cover `Proj R[Tᵢ]`
and `Tᵢ` has degree `1`. No finiteness of `n` is needed. -/
instance Proj.isInvertible_twist_homogeneousSubmodule (baseRing : Type (max u v)) [CommRing baseRing]
    (twistDegree : ℤ) :
    (Proj.twist (MvPolynomial.homogeneousSubmodule coordinates baseRing) twistDegree).IsInvertible :=
  Proj.isInvertible_twist _ twistDegree (Proj.exists_mem_basicOpen_homogeneousSubmodule coordinates baseRing)

end AlgebraicGeometry
