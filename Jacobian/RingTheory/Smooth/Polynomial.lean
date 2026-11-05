import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Polynomial algebras of fixed smooth relative dimension

The presentation with the indeterminates as generators and no relations exhibits a
 polynomial algebra as standard smooth of the expected relative dimension.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace MvPolynomial

open Algebra

variable (baseRing : Type u) [CommRing baseRing] (indeterminates : Type v) [Finite indeterminates]

/-- The submersive presentation of `R[Xᵢ : i ∈ σ]` with the indeterminates as generators and no
relations. -/
noncomputable def submersivePresentation :
    SubmersivePresentation baseRing (MvPolynomial indeterminates baseRing) indeterminates PEmpty.{1} where
  __ := (PreSubmersivePresentation.naive (v := (PEmpty.elim : PEmpty.{1} → MvPolynomial indeterminates baseRing))
    PEmpty.elim (fun relation ↦ relation.elim)).ofAlgEquiv
      ((Ideal.quotientEquivAlgOfEq baseRing (by simp)).trans (AlgEquiv.quotientBot baseRing _))
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp [Matrix.det_isEmpty]

/-- The polynomial algebra `R[Xᵢ : i ∈ σ]` in finitely many indeterminates is standard smooth of
relative dimension `#σ` over `R`. -/
instance isStandardSmoothOfRelativeDimension :
    IsStandardSmoothOfRelativeDimension (Nat.card indeterminates) baseRing (MvPolynomial indeterminates baseRing) :=
  (submersivePresentation baseRing indeterminates).isStandardSmoothOfRelativeDimension (by
    simp [Presentation.dimension])

end MvPolynomial
