import Jacobian.AlgebraicGeometry.Cohomology.ProjectiveTwistFinite
import Jacobian.AlgebraicGeometry.Cohomology.ProjectiveTwistPresentation
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Empty

/-!
# Finite cohomology on projective space

Every coherent sheaf on polynomial projective space over a Noetherian ring has
finite cohomology over that ring. The proof is descending induction on
cohomological degree for all coherent sheaves at once: a finite sum of twists
surjects onto the sheaf, its kernel is coherent, and the native cohomology long
exact sequence gives the induction step.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry.Proj

open Scheme.Modules MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (coordinates : Type v) (coefficients : Type (max u v)) [CommRing coefficients]
  [IsNoetherianRing coefficients] [Finite coordinates]

/-- Coherent sheaves on projective space have finite cohomology in every degree. -/
theorem finite_H
    (moduleSheaf : (projectiveSpaceOverAffine.{u, v} coordinates coefficients).Modules)
    [finitePresentation : moduleSheaf.IsFinitePresentation] (degree : ℕ) :
    letI := moduleHOfSpec.{max u v}
      (projectiveSpaceOverAffineToSpec.{u, v} coordinates coefficients) moduleSheaf degree
    Module.Finite coefficients (moduleSheaf.H degree) := by
  rcases isEmpty_or_nonempty coordinates with emptyCoordinates | nonemptyCoordinates
  · letI := emptyCoordinates
    letI := moduleHOfSpec.{max u v}
      (projectiveSpaceOverAffineToSpec.{u, v} coordinates coefficients) moduleSheaf degree
    letI := subsingleton_H_of_isZero (Scheme.Modules.isZero_of_isEmpty moduleSheaf) degree
    infer_instance
  · letI := nonemptyCoordinates
    obtain ⟨dimension, coordinateCount⟩ : ∃ dimension : ℕ,
        Nat.card coordinates = dimension + 1 :=
      ⟨Nat.card coordinates - 1, by have := Nat.card_pos (α := coordinates); omega⟩
    suffices inductionClaim : ∀ step : ℕ,
        ∀ (moduleSheaf : (projectiveSpaceOverAffine.{u, v} coordinates coefficients).Modules)
        [moduleSheaf.IsFinitePresentation], ∀ degree : ℕ, dimension < degree + step →
        letI := moduleHOfSpec.{max u v}
          (projectiveSpaceOverAffineToSpec.{u, v} coordinates coefficients) moduleSheaf degree
        Module.Finite coefficients (moduleSheaf.H degree) from
      @inductionClaim (degree + dimension + 1) moduleSheaf finitePresentation degree (by omega)
    intro step
    induction step with
    | zero =>
      intro moduleSheaf _ degree degreeBound
      letI := moduleHOfSpec.{max u v}
        (projectiveSpaceOverAffineToSpec.{u, v} coordinates coefficients) moduleSheaf degree
      letI := subsingleton_H_projectiveSpaceOverAffine_of_lt.{u, v} coordinates coefficients
        coordinateCount moduleSheaf (by omega : dimension < degree)
      infer_instance
    | succ step inductionHypothesis =>
      intro moduleSheaf _ degree degreeBound
      by_cases earlierBound : dimension < degree + step
      · exact inductionHypothesis moduleSheaf degree earlierBound
      obtain ⟨indices, finiteIndices, twists, quotientMap, quotientEpi,
        coherentKernel, finiteKernel⟩ := exists_epi_sigma_twist.{u, v}
          coordinates coefficients moduleSheaf
      letI := finiteIndices
      letI := coherentKernel
      letI := finiteKernel
      have shortExact : (ShortComplex.kernelSequence quotientMap).ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact quotientMap)
          inferInstance quotientEpi
      exact finite_H_X₃_of_shortExact
        (p := projectiveSpaceOverAffineToSpec.{u, v} coordinates coefficients) shortExact degree
        (finite_H_sigma (p := projectiveSpaceOverAffineToSpec.{u, v} coordinates coefficients)
          _ degree fun index ↦ finite_H_twist.{u, v} coordinates coefficients _ degree)
        (inductionHypothesis (kernel quotientMap) (degree + 1) (by omega))

/-- Coherent sheaves on projective space satisfy the native finite-cohomology property. -/
theorem hasFiniteH_projectiveSpaceOverAffine
    (moduleSheaf : (projectiveSpaceOverAffine.{u, v} coordinates coefficients).Modules)
    [moduleSheaf.IsFinitePresentation] :
  HasFiniteH (projectiveSpaceOverAffineToSpec.{u, v} coordinates coefficients) moduleSheaf :=
  finite_H.{u, v} coordinates coefficients moduleSheaf

end AlgebraicGeometry.Proj
