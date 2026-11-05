import Jacobian.AlgebraicGeometry.Cohomology.ProjectiveTwistPresentation
import Jacobian.AlgebraicGeometry.Cohomology.ProjectiveTwistVanishing
import Jacobian.AlgebraicGeometry.Cohomology.Vanishing
import Jacobian.AlgebraicGeometry.Modules.TensorEquivalence
import Jacobian.AlgebraicGeometry.Modules.FinitePushforward
import Jacobian.AlgebraicGeometry.Modules.ProjectionFormula

/-!
# Serre vanishing on projective space

Positive cohomology of nonnegative twists vanishes over any commutative ring.
Over a Noetherian ring, a finite presentation by negative twists and descending
induction on cohomological degree give Serre vanishing for coherent modules.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Proj

open Scheme.Modules MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (coordinates coefficients : Type u) [CommRing coefficients]

/-- Every coherent module on finite-dimensional projective space over a Noetherian
ring has vanishing positive cohomology after all sufficiently positive twists. -/
theorem exists_subsingleton_H_tensor_twist [IsNoetherianRing coefficients] [Finite coordinates]
    (moduleSheaf : (projectiveSpaceOverAffine coordinates coefficients).Modules)
    [moduleSheaf.IsFinitePresentation] :
    ∃ bound : ℤ, ∀ twistDegree ≥ bound, ∀ degree : ℕ, 0 < degree →
      Subsingleton ((moduleSheaf ⊗ twist (homogeneousSubmodule coordinates coefficients)
        twistDegree).H degree) := by
  classical
  rcases isEmpty_or_nonempty coordinates with emptyCoordinates | nonemptyCoordinates
  · letI := emptyCoordinates
    exact ⟨0, fun twistDegree _ degree _ ↦ subsingleton_H_of_isZero
      (Scheme.Modules.isZero_of_isEmpty _) degree⟩
  letI := nonemptyCoordinates
  obtain ⟨dimension, coordinateCount⟩ : ∃ dimension : ℕ,
      Nat.card coordinates = dimension + 1 :=
    ⟨Nat.card coordinates - 1, by have := Nat.card_pos (α := coordinates); omega⟩
  suffices inductionClaim : ∀ step : ℕ,
      ∀ (moduleSheaf : (projectiveSpaceOverAffine coordinates coefficients).Modules)
        [moduleSheaf.IsFinitePresentation],
        ∃ bound : ℤ, ∀ twistDegree ≥ bound, ∀ degree : ℕ,
          dimension < degree + step → 0 < degree →
          Subsingleton ((moduleSheaf ⊗ twist (homogeneousSubmodule coordinates coefficients)
            twistDegree).H degree) by
    obtain ⟨bound, vanishing⟩ := inductionClaim (dimension + 1) moduleSheaf
    exact ⟨bound, fun twistDegree degreeBound degree positiveDegree ↦
      vanishing twistDegree degreeBound degree (by omega) positiveDegree⟩
  intro step
  induction step with
  | zero =>
    intro coefficientSheaf _
    refine ⟨0, fun twistDegree _ degree degreeBound _ ↦ ?_⟩
    letI : (coefficientSheaf ⊗ twist (homogeneousSubmodule coordinates coefficients)
        twistDegree).IsQuasicoherent :=
      isQuasicoherent_tensorObj_of_isInvertible coefficientSheaf _
    exact subsingleton_H_projectiveSpaceOverAffine_of_lt coordinates coefficients
      coordinateCount _ (by omega)
  | succ step inductionHypothesis =>
    intro coefficientSheaf _
    obtain ⟨indices, finiteIndices, twists, quotientMap, quotientEpi,
      quasicoherentKernel, finiteKernel⟩ := exists_epi_sigma_twist coordinates coefficients coefficientSheaf
    letI := finiteIndices
    letI := quasicoherentKernel
    letI := finiteKernel
    letI := quotientEpi
    obtain ⟨maximumTwist, twistBound⟩ := (Set.finite_range twists).bddAbove
    obtain ⟨kernelBound, kernelVanishing⟩ := inductionHypothesis (kernel quotientMap)
    refine ⟨max kernelBound (maximumTwist : ℤ),
      fun twistDegree degreeBound degree cohomologicalBound positiveDegree ↦ ?_⟩
    have kernelBound_le : kernelBound ≤ twistDegree := (le_max_left _ _).trans degreeBound
    have twist_le : ∀ index, (twists index : ℤ) ≤ twistDegree := fun index ↦
      (Nat.cast_le.mpr (twistBound ⟨index, rfl⟩)).trans ((le_max_right _ _).trans degreeBound)
    let lineBundle := twist (homogeneousSubmodule coordinates coefficients) twistDegree
    letI : lineBundle.IsInvertible :=
      isInvertible_twist_homogeneousSubmodule coordinates coefficients twistDegree
    have shortExact : (ShortComplex.kernelSequence quotientMap).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact quotientMap)
        inferInstance quotientEpi
    have twistedShortExact := tensorRight_shortExact lineBundle shortExact
    let summands := fun index ↦ twist (homogeneousSubmodule coordinates coefficients)
      (-(twists index : ℤ))
    have summandVanishing : ∀ index, Subsingleton ((summands index ⊗ lineBundle).H degree) := by
      intro index
      obtain ⟨comparison⟩ := nonempty_tensorObj_twist_iso
        (homogeneousSubmodule coordinates coefficients)
        (exists_mem_basicOpen_homogeneousSubmodule coordinates coefficients)
        (-(twists index : ℤ)) twistDegree
      letI := subsingleton_H_twist_of_pos_of_nonneg coordinates coefficients positiveDegree
        (twistDegree := -(twists index : ℤ) + twistDegree) (by have := twist_le index; omega)
      exact (H.mapLinearEquiv comparison degree).toEquiv.subsingleton
    letI : Subsingleton
        ((∐ fun index ↦ (tensorRight lineBundle).obj (summands index)).H degree) :=
      subsingleton_H_sigma (fun index ↦ (tensorRight lineBundle).obj (summands index))
        degree summandVanishing
    have middleVanishing : Subsingleton (((tensorRight lineBundle).obj (∐ summands)).H degree) :=
      (H.mapLinearEquiv (PreservesCoproduct.iso (tensorRight lineBundle) summands) degree).toEquiv.subsingleton
    exact subsingleton_H_X₃_of_shortExact twistedShortExact degree middleVanishing
      (kernelVanishing twistDegree kernelBound_le (degree + 1) (by omega) (by omega))

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Serre vanishing pulls back to any scheme finite over polynomial projective space. -/
theorem exists_subsingleton_H_tensor_pullback_twist_of_isFinite
    (coordinates coefficients : Type u) [CommRing coefficients] [IsNoetherianRing coefficients]
    [Finite coordinates] {sourceScheme : Scheme.{u}}
    (morphism : sourceScheme ⟶ Proj.projectiveSpaceOverAffine coordinates coefficients)
    [IsFinite morphism] (moduleSheaf : sourceScheme.Modules)
    [moduleSheaf.IsFinitePresentation] :
    ∃ bound : ℤ, ∀ twistDegree ≥ bound, ∀ degree : ℕ, 0 < degree →
      Subsingleton ((moduleSheaf ⊗ (pullback morphism).obj
        (Proj.twist (MvPolynomial.homogeneousSubmodule coordinates coefficients)
          twistDegree)).H degree) := by
  letI : IsLocallyNoetherian (Proj.projectiveSpaceOverAffine coordinates coefficients) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Proj.projectiveSpaceOverAffineToSpec coordinates coefficients)
  letI := isFinitePresentation_pushforward_of_isFinite morphism moduleSheaf
  letI := isQuasicoherent_pushforward_of_isAffineHom morphism moduleSheaf
  obtain ⟨bound, vanishing⟩ := Proj.exists_subsingleton_H_tensor_twist coordinates coefficients
    ((pushforward morphism).obj moduleSheaf)
  refine ⟨bound, fun twistDegree degreeBound degree positiveDegree ↦ ?_⟩
  let lineBundle := Proj.twist (MvPolynomial.homogeneousSubmodule coordinates coefficients) twistDegree
  letI : lineBundle.IsInvertible :=
    Proj.isInvertible_twist_homogeneousSubmodule coordinates coefficients twistDegree
  let twistedModule := moduleSheaf ⊗ (pullback morphism).obj lineBundle
  letI : twistedModule.IsQuasicoherent :=
    isQuasicoherent_tensorObj_of_isInvertible moduleSheaf _
  letI := vanishing twistDegree degreeBound degree positiveDegree
  letI : Subsingleton (((pushforward morphism).obj twistedModule).H degree) :=
    (H.mapLinearEquiv (pushforwardTensorPullbackIso morphism moduleSheaf lineBundle)
      degree).toEquiv.subsingleton
  obtain ⟨comparison⟩ := nonempty_functorH_iso_pushforwardAb_of_isAffineHom morphism degree
  let additiveComparison : twistedModule.H degree ≃+
      ((pushforward morphism).obj twistedModule).H degree :=
    (comparison.app
      ⟨(SheafOfModules.toSheaf sourceScheme.ringCatSheaf).obj twistedModule,
        cechAcyclicOnAffines_of_isQuasicoherent twistedModule⟩).addCommGroupIsoToAddEquiv
  exact additiveComparison.toEquiv.subsingleton

end AlgebraicGeometry.Scheme.Modules
