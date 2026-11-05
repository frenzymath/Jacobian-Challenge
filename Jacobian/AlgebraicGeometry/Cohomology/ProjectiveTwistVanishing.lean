import Jacobian.AlgebraicGeometry.Cohomology.ProjectiveTwist
import Jacobian.AlgebraicGeometry.Cohomology.Affine.Leray
import Jacobian.AlgebraicGeometry.Cohomology.Finiteness
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Cech
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Empty
import Jacobian.Algebra.Homology.CochainComplex.RestrictScalars

/-!
# Vanishing for nonnegative twisting sheaves

The monomial Čech complex computes cohomology of twisting sheaves on polynomial
projective space. Its middle cohomology is zero, and its top cohomology is zero
for nonnegative twists. Thus all positive cohomology vanishes for those twists,
over any commutative coefficient ring.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Proj

open Scheme.Modules MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (coordinates coefficients : Type u) [CommRing coefficients]

private lemma subsingleton_of_moduleIso {coefficientRing : Type u} [Ring coefficientRing]
    {sourceModule targetModule : ModuleCat coefficientRing}
    (comparison : sourceModule ≅ targetModule) (vanishing : Subsingleton targetModule) :
    Subsingleton sourceModule := by
  letI := vanishing
  exact comparison.toLinearEquiv.toEquiv.subsingleton

private lemma subsingleton_H_twist_of_subsingleton_monomial [Fintype coordinates]
    (twistDegree : ℤ) (degree : ℕ)
    [Subsingleton ((ProjectiveSpace.monomialCechComplex coordinates coefficients
      twistDegree).homology degree)] :
    Subsingleton ((twist (homogeneousSubmodule coordinates coefficients) twistDegree).H degree) := by
  letI : (twist (homogeneousSubmodule coordinates coefficients) twistDegree).IsQuasicoherent := by
    obtain ⟨generators, generatorProperties⟩ :=
      (isInvertible_twist_homogeneousSubmodule coordinates coefficients twistDegree).exists_isInvertibleData
    haveI := generatorProperties.toIsLocallyFreeData
    exact { nonempty_quasicoherentData := ⟨generators.quasiCoherentData⟩ }
  let cechComplex := (cechComplexFunctor (standardOpen coordinates coefficients)).obj
    (twist (homogeneousSubmodule coordinates coefficients) twistDegree).presheafModuleCat
  let scalarMap := ((Scheme.ΓSpecIso (.of coefficients)).inv ≫
    (projectiveSpaceOverAffineToSpec coordinates coefficients).appTop).hom
  haveI : Subsingleton
      ((((ModuleCat.restrictScalars scalarMap).mapHomologicalComplex _).obj
        cechComplex).homology degree) :=
    subsingleton_of_moduleIso (coefficientRing := coefficients)
      (cechComplexTwistHomologyIso.{u, u} coordinates coefficients twistDegree degree) inferInstance
  haveI : Subsingleton (cechComplex.homology degree) :=
    (ModuleCat.restrictScalarsHomologyIso scalarMap cechComplex degree).symm.toLinearEquiv.toEquiv.subsingleton
  obtain ⟨comparison⟩ := nonempty_cechComplex_linearEquiv_H_of_isSeparated
    (projectiveSpaceOverAffineToSpec coordinates coefficients)
    (standardOpen coordinates coefficients)
    (fun index ↦ isAffineOpen_basicOpen _ _ (isHomogeneous_X coefficients index) one_pos)
    (iSup_basicOpen_eq_top' (homogeneousSubmodule coordinates coefficients)
      (X : coordinates → MvPolynomial coordinates coefficients)
      (fun index ↦ ⟨1, isHomogeneous_X coefficients index⟩)
      (adjoin_range_X_eq_top coordinates coefficients))
    (twist (homogeneousSubmodule coordinates coefficients) twistDegree) degree
  exact comparison.symm.toEquiv.subsingleton

/-- Nonnegative twists have no positive cohomology over any commutative ring. -/
theorem subsingleton_H_twist_of_pos_of_nonneg [Finite coordinates]
    {degree : ℕ} (positiveDegree : 0 < degree) {twistDegree : ℤ}
    (nonnegativeTwist : 0 ≤ twistDegree) :
    Subsingleton ((twist (homogeneousSubmodule coordinates coefficients) twistDegree).H degree) := by
  classical
  letI : Fintype coordinates := Fintype.ofFinite coordinates
  rcases isEmpty_or_nonempty coordinates with emptyCoordinates | nonemptyCoordinates
  · letI := emptyCoordinates
    exact subsingleton_H_of_isZero
      (Scheme.Modules.isZero_of_isEmpty (twist (homogeneousSubmodule coordinates coefficients)
        twistDegree)) degree
  letI := nonemptyCoordinates
  obtain ⟨dimension, coordinateCount⟩ : ∃ dimension : ℕ,
      Fintype.card coordinates = dimension + 1 :=
    ⟨Fintype.card coordinates - 1, by have := Fintype.card_pos (α := coordinates); omega⟩
  rcases lt_trichotomy degree dimension with lowerDegree | rfl | higherDegree
  · obtain ⟨lowerDegreeIndex, rfl⟩ := Nat.exists_eq_succ_of_ne_zero positiveDegree.ne'
    letI := ModuleCat.isZero_iff_subsingleton.mp
      (ProjectiveSpace.exactAt_monomialCechComplex coordinates coefficients twistDegree
        coordinateCount lowerDegreeIndex lowerDegree).isZero_homology
    exact subsingleton_H_twist_of_subsingleton_monomial coordinates coefficients twistDegree _
  · letI := ProjectiveSpace.subsingleton_monomialCechComplex_homology_top
      (A := coefficients) coordinateCount positiveDegree.ne'
      (m := twistDegree) (by omega)
    exact subsingleton_H_twist_of_subsingleton_monomial coordinates coefficients twistDegree _
  · exact subsingleton_H_twist_homogeneousSubmodule_of_lt coordinates coefficients
      (by simpa only [Nat.card_eq_fintype_card] using coordinateCount) twistDegree higherDegree

end AlgebraicGeometry.Proj
