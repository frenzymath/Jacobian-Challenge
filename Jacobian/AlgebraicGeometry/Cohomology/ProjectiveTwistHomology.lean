import Jacobian.Algebra.Homology.CochainComplex.RestrictScalars
import Jacobian.AlgebraicGeometry.Cohomology.Affine.Leray
import Jacobian.AlgebraicGeometry.Cohomology.Finiteness
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Cech
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.Polynomial

/-!
# Cohomology of twists from the monomial complex

The standard affine cover compares actual twist cohomology with the monomial
Čech complex. Its degree-zero and top-degree coefficient descriptions identify
cohomology with homogeneous polynomials and their duals.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe baseUniverse coordinateUniverse

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry.Proj

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (coordinates : Type coordinateUniverse)
  (baseField : Type (max baseUniverse coordinateUniverse)) [Field baseField]

private theorem isQuasicoherent_polynomial_twist (twistDegree : ℤ) :
    (twist (homogeneousSubmodule coordinates baseField) twistDegree).IsQuasicoherent := by
  obtain ⟨generators, generatorProperties⟩ :=
    (isInvertible_twist_homogeneousSubmodule.{baseUniverse, coordinateUniverse}
      coordinates baseField twistDegree).exists_isInvertibleData
  haveI := generatorProperties.toIsLocallyFreeData
  exact { nonempty_quasicoherentData := ⟨generators.quasiCoherentData⟩ }

/-- Twist cohomology is linearly equivalent to the actual monomial Čech homology. -/
theorem nonempty_H_twist_linearEquiv_homology [Fintype coordinates]
    (twistDegree : ℤ) (cohomologyDegree : ℕ) :
    letI := moduleHOfSpec (projectiveSpaceOverAffineToSpec coordinates baseField)
      (twist (homogeneousSubmodule coordinates baseField) twistDegree) cohomologyDegree
    Nonempty ((twist (homogeneousSubmodule coordinates baseField) twistDegree).H
      cohomologyDegree ≃ₗ[baseField]
        (ProjectiveSpace.monomialCechComplex coordinates baseField twistDegree).homology
          cohomologyDegree) := by
  letI := moduleHOfSpec (projectiveSpaceOverAffineToSpec coordinates baseField)
    (twist (homogeneousSubmodule coordinates baseField) twistDegree) cohomologyDegree
  let scalarMap := ((Scheme.ΓSpecIso (.of baseField)).inv ≫
    (projectiveSpaceOverAffineToSpec coordinates baseField).appTop).hom
  let cechComplex := (cechComplexFunctor (standardOpen coordinates baseField)).obj
    (twist (homogeneousSubmodule coordinates baseField) twistDegree).presheafModuleCat
  obtain ⟨lerayComparison⟩ :=
    @nonempty_cechComplex_linearEquiv_H_of_isSeparated.{baseUniverse, coordinateUniverse}
    (Proj (homogeneousSubmodule coordinates baseField)) (Spec (.of baseField))
    (projectiveSpaceOverAffineToSpec coordinates baseField)
    inferInstance inferInstance coordinates
    (standardOpen coordinates baseField)
    (fun index ↦ isAffineOpen_basicOpen _ _ (isHomogeneous_X baseField index) one_pos)
    (iSup_basicOpen_eq_top' (homogeneousSubmodule coordinates baseField)
      (X : coordinates → MvPolynomial coordinates baseField)
      (fun index ↦ ⟨1, isHomogeneous_X baseField index⟩)
      (adjoin_range_X_eq_top coordinates baseField))
    (twist (homogeneousSubmodule coordinates baseField) twistDegree)
    (isQuasicoherent_polynomial_twist coordinates baseField twistDegree) cohomologyDegree
  let scalarComparison : (twist (homogeneousSubmodule coordinates baseField) twistDegree).H
      cohomologyDegree ≃ₗ[baseField]
        (ModuleCat.restrictScalars scalarMap).obj (cechComplex.homology cohomologyDegree) :=
    { lerayComparison.symm.toAddEquiv with
      map_smul' := fun scalar cohomologyClass ↦
        lerayComparison.symm.map_smul (scalarMap scalar) cohomologyClass }
  have monomialComparison := cechComplexTwistHomologyIso.{baseUniverse, coordinateUniverse}
    coordinates baseField twistDegree cohomologyDegree
  have restrictionComparison :=
    (ModuleCat.restrictScalarsHomologyIso scalarMap cechComplex cohomologyDegree).symm
  dsimp only [scalarMap, cechComplex] at scalarComparison restrictionComparison
  exact ⟨scalarComparison ≪≫ₗ (restrictionComparison ≪≫ monomialComparison).toLinearEquiv⟩

/-- Degree-zero twist cohomology is the homogeneous polynomial module. -/
theorem nonempty_H_zero_twist_equiv [Finite coordinates]
    (dimension : ℕ) (coordinateCount : Nat.card coordinates = dimension + 1)
    (twistDegree : ℕ) :
    letI := moduleHOfSpec (projectiveSpaceOverAffineToSpec coordinates baseField)
      (twist (homogeneousSubmodule coordinates baseField) twistDegree) 0
    Nonempty ((twist (homogeneousSubmodule coordinates baseField) twistDegree).H 0 ≃ₗ[baseField]
      homogeneousSubmodule coordinates baseField twistDegree) := by
  letI := moduleHOfSpec (projectiveSpaceOverAffineToSpec coordinates baseField)
    (twist (homogeneousSubmodule coordinates baseField) twistDegree) 0
  letI : Fintype coordinates := Fintype.ofFinite coordinates
  haveI : Nonempty coordinates := (Nat.card_pos_iff.1 (by omega)).1
  obtain ⟨comparison⟩ := nonempty_H_twist_linearEquiv_homology coordinates baseField twistDegree 0
  exact ⟨comparison ≪≫ₗ ProjectiveSpace.monomialCechComplexHomologyZeroLinearEquiv
    coordinates baseField twistDegree⟩

/-- Top-degree twist cohomology is the coefficient dual of homogeneous polynomials. -/
theorem nonempty_H_twist_top_equiv_dual [Finite coordinates]
    (dimension : ℕ) (coordinateCount : Nat.card coordinates = dimension + 1)
    (twistDegree : ℤ) (twistBound : twistDegree ≤ -(dimension : ℤ) - 1) :
    letI := moduleHOfSpec (projectiveSpaceOverAffineToSpec coordinates baseField)
      (twist (homogeneousSubmodule coordinates baseField) twistDegree) dimension
    Nonempty ((twist (homogeneousSubmodule coordinates baseField) twistDegree).H dimension ≃ₗ[baseField]
      Module.Dual baseField
        (homogeneousSubmodule coordinates baseField (-twistDegree - dimension - 1).toNat)) := by
  letI := moduleHOfSpec (projectiveSpaceOverAffineToSpec coordinates baseField)
    (twist (homogeneousSubmodule coordinates baseField) twistDegree) dimension
  letI : Fintype coordinates := Fintype.ofFinite coordinates
  obtain ⟨comparison⟩ := nonempty_H_twist_linearEquiv_homology coordinates baseField twistDegree
    dimension
  exact ⟨comparison ≪≫ₗ ProjectiveSpace.monomialCechComplexHomologyTopLinearEquivDual
    coordinates baseField twistDegree (by rwa [← Nat.card_eq_fintype_card]) twistBound⟩

end AlgebraicGeometry.Proj
