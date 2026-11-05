import Jacobian.Algebra.Homology.CochainComplex.RestrictScalars
import Jacobian.AlgebraicGeometry.Cohomology.Affine.Leray
import Jacobian.AlgebraicGeometry.Cohomology.Finiteness
import Jacobian.AlgebraicGeometry.Cohomology.ProjectiveTwist
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Cech

/-!
# Finite generation of twisting-sheaf cohomology

The actual sheaf cohomology of a twisting sheaf on polynomial projective space
is the homology of its monomial Čech complex, as a module over the coefficient
ring. The monomial computation and the cohomological-dimension bound imply
finite generation in every degree, without a noetherian hypothesis.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Proj

open Scheme.Modules MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (coordinates : Type v) (coefficients : Type (max u v)) [CommRing coefficients]

private def projectiveScalarMap
    (coordinates : Type v) (coefficients : Type (max u v)) [CommRing coefficients] :
    coefficients →+* Γ((projectiveSpaceOverAffine coordinates coefficients), ⊤) :=
  ((Scheme.ΓSpecIso (.of coefficients)).inv ≫
    (projectiveSpaceOverAffineToSpec coordinates coefficients).appTop).hom

private theorem finite_compHom_of_linearEquiv
    {baseRing extensionRing source target : Type*} [Semiring baseRing] [Semiring extensionRing]
    [AddCommMonoid source] [AddCommMonoid target]
    [Module extensionRing source] [Module extensionRing target]
    (scalarMap : baseRing →+* extensionRing)
    (comparison : source ≃ₗ[extensionRing] target)
    (finiteTarget : letI := Module.compHom target scalarMap; Module.Finite baseRing target) :
    letI := Module.compHom source scalarMap
    Module.Finite baseRing source := by
  letI := Module.compHom source scalarMap
  letI := Module.compHom target scalarMap
  letI : Module.Finite baseRing target := finiteTarget
  let restrictedComparison : source ≃ₗ[baseRing] target :=
    { comparison.toAddEquiv with
      map_smul' := fun baseScalar element ↦ comparison.map_smul (scalarMap baseScalar) element }
  exact Module.Finite.equiv restrictedComparison.symm

/-- Every cohomology module of a polynomial twisting sheaf is finitely generated. -/
theorem finite_H_twist [Finite coordinates] (twistDegree : ℤ) (degree : ℕ) :
    @Module.Finite coefficients
      ((twist (homogeneousSubmodule coordinates coefficients) twistDegree).H degree)
      _ _ (moduleHOfSpec (projectiveSpaceOverAffineToSpec coordinates coefficients)
        (twist (homogeneousSubmodule coordinates coefficients) twistDegree) degree) := by
  classical
  letI : Fintype coordinates := Fintype.ofFinite coordinates
  letI : Module coefficients
      ((twist (homogeneousSubmodule coordinates coefficients) twistDegree).H degree) :=
    moduleHOfSpec (projectiveSpaceOverAffineToSpec coordinates coefficients)
      (twist (homogeneousSubmodule coordinates coefficients) twistDegree) degree
  letI : SheafOfModules.IsQuasicoherent
      (R := (projectiveSpaceOverAffine coordinates coefficients).ringCatSheaf)
      (twist (homogeneousSubmodule coordinates coefficients) twistDegree) :=
    SheafOfModules.IsInvertible.isQuasicoherent.{max u v, max u v, max u v}
      (isInvertible_twist_homogeneousSubmodule coordinates coefficients twistDegree)
  rcases isEmpty_or_nonempty coordinates with emptyCoordinates | nonemptyCoordinates
  · letI : IsEmpty coordinates := emptyCoordinates
    haveI : IsEmpty (projectiveSpaceOverAffine coordinates coefficients) := ⟨fun point ↦ by
      have membership : point ∈ ⨆ index, standardOpen coordinates coefficients index := by
        rw [show (⨆ index, standardOpen coordinates coefficients index) = ⊤ from
          iSup_basicOpen_eq_top' (homogeneousSubmodule coordinates coefficients)
            (X : coordinates → MvPolynomial coordinates coefficients)
            (fun index ↦ ⟨1, isHomogeneous_X coefficients index⟩)
            (adjoin_range_X_eq_top coordinates coefficients)]
        trivial
      obtain ⟨index, _⟩ := Opens.mem_iSup.mp membership
      exact isEmptyElim index⟩
    haveI := subsingleton_H_of_isZero
      (Scheme.Modules.isZero_of_isEmpty
        (twist (homogeneousSubmodule coordinates coefficients) twistDegree)) degree
    infer_instance
  · have hcard : 0 < Fintype.card coordinates :=
      Fintype.card_pos_iff.mpr nonemptyCoordinates
    have coordinateCount : Fintype.card coordinates =
        (Fintype.card coordinates - 1) + 1 :=
      (Nat.sub_add_cancel hcard).symm
    let dimension := Fintype.card coordinates - 1
    by_cases degreeBound : degree ≤ dimension
    · let scalarMap := projectiveScalarMap coordinates coefficients
      let cechComplex := (cechComplexFunctor (standardOpen coordinates coefficients)).obj
        (twist (homogeneousSubmodule coordinates coefficients) twistDegree).presheafModuleCat
      obtain ⟨comparison⟩ := Scheme.Modules.nonempty_cechComplex_linearEquiv_H_of_isSeparated.{u, v}
        (projectiveSpaceOverAffineToSpec coordinates coefficients)
        (standardOpen coordinates coefficients)
        (fun index ↦ isAffineOpen_basicOpen _ _ (isHomogeneous_X coefficients index) one_pos)
        (iSup_basicOpen_eq_top' (homogeneousSubmodule coordinates coefficients)
          (X : coordinates → MvPolynomial coordinates coefficients)
          (fun index ↦ ⟨1, isHomogeneous_X coefficients index⟩)
          (adjoin_range_X_eq_top coordinates coefficients))
        (twist (homogeneousSubmodule coordinates coefficients) twistDegree) degree
      letI : Module coefficients (cechComplex.homology degree) :=
        Module.compHom (cechComplex.homology degree) scalarMap
      let monomialHomology :=
        (ProjectiveSpace.monomialCechComplex coordinates coefficients twistDegree).homology degree
      letI : Module coefficients monomialHomology := monomialHomology.isModule
      have restrictionIso :
          (((ModuleCat.restrictScalars scalarMap).mapHomologicalComplex _).obj cechComplex).homology
              degree ≅
            (ModuleCat.restrictScalars scalarMap).obj (cechComplex.homology degree) :=
        ModuleCat.restrictScalarsHomologyIso scalarMap cechComplex degree
      let homologyIso :=
        cechComplexTwistHomologyIso coordinates coefficients twistDegree degree
      have homologyComparison :
          cechComplex.homology degree ≃ₗ[coefficients] monomialHomology :=
        (restrictionIso.symm ≪≫ homologyIso).toLinearEquiv
      have finiteHomology :
          Module.Finite coefficients monomialHomology := by
        change Module.Finite coefficients
          ((ProjectiveSpace.monomialCechComplex coordinates coefficients
            twistDegree).homology degree)
        exact ProjectiveSpace.finite_monomialCechComplex_homology (n := coordinates)
          coefficients coordinateCount twistDegree degreeBound
      letI : Module.Finite coefficients monomialHomology :=
        finiteHomology
      have finiteCech : Module.Finite coefficients (cechComplex.homology degree) :=
        Module.Finite.equiv (R := coefficients)
          (M := monomialHomology)
          (N := cechComplex.homology degree) homologyComparison.symm
      exact finite_compHom_of_linearEquiv scalarMap comparison.symm finiteCech
    · haveI := subsingleton_H_twist_homogeneousSubmodule_of_lt coordinates coefficients
        (by simpa only [Nat.card_eq_fintype_card] using coordinateCount) twistDegree
        (by omega : dimension < degree)
      infer_instance

/-- Polynomial twisting sheaves have finite cohomology over the coefficient ring. -/
theorem hasFiniteH_twist [Finite coordinates] (twistDegree : ℤ) :
    HasFiniteH (projectiveSpaceOverAffineToSpec coordinates coefficients)
      (twist (homogeneousSubmodule coordinates coefficients) twistDegree) :=
  fun degree ↦ finite_H_twist.{u, v} coordinates coefficients twistDegree degree

end AlgebraicGeometry.Proj
