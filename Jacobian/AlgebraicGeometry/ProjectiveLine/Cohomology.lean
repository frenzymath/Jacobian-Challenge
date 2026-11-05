import Jacobian.Algebra.Homology.CochainComplex.RestrictScalars
import Jacobian.AlgebraicGeometry.Cohomology.Affine.Leray
import Jacobian.AlgebraicGeometry.Cohomology.Finiteness
import Jacobian.AlgebraicGeometry.Cohomology.ProjectiveTwist
import Jacobian.AlgebraicGeometry.Curve.Genus
import Jacobian.AlgebraicGeometry.ProjectiveLine.Geometry
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Cech

/-!
# Structure-sheaf cohomology of the projective line

The structure sheaf is the zeroth twisting sheaf on polynomial projective space.
The monomial Čech calculation makes its first cohomology zero, and the two-chart
cohomological dimension bound gives vanishing in higher degrees. In particular,
the projective line has arithmetic genus zero over every field.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

variable (baseField : Type u) [Field baseField]

private theorem subsingleton_H_twist_zero_one :
    Subsingleton ((Proj.twist
      (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) 0).H 1) := by
  let moduleSheaf := Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) 0
  letI : moduleSheaf.IsQuasicoherent :=
    SheafOfModules.IsInvertible.isQuasicoherent.{u, u, u}
      (Proj.isInvertible_twist_homogeneousSubmodule (Fin 2) baseField 0)
  let cechComplex := (cechComplexFunctor (Proj.standardOpen (Fin 2) baseField)).obj
    moduleSheaf.presheafModuleCat
  let scalarMap := ((Scheme.ΓSpecIso (.of baseField)).inv ≫
    (Proj.projectiveSpaceOverAffineToSpec (Fin 2) baseField).appTop).hom
  letI : Subsingleton ((ProjectiveSpace.monomialCechComplex (Fin 2) baseField 0).homology 1) :=
    ProjectiveSpace.subsingleton_monomialCechComplex_homology_top
      (by decide) (by decide) (by decide)
  letI : Subsingleton
      ((((ModuleCat.restrictScalars scalarMap).mapHomologicalComplex _).obj
        cechComplex).homology 1) :=
    (Proj.cechComplexTwistHomologyIso.{u, 0} (Fin 2) baseField 0 1).toLinearEquiv.toEquiv.subsingleton
  letI : Subsingleton (cechComplex.homology 1) :=
    (ModuleCat.restrictScalarsHomologyIso scalarMap cechComplex 1).symm.toLinearEquiv.toEquiv.subsingleton
  obtain ⟨comparison⟩ := nonempty_cechComplex_linearEquiv_H_of_isSeparated.{u, 0}
    (Proj.projectiveSpaceOverAffineToSpec (Fin 2) baseField)
    (Proj.standardOpen (Fin 2) baseField)
    (fun index ↦ Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X baseField index)
      one_pos)
    (Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
      (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) baseField)
      (fun index ↦ ⟨1, MvPolynomial.isHomogeneous_X baseField index⟩)
      (MvPolynomial.adjoin_range_X_eq_top (Fin 2) baseField)) moduleSheaf 1
  exact comparison.symm.toEquiv.subsingleton

/-- All positive cohomology groups of the projective-line structure sheaf vanish. -/
theorem subsingleton_H_unit (degree : ℕ) (positiveDegree : 0 < degree) :
    Subsingleton (Scheme.Modules.H (X := projectiveLine baseField)
      (SheafOfModules.unit (projectiveLine baseField).ringCatSheaf) degree) := by
  rcases Nat.eq_or_lt_of_le positiveDegree with rfl | higherDegree
  · letI := subsingleton_H_twist_zero_one baseField
    exact (H.mapLinearEquiv
      (Proj.unitIsoTwistZero
        (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) baseField)) 1).toEquiv.subsingleton
  · letI : (SheafOfModules.unit (projectiveLine baseField).ringCatSheaf).IsQuasicoherent :=
      SheafOfModules.IsInvertible.isQuasicoherent.{u, u, u}
        (Scheme.Modules.isInvertible_unit (projectiveLine baseField))
    exact Proj.subsingleton_H_projectiveSpaceOverAffine_of_lt.{u, 0} (Fin 2) baseField
      (Nat.card_fin 2) (SheafOfModules.unit (projectiveLine baseField).ringCatSheaf) higherDegree

/-- The projective line has arithmetic genus zero. -/
@[simp]
theorem arithmeticGenus_eq_zero : (projectiveLine baseField).arithmeticGenus baseField = 0 := by
  letI := subsingleton_H_unit baseField 1 (by decide)
  exact Module.finrank_zero_of_subsingleton

end AlgebraicGeometry.ProjectiveLine
