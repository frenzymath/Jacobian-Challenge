import Jacobian.AlgebraicGeometry.Cohomology.Affine.Vanishing
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Basic

/-!
# Cohomological dimension of projective space

Projective space with `d + 1` homogeneous coordinates has a cover by that many
affine standard opens. The finite affine-cover vanishing theorem gives vanishing
of native sheaf cohomology in every degree greater than `d`, for arbitrary
quasi-coherent coefficients and without a noetherian hypothesis.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (coordinates : Type v) (coefficients : Type (max u v)) [CommRing coefficients]

set_option maxHeartbeats 800000 in
/-- Quasi-coherent cohomology of projective `d`-space vanishes above degree `d`. -/
theorem subsingleton_H_projectiveSpaceOverAffine_of_lt [Finite coordinates] {dimension : ℕ}
    (coordinateCount : Nat.card coordinates = dimension + 1)
    (moduleSheaf : (projectiveSpaceOverAffine coordinates coefficients).Modules)
    [SheafOfModules.IsQuasicoherent
      (R := (projectiveSpaceOverAffine coordinates coefficients).ringCatSheaf) moduleSheaf]
    {degree : ℕ} (degreeBound : dimension < degree) :
    Subsingleton (moduleSheaf.H degree) := by
  classical
  let abelianSheaf : CategoryTheory.Sheaf
      (_root_.Opens.grothendieckTopology
        (projectiveSpaceOverAffine coordinates coefficients)) AddCommGrpCat.{max u v} :=
    (SheafOfModules.toSheaf.{max u v}
      (projectiveSpaceOverAffine coordinates coefficients).ringCatSheaf).obj moduleSheaf
  change Subsingleton (CategoryTheory.Sheaf.H abelianSheaf degree)
  letI : Fintype coordinates := Fintype.ofFinite coordinates
  letI : Scheme.IsSeparated (projectiveSpaceOverAffine coordinates coefficients) :=
    inferInstanceAs (Scheme.IsSeparated
      (Proj (MvPolynomial.homogeneousSubmodule coordinates coefficients)))
  let standardCover : coordinates → (projectiveSpaceOverAffine coordinates coefficients).Opens :=
    fun index ↦ Proj.basicOpen (MvPolynomial.homogeneousSubmodule coordinates coefficients)
      (MvPolynomial.X index)
  have coverCardinality : (Finset.univ : Finset coordinates).card = dimension + 1 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, coordinateCount]
  have coverNonempty : (Finset.univ : Finset coordinates).Nonempty := by
    apply Finset.card_pos.mp
    rw [coverCardinality]
    exact Nat.succ_pos dimension
  have coverAffine : ∀ index, IsAffineOpen (standardCover index) := fun index ↦
    Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule coordinates coefficients)
      (MvPolynomial.X index) (MvPolynomial.isHomogeneous_X coefficients index) one_pos
  have covers : Finset.univ.sup standardCover = ⊤ := by
    rw [Finset.sup_univ_eq_iSup]
    exact Proj.iSup_basicOpen_eq_top'
      (MvPolynomial.homogeneousSubmodule coordinates coefficients)
      (MvPolynomial.X : coordinates → MvPolynomial coordinates coefficients)
      (fun index ↦ ⟨1, MvPolynomial.isHomogeneous_X coefficients index⟩)
      (MvPolynomial.adjoin_range_X_eq_top coordinates coefficients)
  exact Scheme.Modules.subsingleton_H_of_card_le
    (scheme := projectiveSpaceOverAffine coordinates coefficients) Finset.univ
    coverNonempty standardCover (fun index _ ↦ coverAffine index) covers abelianSheaf
    (Scheme.Modules.cechAcyclicOnAffines_of_isQuasicoherent moduleSheaf)
    (by rw [coverCardinality]; exact degreeBound)

end AlgebraicGeometry.Proj
