import Jacobian.AlgebraicGeometry.Modules.ZeroLocus
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.Tensor
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist

/-!
# Zero loci of homogeneous sections of the degree-one twist

The nonvanishing locus of the section defined by a homogeneous element of degree
one is its standard open, when the degree-one standard opens cover Proj.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory MonoidalCategory HomogeneousLocalization

namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist

variable {gradedRing gradedPieceType : Type u} [CommRing gradedRing] [SetLike gradedPieceType gradedRing] [AddSubgroupClass gradedPieceType gradedRing] {grading : ℕ → gradedPieceType}
  [GradedRing grading]

/-- **The non-vanishing locus of a section of degree one.** If the basic opens `D₊(g)` of the
elements `g` of degree `1` cover `Proj 𝒜`, then for `f` of degree `1` the zero scheme of the
section `f` of `𝒪(1)` is the complement of `D₊(f)`: on `D₊(g)` the section `g` is a free
generator of `𝒪(1)`, and `f = (f / g) • g`, which vanishes exactly where `f` does. -/
theorem compl_support_zeroLocus_unitToTwist
    (compatibility : ∀ point : Proj grading, ∃ otherMorphism ∈ grading 1, point ∈ Proj.basicOpen grading otherMorphism) {homogeneousElement : gradedRing} (hf : homogeneousElement ∈ grading 1) :
    letI : SheafOfModules.IsInvertible.{u, u, u} (twist grading (0 + (1 : ℕ))) :=
      isInvertible_twist grading _ compatibility
    (Scheme.Modules.Hom.zeroLocus (unitToTwist hf)).support.compl = Proj.basicOpen grading homogeneousElement := by
  letI : SheafOfModules.IsInvertible.{u, u, u} (twist grading (0 + (1 : ℕ))) :=
    isInvertible_twist grading _ compatibility
  ext point
  obtain ⟨otherMorphism, hg, hxg⟩ := compatibility point
  let openSubset : (Proj grading).affineOpens := ⟨_, isAffineOpen_basicOpen grading otherMorphism hg one_pos⟩
  obtain ⟨secondElement, hb⟩ := (isFreeGenerator_unitToTwist hg).exists_smul_eq
    ((unitToTwist hf).app openSubset.1 (1 : Γ(Proj grading, openSubset.1)))
  have : point.asHomogeneousIdeal.toIdeal.IsPrime := point.isPrime
  have hval : (secondElement.1 ⟨point, hxg⟩).val * ((1 : AtPrime grading point.asHomogeneousIdeal.toIdeal).val *
      Localization.mk otherMorphism 1) = (1 : AtPrime grading point.asHomogeneousIdeal.toIdeal).val *
        Localization.mk homogeneousElement 1 :=
    congr((($hb).1 ⟨point, hxg⟩).1)
  rw [HomogeneousLocalization.val_one, one_mul, one_mul] at hval
  have hunit (firstElement : gradedRing) : IsUnit (Localization.mk firstElement 1 : Localization.AtPrime
      point.asHomogeneousIdeal.toIdeal) ↔ firstElement ∉ point.asHomogeneousIdeal := by
    rw [Localization.mk_one_eq_algebraMap]
    exact IsLocalization.AtPrime.isUnit_to_map_iff _ _ firstElement
  have key : point ∈ (Proj grading).basicOpen secondElement ↔ point ∈ Proj.basicOpen grading homogeneousElement := by
    rw [mem_basicOpen_iff_isUnit_val secondElement hxg, Proj.mem_basicOpen, ← hunit, ← hval,
      IsUnit.mul_iff, and_iff_left ((hunit otherMorphism).mpr hxg)]
  have hsupp : point ∈ (Scheme.Modules.Hom.zeroLocus (unitToTwist hf)).support ↔
      point ∉ (Proj grading).basicOpen secondElement := by
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := openSubset) hxg,
      Scheme.Modules.Hom.ideal_zeroLocus _ openSubset (Scheme.Modules.isFreeGenerator_one _)
        (isFreeGenerator_unitToTwist hg) hb.symm, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton]
    rfl
  exact (not_congr hsupp).trans (not_not.trans key)

end AlgebraicGeometry.Proj
