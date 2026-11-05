import Jacobian.RingTheory.GradedAlgebra.HomogeneousLocalization.Away

/-!
# Transition functions between homogeneous affine charts

The ratios on two charts satisfy the multiplicative transition identity on
their overlap.
-/

namespace HomogeneousLocalization

variable {degreeType gradedPieceType gradedRing : Type*} [CommRing gradedRing]
    [SetLike gradedPieceType gradedRing] [AddSubgroupClass gradedPieceType gradedRing]
    [AddCommMonoid degreeType] [DecidableEq degreeType]
    (grading : degreeType → gradedPieceType) [GradedRing grading]
    {degree : degreeType} {firstDenominator secondDenominator numerator : gradedRing}

private lemma Away.mk_mul (denominator_homogeneous : firstDenominator ∈ grading degree)
    (firstPower secondPower : ℕ) (firstNumerator secondNumerator : gradedRing)
    (first_homogeneous : firstNumerator ∈ grading (firstPower • degree))
    (second_homogeneous : secondNumerator ∈ grading (secondPower • degree)) :
    Away.mk grading denominator_homogeneous firstPower firstNumerator first_homogeneous *
        Away.mk grading denominator_homogeneous secondPower secondNumerator second_homogeneous =
      Away.mk grading denominator_homogeneous (firstPower + secondPower)
        (firstNumerator * secondNumerator)
        (add_smul firstPower secondPower degree ▸
          SetLike.mul_mem_graded first_homogeneous second_homogeneous) := by
  apply val_injective
  rw [val_mul, Away.val_mk, Away.val_mk, Away.val_mk, Localization.mk_mul]
  congr 1
  exact Subtype.ext (pow_add firstDenominator firstPower secondPower).symm

/-- Homogeneous ratios satisfy the multiplicative transition identity on an overlap. -/
lemma awayMap_mk_one_eq_mul (first_homogeneous : firstDenominator ∈ grading degree) (second_homogeneous : secondDenominator ∈ grading degree) (numerator_homogeneous : numerator ∈ grading (1 • degree)) :
    awayMap grading first_homogeneous (mul_comm firstDenominator secondDenominator) (Away.mk grading second_homogeneous 1 numerator numerator_homogeneous) =
      awayMap grading second_homogeneous (rfl : firstDenominator * secondDenominator = firstDenominator * secondDenominator) (Away.mk grading first_homogeneous 1 numerator numerator_homogeneous) *
        awayMap grading first_homogeneous (mul_comm firstDenominator secondDenominator) (Away.mk grading second_homogeneous 1 firstDenominator (by simpa using first_homogeneous)) := by
  rw [awayMap_mk, awayMap_mk, awayMap_mk, Away.mk_mul]
  refine Away.mk_eq_mk_of_mul_pow_eq grading _ _ _ ?_
  ring


end HomogeneousLocalization
