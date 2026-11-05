import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Relevant

/-!
# Homogeneous prime avoidance for finite sets

A finite set of points of a projective spectrum lies in a single basic open
defined by a homogeneous element of positive degree.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {coefficients gradedPiece : Type*} [CommRing coefficients]
  [SetLike gradedPiece coefficients] [AddSubgroupClass gradedPiece coefficients]
  {grading : ℕ → gradedPiece} [GradedRing grading]

namespace ProjectiveSpectrum

/-- A finite set of relevant homogeneous primes misses a common homogeneous element
of positive degree. -/
theorem exists_homogeneous_notMem_of_finset (points : Finset (ProjectiveSpectrum grading)) :
    ∃ degree > 0, ∃ homogeneousElement ∈ grading degree,
      ∀ point ∈ points, homogeneousElement ∉ point.asHomogeneousIdeal := by
  classical
  induction points using Finset.strongInduction with
  | H points inductionHypothesis =>
    rcases points.eq_empty_or_nonempty with rfl | nonemptyPoints
    · exact ⟨1, one_pos, 0, zero_mem _, by simp⟩
    obtain ⟨minimalPoint, minimality⟩ := points.exists_minimal nonemptyPoints
    obtain ⟨degree, positiveDegree, homogeneousElement, homogeneous, avoidsOthers⟩ :=
      inductionHypothesis (points.erase minimalPoint)
        (Finset.erase_ssubset minimality.prop)
    by_cases outsideMinimal : homogeneousElement ∉ minimalPoint.asHomogeneousIdeal
    · refine ⟨degree, positiveDegree, homogeneousElement, homogeneous, fun point membership ↦ ?_⟩
      by_cases equality : point = minimalPoint
      · exact equality ▸ outsideMinimal
      · exact avoidsOthers point (Finset.mem_erase.mpr ⟨equality, membership⟩)
    rw [not_not] at outsideMinimal
    have separatingSection (point : points.erase minimalPoint) :
        ∃ degree, ∃ homogeneousElement ∈ grading degree,
          homogeneousElement ∈ point.1.asHomogeneousIdeal ∧
            homogeneousElement ∉ minimalPoint.asHomogeneousIdeal := by
      have notBelow : ¬ point.1.asHomogeneousIdeal ≤ minimalPoint.asHomogeneousIdeal :=
        fun inclusion ↦ (Finset.mem_erase.mp point.2).1
          (le_antisymm inclusion (minimality.2 (Finset.mem_erase.mp point.2).2 inclusion))
      obtain ⟨element, inPrime, outsidePrime⟩ := SetLike.not_le_iff_exists.mp notBelow
      by_contra! contradiction
      refine outsidePrime ?_
      rw [← DirectSum.sum_support_decompose grading element]
      exact minimalPoint.1.toIdeal.sum_mem fun degree _ ↦
        contradiction degree _ (SetLike.coe_mem _)
          (point.1.asHomogeneousIdeal.2 degree inPrime)
    choose separatingDegree separatingElement separatingHomogeneous inOtherPrime
      outsideMinimalPrime using separatingSection
    obtain ⟨initialDegree, positiveInitialDegree, initialElement, initialHomogeneous,
      initialOutside⟩ := minimalPoint.exists_homogeneous_notMem
    let totalDegree := initialDegree +
      ∑ point ∈ (points.erase minimalPoint).attach, separatingDegree point
    let productSection := initialElement *
      ∏ point ∈ (points.erase minimalPoint).attach, separatingElement point
    have productHomogeneous : productSection ∈ grading totalDegree :=
      SetLike.mul_mem_graded initialHomogeneous
        (SetLike.prod_mem_graded _ _ _ (fun point _ ↦ separatingHomogeneous point))
    have productOutside : productSection ∉ minimalPoint.asHomogeneousIdeal := by
      refine minimalPoint.isPrime.mul_notMem initialOutside ?_
      rw [Ideal.IsPrime.prod_mem_iff (hp := minimalPoint.isPrime)]
      push Not
      exact fun point _ ↦ outsideMinimalPrime point
    have productInOther (point : points.erase minimalPoint) :
        productSection ∈ point.1.asHomogeneousIdeal :=
      Ideal.mul_mem_left _ _ (Ideal.mem_of_dvd _
        (Finset.dvd_prod_of_mem _ (Finset.mem_attach _ point)) (inOtherPrime point))
    have positiveTotalDegree : 0 < totalDegree :=
      lt_of_lt_of_le positiveInitialDegree (Nat.le_add_right _ _)
    refine ⟨degree * totalDegree, Nat.mul_pos positiveDegree positiveTotalDegree,
      homogeneousElement ^ totalDegree + productSection ^ degree, add_mem ?_ ?_,
      fun point membership ↦ ?_⟩
    · simpa [mul_comm] using SetLike.pow_mem_graded totalDegree homogeneous
    · simpa using SetLike.pow_mem_graded degree productHomogeneous
    · by_cases equality : point = minimalPoint
      · subst equality
        intro inPrime
        exact productOutside (point.isPrime.mem_of_pow_mem degree
          ((Ideal.add_mem_iff_right _
            (Ideal.pow_mem_of_mem _ outsideMinimal totalDegree positiveTotalDegree)).mp inPrime))
      · have inErased : point ∈ points.erase minimalPoint :=
          Finset.mem_erase.mpr ⟨equality, membership⟩
        intro inPrime
        exact avoidsOthers point inErased (point.isPrime.mem_of_pow_mem totalDegree
          ((Ideal.add_mem_iff_left _
            (Ideal.pow_mem_of_mem _ (productInOther ⟨point, inErased⟩)
              degree positiveDegree)).mp inPrime))

end ProjectiveSpectrum
