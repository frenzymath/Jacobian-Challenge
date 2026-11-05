import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeModelBaseChange
import Jacobian.AlgebraicGeometry.Cohomology.PerfectLocus
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Local constancy of the fibre Euler characteristic

For a proper locally finitely presented family with finitely presented,
relatively flat coefficients, the Euler characteristic of the residue-field
fibres is locally constant. On a neighborhood carrying a universal finite
free cohomology model, it is the alternating sum of the ranks of that model.
No Noetherian hypothesis on the base is needed.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

private theorem alternating_sum_adjacent_eq_endpoints (values : ℤ → ℤ) (bound : ℕ) :
    ∑ degree ∈ Finset.range (bound + 1),
      (-1) ^ degree * (values degree + values ((degree : ℤ) - 1)) =
        (-1) ^ bound * values bound + values (-1) := by
  induction bound with
  | zero => simp
  | succ bound inductionHypothesis =>
    rw [Finset.sum_range_succ, inductionHypothesis, pow_succ]
    push_cast
    ring_nf

/-- The fibre Euler characteristic of finitely presented relatively flat
coefficients in a proper finitely presented family is locally constant. -/
theorem isLocallyConstant_eulerCharFiber
    {sourceScheme baseScheme : Scheme.{schemeUniverse}}
    (sourceMap : sourceScheme ⟶ baseScheme)
    [IsProper sourceMap] [LocallyOfFinitePresentation sourceMap]
    (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsFinitePresentation]
    (flat : moduleSheaf.IsFlatOver sourceMap) :
    IsLocallyConstant (moduleSheaf.eulerCharFiber sourceMap) := by
  classical
  rw [IsLocallyConstant.iff_eventually_eq]
  intro point
  obtain ⟨openSubset, complex, bound, membership, finiteFree, baseChangeComparison⟩ :=
    exists_isFiniteFreeComplex_higherDirectImage sourceMap moduleSheaf flat point
  choose termRanks termTrivializations using finiteFree.exists_iso_free
  let trivialization degree := (termTrivializations degree).some
  suffices constant : ∀ fibrePoint ∈ openSubset,
      moduleSheaf.eulerCharFiber sourceMap fibrePoint =
        ∑ degree ∈ Finset.range (bound + 1), (-1) ^ degree * (termRanks degree : ℤ) by
    filter_upwards [openSubset.isOpen.mem_nhds membership] with fibrePoint fibreMembership
    rw [constant fibrePoint fibreMembership, constant point membership]
  intro fibrePoint fibreMembership
  let residueMap := baseScheme.fromSpecResidueField fibrePoint
  have residueRange : Set.range residueMap ⊆ Set.range openSubset.ι := by
    rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]
    exact Set.singleton_subset_iff.mpr fibreMembership
  let fibreMap := IsOpenImmersion.lift openSubset.ι residueMap residueRange
  have fibreFactorization : fibreMap ≫ openSubset.ι = residueMap :=
    IsOpenImmersion.lift_fac _ _ _
  have fibreDimensions := hFiber_eq_finrank_homology sourceMap moduleSheaf
    baseChangeComparison fibreMap fibreFactorization
  have residueField : IsField (baseScheme.residueField fibrePoint) := Field.toIsField _
  have dimensionEquation :=
    finrank_homology_pullback_add_rank_add_rank trivialization residueField fibreMap
  let differentialRank : ℤ → ℕ := fun degree ↦
    ((freeMatrix ((trivialization degree).inv ≫ complex.d degree (degree + 1) ≫
      (trivialization (degree + 1)).hom)).map fibreMap.appTop).rank
  have differentialRank_eq (sourceDegree targetDegree : ℤ)
      (degreeCondition : sourceDegree + 1 = targetDegree) :
      differentialRank sourceDegree =
        ((freeMatrix ((trivialization sourceDegree).inv ≫ complex.d sourceDegree targetDegree ≫
          (trivialization targetDegree).hom)).map fibreMap.appTop).rank := by
    subst targetDegree
    rfl
  have rankEquation (degree : ℕ) :
      (moduleSheaf.hFiber sourceMap degree fibrePoint : ℤ) =
        (termRanks degree : ℤ) - (differentialRank degree : ℤ) -
          (differentialRank ((degree : ℤ) - 1) : ℤ) := by
    have equation := dimensionEquation degree
    rw [← differentialRank_eq ((degree : ℤ) - 1) degree (by omega)] at equation
    change _ + differentialRank degree + _ = _ at equation
    rw [fibreDimensions degree]
    omega
  have differentialRank_zero (degree : ℤ)
      (zeroTerm : IsZero (complex.X degree) ∨ IsZero (complex.X (degree + 1))) :
      differentialRank degree = 0 := by
    have zeroDifferential : complex.d degree (degree + 1) = 0 :=
      zeroTerm.elim (fun zeroSource ↦ zeroSource.eq_of_src _ _)
        (fun zeroTarget ↦ zeroTarget.eq_of_tgt _ _)
    simp [differentialRank, zeroDifferential, freeMatrix_zero]
  haveI := finiteFree.isStrictlyGE
  haveI := finiteFree.isStrictlyLE
  have firstRank : differentialRank (-1) = 0 :=
    differentialRank_zero _ (.inl (CochainComplex.isZero_of_isStrictlyGE
      complex 0 (-1) (by omega)))
  have lastRank : differentialRank bound = 0 :=
    differentialRank_zero _ (.inr (CochainComplex.isZero_of_isStrictlyLE
      complex bound (bound + 1) (by omega)))
  have vanishing (degree : ℕ) (aboveBound : bound < degree) :
      moduleSheaf.hFiber sourceMap degree fibrePoint = 0 := by
    rw [fibreDimensions degree]
    let pulledComplex :
        CochainComplex (Spec (baseScheme.residueField fibrePoint)).Modules ℤ :=
      ((pullback fibreMap).mapHomologicalComplex (.up ℤ)).obj complex
    have zeroTerm : IsZero (pulledComplex.X degree) :=
      (pullback fibreMap).map_isZero
        (CochainComplex.isZero_of_isStrictlyLE complex bound degree (by omega))
    have zeroHomology : IsZero (pulledComplex.homology degree) :=
      ShortComplex.isZero_homology_of_isZero_X₂ _ zeroTerm
    have := ModuleCat.subsingleton_of_isZero
      ((moduleSpecΓFunctor (R := baseScheme.residueField fibrePoint)).map_isZero zeroHomology)
    exact Module.finrank_zero_of_subsingleton
  rw [eulerCharFiber, finsum_eq_sum_of_support_subset (s := Finset.range (bound + 1))]
  · have telescope := alternating_sum_adjacent_eq_endpoints
      (fun degree ↦ (differentialRank degree : ℤ)) bound
    simp only [firstRank, lastRank, Nat.cast_zero, mul_zero, zero_add] at telescope
    rw [← sub_zero (∑ degree ∈ Finset.range (bound + 1),
      (-1) ^ degree * (termRanks degree : ℤ)), ← telescope, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun degree _ ↦ ?_
    rw [rankEquation]
    ring
  · intro degree supported
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at supported
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra outside
    exact supported.2 (by rw [vanishing degree (by omega)]; simp)

end AlgebraicGeometry.Scheme.Modules
