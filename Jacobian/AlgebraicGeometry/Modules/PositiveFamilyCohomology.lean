import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.RankLocus
import Jacobian.AlgebraicGeometry.Curve.CanonicalDegree

/-!
# Cohomology of positive line bundles in families of curves

For a proper smooth family of geometrically irreducible curves, a line bundle
whose fibre degrees exceed the canonical degrees has fibre cohomology only in
degree zero. Riemann--Roch computes its rank. When this rank is constant, the
arbitrary-base cohomology rank locus gives the same locally free direct image
and higher vanishing after every Cartesian base change.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {source base : Scheme.{u}} (family : source ⟶ base)
  [IsProper family] [SmoothOfRelativeDimension 1 family]
  [GeometricallyIrreducible family]

private def residueCurve (point : base) : Curve (base.residueField point) where
  carrier := Over.mk (family.fiberToSpecResidueField point)
  isProper := by
    change IsProper (pullback.snd family (base.fromSpecResidueField point))
    exact MorphismProperty.pullback_snd _ _ (inferInstanceAs (IsProper family))
  smoothOfRelativeDimension := by
    letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
    change SmoothOfRelativeDimension 1 (pullback.snd family (base.fromSpecResidueField point))
    exact MorphismProperty.pullback_snd _ _ (inferInstanceAs (SmoothOfRelativeDimension 1 family))
  geometricallyIrreducible := by
    change GeometricallyIrreducible (pullback.snd family (base.fromSpecResidueField point))
    exact MorphismProperty.pullback_snd _ _ (inferInstanceAs (GeometricallyIrreducible family))

variable (lineBundle : source.Modules) [lineBundle.IsInvertible]

/-- Above canonical degree, the fibre cohomology vanishes in every positive
degree, not only in degree one. -/
theorem mem_perfectLocus_of_fibre_degree_gt_canonical (point : base)
    (degreeBound :
      letI := family.fiberOverSpecResidueField point
      2 * ((family.fiber point).arithmeticGenus (base.residueField point) : ℤ) - 2 <
        ((pullback (family.fiberι point)).obj lineBundle).degree (base.residueField point)) :
    point ∈ lineBundle.perfectLocus family 0 := by
  letI := family.fiberOverSpecResidueField point
  let curve := residueCurve family point
  let fibreLine := (pullback (family.fiberι point)).obj lineBundle
  letI : IsProper (family.fiber point ↘ Spec (.of (base.residueField point))) :=
    curve.isProper
  letI : SmoothOfRelativeDimension 1
      (family.fiber point ↘ Spec (.of (base.residueField point))) :=
    curve.smoothOfRelativeDimension
  letI : GeometricallyIrreducible
      (family.fiber point ↘ Spec (.of (base.residueField point))) :=
    curve.geometricallyIrreducible
  intro degree positive
  change fibreLine.finrankH (base.residueField point) degree = 0
  by_cases degreeOne : degree = 1
  · subst degree
    exact finrankH_one_eq_zero_of_degree_gt_canonical fibreLine degreeBound
  · have : Subsingleton (fibreLine.H degree) :=
      curve.subsingleton_H fibreLine (by omega)
    exact Module.finrank_zero_of_subsingleton

/-- Riemann--Roch computes the dimension of the sections on the actual residue
fibre using the same module and scalar action as the direct-image rank locus. -/
theorem hFiber_zero_eq_degree_add_one_sub_genus (point : base)
    (degreeBound :
      letI := family.fiberOverSpecResidueField point
      2 * ((family.fiber point).arithmeticGenus (base.residueField point) : ℤ) - 2 <
        ((pullback (family.fiberι point)).obj lineBundle).degree (base.residueField point)) :
    letI := family.fiberOverSpecResidueField point
    (lineBundle.hFiber family 0 point : ℤ) =
      ((pullback (family.fiberι point)).obj lineBundle).degree (base.residueField point) + 1 -
        ((family.fiber point).arithmeticGenus (base.residueField point) : ℤ) := by
  letI := family.fiberOverSpecResidueField point
  let curve := residueCurve family point
  letI : IsProper (family.fiber point ↘ Spec (.of (base.residueField point))) :=
    curve.isProper
  letI : SmoothOfRelativeDimension 1
      (family.fiber point ↘ Spec (.of (base.residueField point))) :=
    curve.smoothOfRelativeDimension
  letI : GeometricallyIrreducible
      (family.fiber point ↘ Spec (.of (base.residueField point))) :=
    curve.geometricallyIrreducible
  exact finrankH_zero_eq_degree_add_one_sub_genus
    ((pullback (family.fiberι point)).obj lineBundle) degreeBound

/-- Constant positive fibre cohomology gives universal locally free direct
images over arbitrary bases. The hypotheses are numerical facts on the actual
fibres, rather than a supplied direct-image or base-change certificate. -/
theorem isFiniteLocallyFreeInDegree_of_positive_fibres (rank : ℕ)
    (degreeBound : ∀ point : base,
      letI := family.fiberOverSpecResidueField point
      2 * ((family.fiber point).arithmeticGenus (base.residueField point) : ℤ) - 2 <
        ((pullback (family.fiberι point)).obj lineBundle).degree (base.residueField point))
    (dimension : ∀ point : base, lineBundle.hFiber family 0 point = rank)
    {changedBase changedSource : Scheme.{u}}
    (baseChange : changedBase ⟶ base) (sourceChange : changedSource ⟶ source)
    (changedFamily : changedSource ⟶ changedBase)
    [HasInjectiveResolutions changedSource.Modules]
    (square : IsPullback sourceChange changedFamily family baseChange) :
    IsFiniteLocallyFreeInDegree (fun degree ↦ (higherDirectImage changedFamily degree).obj
      ((pullback sourceChange).obj lineBundle)) 0 rank := by
  letI : Smooth family := SmoothOfRelativeDimension.smooth 1 family
  obtain ⟨rankOpen, rankOpen_eq, universal⟩ :=
    exists_opens_range_subset_iff_isFiniteLocallyFreeInDegree family lineBundle
      (isFlatOver_of_isInvertible family lineBundle) 0 rank
  apply (universal baseChange sourceChange changedFamily square).mp
  rw [rankOpen_eq]
  rintro point ⟨changedPoint, rfl⟩
  exact ⟨mem_perfectLocus_of_fibre_degree_gt_canonical family lineBundle _ (degreeBound _),
    dimension _⟩

end AlgebraicGeometry.Scheme.Modules
