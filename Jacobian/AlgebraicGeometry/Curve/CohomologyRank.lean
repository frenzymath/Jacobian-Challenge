import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.FieldRank
import Jacobian.AlgebraicGeometry.Curve.Cohomology

/-!
# Acyclic rank-one direct images on curves

On a smooth proper geometrically irreducible curve, a finitely presented
coefficient sheaf with one-dimensional global sections and zero first
cohomology has invertible direct image in degree zero and no higher direct
images. Finite-dimensionality and vanishing above degree one follow from
the curve's cohomology, rather than additional hypotheses on direct images.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe curveUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {baseField : Type curveUniverse} [Field baseField] {source : Scheme.{curveUniverse}}
  [source.Over (Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
  [IsProper (source ↘ Spec (.of baseField))]
  [GeometricallyIrreducible (source ↘ Spec (.of baseField))]

/-- The curve-cohomology criterion for an invertible direct image concentrated
in degree zero. -/
theorem isFiniteLocallyFreeInDegree_higherDirectImage_of_finrankH
    (moduleSheaf : source.Modules) [moduleSheaf.IsFinitePresentation]
    (dimensionZero : moduleSheaf.finrankH baseField 0 = 1)
    (dimensionOne : moduleSheaf.finrankH baseField 1 = 0) :
    IsFiniteLocallyFreeInDegree
      (fun degree ↦
        (higherDirectImage (source ↘ Spec (.of baseField)) degree).obj moduleSheaf) 0 1 := by
  let curve : Curve baseField :=
    { carrier := Over.mk (source ↘ Spec (.of baseField))
      isProper := inferInstanceAs (IsProper (source ↘ Spec (.of baseField)))
      smoothOfRelativeDimension :=
        inferInstanceAs (SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField)))
      geometricallyIrreducible :=
        inferInstanceAs (GeometricallyIrreducible (source ↘ Spec (.of baseField))) }
  have : Module.Finite baseField (moduleSheaf.H 0) := curve.hasFiniteH moduleSheaf 0
  refine isFiniteLocallyFreeInDegree_higherDirectImage_of_cohomology
    moduleSheaf dimensionZero fun degree positive ↦ ?_
  by_cases degreeOne : degree = 1
  · subst degree
    have : Module.Finite baseField (moduleSheaf.H 1) := curve.hasFiniteH moduleSheaf 1
    exact (Module.finrank_eq_zero_iff_of_free baseField _).mp dimensionOne
  · exact curve.subsingleton_H moduleSheaf (by omega)

end AlgebraicGeometry.Scheme.Modules
