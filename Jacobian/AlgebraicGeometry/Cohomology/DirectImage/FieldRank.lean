import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Jacobian.AlgebraicGeometry.Modules.FieldRank
import Jacobian.AlgebraicGeometry.Modules.FiniteFreeComplex

/-!
# Single-degree direct images over a field

For quasi-coherent coefficients on a quasi-compact separated scheme over a
field, higher direct images are detected by cohomology. Finite-dimensional
cohomology concentrated in one degree gives a locally free direct image of
the same rank in that degree and zero direct images in every other degree.
-/

noncomputable section

universe cohomologyUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {baseField : Type cohomologyUniverse} [Field baseField]
  {source : Scheme.{cohomologyUniverse}}
  [source.Over (Spec (.of baseField))]
  [QuasiCompact (source ↘ Spec (.of baseField))]
  [IsSeparated (source ↘ Spec (.of baseField))]

/-- Cohomology over a field detects a direct image concentrated in a single
degree with prescribed finite rank. -/
theorem isFiniteLocallyFreeInDegree_higherDirectImage_of_cohomology
    (moduleSheaf : source.Modules) [moduleSheaf.IsQuasicoherent]
    {degree rank : ℕ} [Module.Finite baseField (moduleSheaf.H degree)]
    (dimension : Module.finrank baseField (moduleSheaf.H degree) = rank)
    (vanishing : ∀ otherDegree, otherDegree ≠ degree →
      Subsingleton (moduleSheaf.H otherDegree)) :
    IsFiniteLocallyFreeInDegree
      (fun otherDegree ↦
        (higherDirectImage (source ↘ Spec (.of baseField)) otherDegree).obj moduleSheaf)
      degree rank := by
  have := isGrothendieckAbelian source
  refine ⟨?_, ?_⟩
  · intro otherDegree different
    obtain ⟨comparison⟩ :=
      nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H
        moduleSheaf baseField otherDegree
    have : Subsingleton (moduleSheaf.H otherDegree) := vanishing otherDegree different
    have := comparison.toEquiv.subsingleton
    exact (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero
      (Field.toIsField baseField) _).2 Module.finrank_zero_of_subsingleton
  · obtain ⟨comparison⟩ :=
      nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H
        moduleSheaf baseField degree
    have := Module.Finite.equiv comparison.symm
    exact (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj
      (Field.toIsField baseField) _ rank).2 (comparison.finrank_eq.trans dimension)

end AlgebraicGeometry.Scheme.Modules
