import Jacobian.RingTheory.RegularLocalRing.Domain
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Normality of regular local rings in dimension at most one

A regular local ring of dimension at most one is a field or a discrete
valuation ring. In either case it is integrally closed.
-/

noncomputable section

/-- A regular local ring of Krull dimension at most one is integrally closed. -/
theorem IsRegularLocalRing.isIntegrallyClosed (ring : Type*) [CommRing ring]
    [IsRegularLocalRing ring] (dimensionBound : ringKrullDim ring ≤ 1) :
    IsIntegrallyClosed ring := by
  by_cases field : IsField ring
  · letI := field.toField
    infer_instance
  have dimension : ringKrullDim ring = 1 := by
    refine le_antisymm dimensionBound (not_lt.mp fun smaller ↦ field ?_)
    have : Ring.KrullDimLE 0 ring :=
      Ring.krullDimLE_iff.mpr (ENat.WithBot.lt_add_one_iff.mp (by simpa using smaller))
    exact Ring.KrullDimLE.isField_of_isDomain
  have := IsRegularLocalRing.isDiscreteValuationRing ring dimension
  infer_instance
