import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# A common independent companion

In a vector space of dimension at least two, any two nonzero vectors have a
common vector independent of each of them. The result holds over every field,
including the field with two elements.
-/

namespace Module

variable {baseField vectorSpace : Type*} [Field baseField]
  [AddCommGroup vectorSpace] [Module baseField vectorSpace]

private theorem pair_independent_iff_not_mem_span {first companion : vectorSpace}
    (nonzero : first ≠ 0) :
    LinearIndependent baseField ![first, companion] ↔
      companion ∉ Submodule.span baseField {first} := by
  rw [LinearIndependent.pair_iff' nonzero, Submodule.mem_span_singleton]
  simp only [not_exists]

private theorem not_both_mem_span_singleton {first second generator : vectorSpace}
    (independent : LinearIndependent baseField ![first, second])
    (first_mem : first ∈ Submodule.span baseField {generator})
    (second_mem : second ∈ Submodule.span baseField {generator}) : False := by
  obtain ⟨firstScalar, first_eq⟩ := Submodule.mem_span_singleton.mp first_mem
  obtain ⟨secondScalar, second_eq⟩ := Submodule.mem_span_singleton.mp second_mem
  have relation : secondScalar • first = firstScalar • second := by
    rw [← first_eq, ← second_eq, smul_smul, smul_smul, mul_comm secondScalar firstScalar]
  have scalar_zero := (independent.eq_zero_of_pair' relation).2
  have first_zero : first = 0 := by simpa [scalar_zero] using first_eq.symm
  exact independent.ne_zero 0 first_zero

/-- Two nonzero vectors in dimension at least two have a common independent
companion, without any assumption on the cardinality of the field. -/
theorem exists_linearIndependent_pair_companion
    (dimension : 1 < Module.finrank baseField vectorSpace)
    {first second : vectorSpace} (first_nonzero : first ≠ 0) (second_nonzero : second ≠ 0) :
    ∃ companion : vectorSpace, LinearIndependent baseField ![first, companion] ∧
      LinearIndependent baseField ![second, companion] := by
  classical
  obtain ⟨independentVector, independent⟩ :=
    exists_linearIndependent_pair_of_one_lt_finrank dimension first_nonzero
  have outside_first : independentVector ∉ Submodule.span baseField {first} :=
    (pair_independent_iff_not_mem_span first_nonzero).mp independent
  by_cases mem_second : independentVector ∈ Submodule.span baseField {second}
  · refine ⟨first + independentVector, ?_, ?_⟩
    · apply (pair_independent_iff_not_mem_span first_nonzero).mpr
      intro sum_mem
      apply outside_first
      have first_mem : first ∈ Submodule.span baseField {first} :=
        Submodule.subset_span (by simp)
      simpa using (Submodule.span baseField {first}).sub_mem sum_mem first_mem
    · apply (pair_independent_iff_not_mem_span second_nonzero).mpr
      intro sum_mem
      have first_mem : first ∈ Submodule.span baseField {second} := by
        simpa using (Submodule.span baseField {second}).sub_mem sum_mem mem_second
      exact not_both_mem_span_singleton independent first_mem mem_second
  · exact ⟨independentVector, independent,
      (pair_independent_iff_not_mem_span second_nonzero).mpr mem_second⟩

end Module
