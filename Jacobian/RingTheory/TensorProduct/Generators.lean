import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Adjoin.Basic

/-!
# Ring generators of tensor products

Products of ring-generating families containing one generate the tensor product.
-/

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {baseRing firstRing secondRing : Type*} [CommRing baseRing] [CommRing firstRing]
    [CommRing secondRing] [Algebra baseRing firstRing] [Algebra baseRing secondRing]

/-- Elementary tensors of ring generators containing one generate the tensor product. -/
theorem closure_range_tmul_eq_top {firstIndex secondIndex : Type*} {firstFamily : firstIndex → firstRing} {secondFamily : secondIndex → secondRing}
    (first_generates : Subring.closure (Set.range firstFamily) = ⊤) (second_generates : Subring.closure (Set.range secondFamily) = ⊤)
    {firstUnitIndex : firstIndex} (first_one : firstFamily firstUnitIndex = 1) {secondUnitIndex : secondIndex} (second_one : secondFamily secondUnitIndex = 1) :
    Subring.closure (Set.range fun indices : firstIndex × secondIndex ↦ firstFamily indices.1 ⊗ₜ[baseRing] secondFamily indices.2) = ⊤ := by
  set generatedRing := Subring.closure (Set.range fun indices : firstIndex × secondIndex ↦ firstFamily indices.1 ⊗ₜ[baseRing] secondFamily indices.2) with hS
  have hleft : ∀ firstElement : firstRing, firstElement ⊗ₜ[baseRing] (1 : secondRing) ∈ generatedRing := by
    intro firstElement
    have first_mem : firstElement ⊗ₜ[baseRing] (1 : secondRing) ∈ Subring.map (includeLeftRingHom (R := baseRing) (A := firstRing) (B := secondRing))
        (Subring.closure (Set.range firstFamily)) := by
      rw [first_generates]
      exact ⟨firstElement, trivial, rfl⟩
    rw [RingHom.map_closure] at first_mem
    refine Subring.closure_le.mpr ?_ first_mem
    rintro _ ⟨_, ⟨index, rfl⟩, rfl⟩
    exact Subring.subset_closure ⟨(index, secondUnitIndex), by simp [second_one]⟩
  have hright : ∀ secondElement : secondRing, (1 : firstRing) ⊗ₜ[baseRing] secondElement ∈ generatedRing := by
    intro secondElement
    have second_mem : (1 : firstRing) ⊗ₜ[baseRing] secondElement ∈ Subring.map
        (includeRight (R := baseRing) (A := firstRing) (B := secondRing)).toRingHom (Subring.closure (Set.range secondFamily)) := by
      rw [second_generates]
      exact ⟨secondElement, trivial, rfl⟩
    rw [RingHom.map_closure] at second_mem
    refine Subring.closure_le.mpr ?_ second_mem
    rintro _ ⟨_, ⟨index, rfl⟩, rfl⟩
    exact Subring.subset_closure ⟨(firstUnitIndex, index), by simp [first_one]⟩
  have key : ∀ element : firstRing ⊗[baseRing] secondRing, element ∈ generatedRing := by
    intro element
    induction element with
    | zero => exact zero_mem _
    | tmul firstElement secondElement =>
        have factorization : firstElement ⊗ₜ[baseRing] secondElement = (firstElement ⊗ₜ[baseRing] (1 : secondRing)) * ((1 : firstRing) ⊗ₜ[baseRing] secondElement) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul]; simp
        rw [factorization]
        exact mul_mem (hleft firstElement) (hright secondElement)
    | add firstElement secondElement first_mem second_mem => exact add_mem first_mem second_mem
  exact le_antisymm le_top fun element _ ↦ key element

end Algebra.TensorProduct
