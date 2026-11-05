import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper dense open subschemes

An open subscheme that is universally closed and dense is the entire scheme.
In particular, an open that is proper over a separated base and dense in an
intermediate open equals that intermediate open.
-/

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {ambientScheme baseScheme : Scheme.{u}}

theorem Scheme.Opens.eq_of_universallyClosed_of_dense {smallerOpen largerOpen : ambientScheme.Opens} (inclusion : smallerOpen ≤ largerOpen)
    [UniversallyClosed (ambientScheme.homOfLE inclusion)] (dense : (largerOpen : Set ambientScheme) ⊆ closure (smallerOpen : Set ambientScheme)) :
    smallerOpen = largerOpen := by
  have range_eq : Set.range (ambientScheme.homOfLE inclusion).base = largerOpen.ι.base ⁻¹' (smallerOpen : Set ambientScheme) := by
    rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
    rfl
  have range_dense : DenseRange (ambientScheme.homOfLE inclusion).base := by
    rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, range_eq,
      ← largerOpen.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage largerOpen.ι.continuous]
    exact fun point _ ↦ dense point.2
  have : IsDominant (ambientScheme.homOfLE inclusion) := ⟨range_dense⟩
  refine le_antisymm inclusion fun point membership ↦ ?_
  obtain ⟨preimage, image_eq⟩ := (ambientScheme.homOfLE inclusion).surjective ⟨point, membership⟩
  have range_mem : (⟨point, membership⟩ : largerOpen.toScheme) ∈ Set.range (ambientScheme.homOfLE inclusion).base := ⟨preimage, image_eq⟩
  rw [range_eq] at range_mem
  exact range_mem

theorem Scheme.Opens.eq_of_isProper_of_dense {smallerOpen largerOpen : ambientScheme.Opens} (inclusion : smallerOpen ≤ largerOpen) (baseMap : largerOpen.toScheme ⟶ baseScheme)
    [IsProper (ambientScheme.homOfLE inclusion ≫ baseMap)] [IsSeparated baseMap]
    (dense : (largerOpen : Set ambientScheme) ⊆ closure (smallerOpen : Set ambientScheme)) :
    smallerOpen = largerOpen :=
  have : UniversallyClosed (ambientScheme.homOfLE inclusion) :=
    UniversallyClosed.of_comp_of_isSeparated (f := ambientScheme.homOfLE inclusion) (g := baseMap)
  eq_of_universallyClosed_of_dense inclusion dense

end AlgebraicGeometry
