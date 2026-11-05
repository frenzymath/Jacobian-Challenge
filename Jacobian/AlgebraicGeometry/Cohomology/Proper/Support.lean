import Jacobian.AlgebraicGeometry.Modules.Vanishing
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Enlarging opens along closed supports

For a closed immersion, a nonempty open in the source enlarges any open in the
target disjoint from its image. The enlarged open pulls back into the chosen
source open. A module vanishing on that source open therefore has direct image
vanishing on the enlarged target open, as needed for noetherian dévissage.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Z : Scheme.{u}}

/-- A nonempty open of a closed subscheme enlarges any open disjoint from that subscheme,
without introducing points outside the chosen open in the inverse image. -/
lemma exists_open_extension (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens)
    (disjoint : Disjoint (U : Set X) (Set.range i)) (W : Z.Opens)
    (nonempty : (W : Set Z).Nonempty) :
    ∃ V : X.Opens, U < V ∧ i ⁻¹ᵁ V ≤ W := by
  let extension : X.Opens := ⟨(i.base '' (W : Set Z)ᶜ)ᶜ,
    (i.isClosedEmbedding.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩
  have outside (point : Z) : i point ∉ U := fun membership ↦
    Set.disjoint_left.mp disjoint membership ⟨point, rfl⟩
  refine ⟨U ⊔ extension, ?_, ?_⟩
  · obtain ⟨point, membership⟩ := nonempty
    refine lt_of_le_of_ne le_sup_left fun equality ↦ outside point ?_
    rw [equality]
    refine Or.inr fun ⟨otherPoint, not_mem, same_image⟩ ↦ not_mem ?_
    rwa [i.isClosedEmbedding.injective same_image]
  · intro point membership
    obtain membership | membership := membership
    · exact (outside point membership).elim
    · by_contra not_mem
      exact membership ⟨point, not_mem, rfl⟩

end Scheme.Hom

namespace Scheme.Modules

variable {X Z : Scheme.{u}}

/-- A direct image vanishes on any open whose inverse image is contained in a source
open on which the module vanishes. -/
lemma isZero_restrict_pushforward_of_preimage_le (i : Z ⟶ X) (M : Z.Modules)
    {U : X.Opens} {W : Z.Opens} (containment : i ⁻¹ᵁ U ≤ W)
    (vanishing : IsZero (M.restrict W.ι)) :
    IsZero (((pushforward i).obj M).restrict U.ι) := by
  rw [isZero_restrict_iff]
  intro V hV
  rw [pushforward_obj_obj]
  exact (isZero_restrict_iff M W).mp vanishing (i ⁻¹ᵁ V)
    ((i.preimage_mono hV).trans containment)

end Scheme.Modules

end AlgebraicGeometry
