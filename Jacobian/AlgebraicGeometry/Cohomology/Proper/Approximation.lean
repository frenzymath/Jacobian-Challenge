import Jacobian.AlgebraicGeometry.Cohomology.Proper.Modification
import Jacobian.AlgebraicGeometry.Modules.PullbackMonoidal
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Twist
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Twisted comparisons on proper modifications

A coordinate power defines a map from a module to the pushforward of its twisted
pullback along a proper modification. On a nonempty open where the modification
is an isomorphism, one can choose a coordinate and shrink the open so that all
nonnegative powers give isomorphisms. This geometric comparison does not require
cohomological finiteness or a bound on the twisting degree.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y baseScheme : Scheme.{u}} {coordinates : Type u}

/-- The comparison obtained by multiplying a pulled-back module by a coordinate power. -/
def twistedModificationComparison (π : X ⟶ Y)
    (embedding : X ⟶ ℙ(coordinates; baseScheme)) (moduleSheaf : Y.Modules)
    (coordinate : coordinates) (degree : ℕ) :
    moduleSheaf ⟶ (pushforward π).obj
      ((pullback π).obj moduleSheaf ⊗ ProjectiveSpace.twistRestrict embedding degree) :=
  modificationComparison π moduleSheaf _
    ((ρ_ ((pullback π).obj moduleSheaf)).inv ≫
      ((pullback π).obj moduleSheaf ◁
        ProjectiveSpace.pullbackTwistPowSection embedding coordinate degree))

/-- A coordinate can be chosen so that all nonnegative twisted comparisons are
isomorphisms over one nonempty open contained in the isomorphism locus. -/
theorem exists_nonempty_open_isIso_twistedModificationComparison (π : X ⟶ Y)
    [IsProper π] (surjective : Function.Surjective π)
    (embedding : X ⟶ ℙ(coordinates; baseScheme))
    (moduleSheaf : Y.Modules) [moduleSheaf.IsQuasicoherent]
    (isomorphismOpen : Y.Opens) (nonemptyOpen : (isomorphismOpen : Set Y).Nonempty)
    [IsIso (π ∣_ isomorphismOpen)] :
    ∃ (coordinate : coordinates) (openSubset : Y.Opens),
      (openSubset : Set Y).Nonempty ∧ openSubset ≤ isomorphismOpen ∧
      ∀ degree : ℕ, IsIso ((restrictFunctor openSubset.ι).map
        (twistedModificationComparison π embedding moduleSheaf coordinate degree)) := by
  classical
  obtain ⟨point, point_mem⟩ := nonemptyOpen
  obtain ⟨preimagePoint, rfl⟩ := surjective point
  obtain ⟨coordinate, coordinate_mem⟩ : ∃ coordinate,
      embedding preimagePoint ∈ ProjectiveSpace.standardOpen coordinates baseScheme coordinate :=
    Opens.mem_iSup.mp ((ProjectiveSpace.iSup_standardOpen coordinates baseScheme).symm ▸ trivial :
      embedding preimagePoint ∈ ⨆ coordinate,
        ProjectiveSpace.standardOpen coordinates baseScheme coordinate)
  let coordinateOpen := embedding ⁻¹ᵁ
    ProjectiveSpace.standardOpen coordinates baseScheme coordinate
  let openSubset : Y.Opens := isomorphismOpen ⊓
    ⟨(π '' (coordinateOpen : Set X)ᶜ)ᶜ,
      (π.isClosedMap _ coordinateOpen.isOpen.isClosed_compl).isOpen_compl⟩
  have injectiveOverOpen {firstPoint secondPoint : X}
      (first_mem : π firstPoint ∈ isomorphismOpen)
      (second_mem : π secondPoint ∈ isomorphismOpen)
      (equal_image : π firstPoint = π secondPoint) : firstPoint = secondPoint := by
    exact congrArg Subtype.val ((π ∣_ isomorphismOpen).isOpenEmbedding.injective
      (a₁ := ⟨firstPoint, first_mem⟩) (a₂ := ⟨secondPoint, second_mem⟩)
      (Subtype.ext (by simpa using equal_image)))
  have preimage_le : π ⁻¹ᵁ openSubset ≤ coordinateOpen := by
    intro sourcePoint sourcePoint_mem
    by_contra sourcePoint_not_mem
    exact sourcePoint_mem.2 ⟨sourcePoint, sourcePoint_not_mem, rfl⟩
  have point_mem_openSubset : π preimagePoint ∈ openSubset :=
    ⟨point_mem, fun ⟨sourcePoint, sourcePoint_not_mem, equal_image⟩ ↦
      sourcePoint_not_mem
        (injectiveOverOpen (equal_image ▸ point_mem) point_mem equal_image ▸ coordinate_mem)⟩
  refine ⟨coordinate, openSubset, ⟨_, point_mem_openSubset⟩, inf_le_left, fun degree ↦ ?_⟩
  let pulledBack := (pullback π).obj moduleSheaf
  let sectionMap := ProjectiveSpace.pullbackTwistPowSection embedding coordinate degree
  let multiplication : pulledBack ⟶
      pulledBack ⊗ ProjectiveSpace.twistRestrict embedding degree :=
    (ρ_ pulledBack).inv ≫ (pulledBack ◁ sectionMap)
  have : IsIso ((restrictFunctor coordinateOpen.ι).map sectionMap) :=
    ProjectiveSpace.isIso_restrict_pullbackTwistPowSection embedding coordinate degree
  have : IsIso ((restrictFunctor coordinateOpen.ι).map multiplication) := by
    have := isIso_restrict_whiskerLeft pulledBack sectionMap coordinateOpen
    dsimp only [multiplication]
    rw [Functor.map_comp]
    infer_instance
  refine isIso_restrict_of_bijective_app _ openSubset fun affineOpen affineOpen_affine
    affineOpen_le ↦ ?_
  exact (bijective_app_of_isIso_restrict multiplication
    ((π.preimage_mono affineOpen_le).trans preimage_le)).comp
      (bijective_pullbackSection_of_isIso_morphismRestrict π moduleSheaf affineOpen_affine
        (affineOpen_le.trans inf_le_left))

end AlgebraicGeometry.Scheme.Modules
