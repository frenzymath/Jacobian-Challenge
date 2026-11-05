import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over

/-!
# Points of fppf covering sieves

Every point of a scheme lifts to a flat, locally finitely presented morphism
in a covering sieve. The same statement holds on the category of schemes
over a fixed base.
-/

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A covering sieve of the fppf topology on a scheme `X` is jointly surjective through flat
morphisms locally of finite presentation: every point of `X` is in the image of some flat
morphism locally of finite presentation `g : Y ⟶ X` of the sieve. -/
lemma exists_flat_mem_of_mem_fppfTopology {X : Scheme.{u}} {S : Sieve X}
    (hS : S ∈ fppfTopology X) (x : X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), S g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
      x ∈ Set.range g.base := by
  have : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}).ContainsIdentities :=
    ⟨fun X ↦ ⟨inferInstanceAs (Flat (𝟙 X)), inferInstanceAs (LocallyOfFinitePresentation (𝟙 X))⟩⟩
  have : fppfPrecoverage.{u}.HasIsos := by unfold fppfPrecoverage; infer_instance
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨R, ⟨hR₁, hR₂⟩, hle⟩ := hS
  obtain ⟨_, _, h, hx⟩ := hR₁ x
  rcases h with ⟨hg⟩
  exact ⟨_, _, hle _ _ hg, (hR₂ hg).1, (hR₂ hg).2, hx⟩

/-- A covering sieve of the fppf topology on `Over S` is jointly surjective through morphisms
whose underlying morphism of schemes is flat and locally of finite presentation. -/
lemma exists_flat_mem_of_mem_fppfTopology_over {S : Scheme.{u}} {T : Over S} {R : Sieve T}
    (hR : R ∈ fppfTopology.over S T) (t : T.left) :
    ∃ (Z : Over S) (g : Z ⟶ T), R g ∧ Flat g.left ∧ LocallyOfFinitePresentation g.left ∧
      t ∈ Set.range g.left.base := by
  obtain ⟨Y, g, ⟨Z, h, k, hh, rfl⟩, hg₁, hg₂, hx⟩ :=
    exists_flat_mem_of_mem_fppfTopology ((GrothendieckTopology.mem_over_iff _ _).1 hR) t
  refine ⟨Over.mk (k ≫ Z.hom), Over.homMk k ≫ h, R.downward_closed hh _, ?_, ?_, ?_⟩
  all_goals simpa using ‹_›

end AlgebraicGeometry.Scheme
