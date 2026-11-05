import Jacobian.AlgebraicGeometry.Picard.Sheaf
import Jacobian.AlgebraicGeometry.Sites.Fppf
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Local representatives of the relative Picard sheaf

A section of the fppf Picard sheaf is represented locally near every point
by an invertible sheaf class. If two classes represent the same section,
they agree after a flat, locally finitely presented morphism through each
point. These statements permit fiberwise invariants to descend to the sheaf.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Every point admits an fppf local representative of a Picard-sheaf section. -/
lemma exists_picardClass_representative {T : Over S} (x : (picardFunctor f).obj.obj (.op T))
    (t : T.left) :
    ∃ (Z : Over S) (g : Z ⟶ T) (L : (picardPresheaf f).obj (.op Z)) (z : Z.left),
      (toPicardFunctor f).app (.op Z) L = (picardFunctor f).obj.map g.op x ∧
        g.left z = t ∧ Flat g.left ∧ LocallyOfFinitePresentation g.left := by
  obtain ⟨Z, g, ⟨L, hL⟩, hg₁, hg₂, z, hz⟩ := exists_flat_mem_of_mem_fppfTopology_over
    (Presheaf.imageSieve_mem (fppfTopology.over S) (toPicardFunctor f) x) t
  exact ⟨Z, g, L, z, hL, hz, hg₁, hg₂⟩

/-- Classes with equal sheafification agree fppf locally through every point. -/
lemma exists_picardClass_eq_of_toPicardFunctor_eq {T : Over S}
    {L L' : (picardPresheaf f).obj (.op T)}
    (h : (toPicardFunctor f).app (.op T) L = (toPicardFunctor f).app (.op T) L')
    (t : T.left) :
    ∃ (Z : Over S) (g : Z ⟶ T) (z : Z.left),
      (picardPresheaf f).map g.op L = (picardPresheaf f).map g.op L' ∧
        g.left z = t ∧ Flat g.left ∧ LocallyOfFinitePresentation g.left := by
  obtain ⟨Z, g, hg, hg₁, hg₂, z, hz⟩ := exists_flat_mem_of_mem_fppfTopology_over
    (Presheaf.equalizerSieve_mem (fppfTopology.over S) (toPicardFunctor f) L L' h) t
  exact ⟨Z, g, z, hg, hz, hg₁, hg₂⟩

end AlgebraicGeometry
