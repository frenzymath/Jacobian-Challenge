import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Artinian.Algebra

/-!
# Schemes finite over a field

A scheme finite over a field has a finite-dimensional ring of global sections and a finite
discrete underlying space.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Global sections of a finite scheme over a field form a finite algebra. -/
theorem finite_globalSections_of_isFinite {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K))
    [IsFinite g] :
    letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom.toAlgebra
    Module.Finite K Γ(Z, ⊤) := by
  have finiteMap := (HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := g)).mp
    inferInstance
  exact finiteMap.2.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)

/-- Finite schemes over a field have a finite discrete underlying space. -/
theorem finite_and_discreteTopology_of_isFinite {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K))
    [IsFinite g] : Finite Z ∧ DiscreteTopology Z := by
  have : IsAffine Z := isAffine_of_isAffineHom g
  letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appTop).hom.toAlgebra
  letI := finite_globalSections_of_isFinite g
  have : IsArtinianRing Γ(Z, ⊤) := .of_finite K Γ(Z, ⊤)
  let comparison := Scheme.homeoOfIso Z.isoSpec
  have : Finite (Spec Γ(Z, ⊤)) := inferInstanceAs (Finite (PrimeSpectrum Γ(Z, ⊤)))
  have : DiscreteTopology (Spec Γ(Z, ⊤)) :=
    inferInstanceAs (DiscreteTopology (PrimeSpectrum _))
  exact ⟨Finite.of_injective comparison comparison.injective,
    comparison.isEmbedding.discreteTopology⟩

end AlgebraicGeometry
