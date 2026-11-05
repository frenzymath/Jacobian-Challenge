import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Perfect complexes of modules

An object of the derived category of modules is perfect when it has a bounded
representative consisting of finite projective modules. Perfect objects are
bounded, and over a Noetherian ring their cohomology modules are finite.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u w

open CategoryTheory Limits

namespace DerivedCategory

variable {baseRing : Type u} [CommRing baseRing]
  [HasDerivedCategory.{w} (ModuleCat.{u} baseRing)]

/-- A perfect object is represented by a bounded complex of finite projective modules. -/
def IsPerfect (object : DerivedCategory (ModuleCat.{u} baseRing)) : Prop :=
  ∃ (complex : CochainComplex (ModuleCat.{u} baseRing) ℤ) (lowerBound upperBound : ℤ),
    complex.IsStrictlyGE lowerBound ∧ complex.IsStrictlyLE upperBound ∧
      (∀ degree, Module.Projective baseRing (complex.X degree) ∧
        Module.Finite baseRing (complex.X degree)) ∧ Nonempty (object ≅ Q.obj complex)

/-- Perfectness is invariant under isomorphism. -/
theorem IsPerfect.of_iso {source target : DerivedCategory (ModuleCat.{u} baseRing)}
    (perfect : source.IsPerfect) (comparison : source ≅ target) : target.IsPerfect := by
  obtain ⟨complex, lowerBound, upperBound, below, above, finite_projective, ⟨model⟩⟩ := perfect
  exact ⟨complex, lowerBound, upperBound, below, above, finite_projective,
    ⟨comparison.symm ≪≫ model⟩⟩

/-- The image of a bounded finite projective complex is perfect. -/
lemma isPerfect_Q_obj (complex : CochainComplex (ModuleCat.{u} baseRing) ℤ)
    (lowerBound upperBound : ℤ) [complex.IsStrictlyGE lowerBound] [complex.IsStrictlyLE upperBound]
    (finite_projective : ∀ degree, Module.Projective baseRing (complex.X degree) ∧
      Module.Finite baseRing (complex.X degree)) : (Q.obj complex).IsPerfect :=
  ⟨complex, lowerBound, upperBound, inferInstance, inferInstance, finite_projective, ⟨Iso.refl _⟩⟩

/-- A perfect object is bounded for the canonical t-structure. -/
theorem IsPerfect.bounded {object : DerivedCategory (ModuleCat.{u} baseRing)}
    (perfect : object.IsPerfect) : TStructure.t.bounded object := by
  obtain ⟨complex, lowerBound, upperBound, _, _, _, ⟨model⟩⟩ := perfect
  exact ⟨⟨lowerBound, TStructure.t.isGE_of_iso model.symm lowerBound⟩,
    ⟨upperBound, TStructure.t.isLE_of_iso model.symm upperBound⟩⟩

/-- Cohomology modules of perfect objects over a Noetherian ring are finite. -/
theorem IsPerfect.finite_homology [IsNoetherianRing baseRing]
    {object : DerivedCategory (ModuleCat.{u} baseRing)} (perfect : object.IsPerfect) (degree : ℤ) :
    Module.Finite baseRing ((homologyFunctor (ModuleCat.{u} baseRing) degree).obj object) := by
  obtain ⟨complex, _, _, _, _, finite_projective, ⟨model⟩⟩ := perfect
  let cohomology_comparison :
      (homologyFunctor (ModuleCat.{u} baseRing) degree).obj object ≅ complex.homology degree :=
    (homologyFunctor (ModuleCat.{u} baseRing) degree).mapIso model ≪≫
      (homologyFunctorFactors (ModuleCat.{u} baseRing) degree).app complex
  have := (finite_projective degree).2
  have : Module.Finite baseRing (complex.cycles degree) :=
    Module.Finite.of_injective (complex.iCycles degree).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have : Module.Finite baseRing (complex.homology degree) :=
    Module.Finite.of_surjective (complex.homologyπ degree).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  exact Module.Finite.equiv cohomology_comparison.toLinearEquiv.symm

end DerivedCategory
