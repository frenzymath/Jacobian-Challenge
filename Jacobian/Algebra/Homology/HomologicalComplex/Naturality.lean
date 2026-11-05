import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Natural endomorphisms on complex homology

A natural endomorphism of the identity, applied termwise to a complex,
induces that same endomorphism on its homology.
-/

universe v u
open CategoryTheory Limits
namespace HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}

/-- A natural endomorphism `β` of the identity functor, applied termwise to a complex `K`, induces
`β` on the homology of `K`. -/
lemma homologyMap_eq_app_homology (β : 𝟭 C ⟶ 𝟭 C) {K : HomologicalComplex C c} (φ : K ⟶ K)
    (hφ : ∀ i, φ.f i = β.app (K.X i)) (i : ι) :
    homologyMap φ i = β.app (K.homology i) := by
  have hc : cyclesMap φ i = β.app (K.cycles i) := by
    rw [← cancel_mono (K.iCycles i), cyclesMap_i, hφ]
    exact β.naturality (K.iCycles i)
  rw [← cancel_epi (K.homologyπ i), homologyπ_naturality, hc]
  exact (β.naturality (K.homologyπ i)).symm

end HomologicalComplex
