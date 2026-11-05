import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Finite summands and additive functors

Additive functors transport finite-sum splittings, including across
isomorphisms of the two objects involved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

/-- An additive functor `functor` preserves the property that `sourceObject` is a direct summand of a finite
direct sum of copies of `summandObject`, up to isomorphisms `functor sourceObject ≅ sourceObject'` and `functor summandObject ≅ summandObject'`. -/
lemma CategoryTheory.Functor.exists_sum_comp_eq_id_of_iso
    {sourceCategory targetCategory : Type*} [Category sourceCategory] [Category targetCategory]
    [Preadditive sourceCategory] [Preadditive targetCategory] (functor : sourceCategory ⥤ targetCategory)
    [functor.Additive] {sourceObject summandObject : sourceCategory}
    {targetObject targetSummand : targetCategory}
    (objectIso : functor.obj sourceObject ≅ targetObject)
    (summandIso : functor.obj summandObject ≅ targetSummand)
    (splitting : ∃ (rank : ℕ) (coordinates : Fin rank → (sourceObject ⟶ summandObject))
      (generators : Fin rank → (summandObject ⟶ sourceObject)),
      ∑ index, coordinates index ≫ generators index = 𝟙 sourceObject) :
    ∃ (rank : ℕ) (coordinates : Fin rank → (targetObject ⟶ targetSummand))
      (generators : Fin rank → (targetSummand ⟶ targetObject)),
      ∑ index, coordinates index ≫ generators index = 𝟙 targetObject := by
  obtain ⟨rank, coordinates, generators, splitting⟩ := splitting
  refine ⟨rank, fun index ↦ objectIso.inv ≫ functor.map (coordinates index) ≫ summandIso.hom,
    fun index ↦ summandIso.inv ≫ functor.map (generators index) ≫ objectIso.hom, ?_⟩
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Preadditive.comp_sum]
  simp only [← Category.assoc, ← Preadditive.sum_comp]
  simp only [Category.assoc, ← functor.map_comp, ← functor.map_sum, splitting, functor.map_id, Category.id_comp,
    Iso.inv_hom_id]
