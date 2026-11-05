import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Slices in cartesian monoidal categories

A morphism into a product with constant second coordinate factors through
the corresponding slice. Constancy on a slice is preserved by composition.
-/

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory.CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- A morphism `p : T ⟶ X ⊗ Y` whose second component is constant with value the point
`y : 𝟙_ C ⟶ Y` factors through the slice `lift (𝟙 X) (toUnit X ≫ y) : X ⟶ X ⊗ Y` over `y`. 

-/
theorem eq_comp_lift_id_of_comp_snd_eq {T X Y : C} {p : T ⟶ X ⊗ Y} {y : 𝟙_ C ⟶ Y}
    (h : p ≫ snd X Y = toUnit T ≫ y) :
    p = (p ≫ fst X Y) ≫ lift (𝟙 X) (toUnit X ≫ y) := by
  rw [comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit, ← h, lift_comp_fst_snd]

/-- If `f : X ⊗ Y ⟶ Z` is constant on the slice over the point `y : 𝟙_ C ⟶ Y` (with value the
point `c : 𝟙_ C ⟶ Z`), then `f` composed with any morphism whose second component is constant
with value `y` is constant with value `c`. 

-/
theorem comp_eq_toUnit_comp_of_comp_snd_eq {T X Y Z : C} {p : T ⟶ X ⊗ Y} {y : 𝟙_ C ⟶ Y}
    {f : X ⊗ Y ⟶ Z} {c : 𝟙_ C ⟶ Z} (h : p ≫ snd X Y = toUnit T ≫ y)
    (hf : lift (𝟙 X) (toUnit X ≫ y) ≫ f = toUnit X ≫ c) :
    p ≫ f = toUnit T ≫ c := by
  rw [eq_comp_lift_id_of_comp_snd_eq h, Category.assoc, hf, ← Category.assoc, comp_toUnit]

end CategoryTheory.CartesianMonoidalCategory
