import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Additivity of injective resolutions in the homotopy category

Comparison maps for the sum of two morphisms agree up to homotopy with the
sum of their comparison maps. Hence the injective-resolution functor is additive.
-/

noncomputable section
open CategoryTheory Category Limits
namespace CategoryTheory
variable (C : Type*) [Category* C] [Abelian C] [HasInjectiveResolutions C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance : (injectiveResolutions C).Additive where
  map_add {X Y f g} := by
    dsimp [injectiveResolutions]
    rw [← Functor.map_add]
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descHomotopy (f + g) <;>
      simp [Preadditive.comp_add, Preadditive.add_comp]

end CategoryTheory

namespace CategoryTheory

variable {C : Type*} [Category* C] [HasZeroObject C] [HasZeroMorphisms C]

/-- A category in which every object has an injective resolution has enough injectives: the
first map `X ⟶ I⁰` of an injective resolution is a monomorphism into an injective object. -/
lemma enoughInjectives_of_hasInjectiveResolutions [HasInjectiveResolutions C] :
    EnoughInjectives C where
  presentation X :=
    let R := (HasInjectiveResolution.out (Z := X)).some
    ⟨{ J := R.cocomplex.X 0
       f := (HomologicalComplex.singleObjXSelf _ 0 X).inv ≫ R.ι.f 0 }⟩

end CategoryTheory
