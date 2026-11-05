import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

/-!
# The restriction of scalars of presheaves of modules is lax monoidal

Let `R` and `R'` be presheaves of commutative rings on a category `C`. For a morphism
`α : R ⋙ forget₂ _ _ ⟶ R' ⋙ forget₂ _ _` of the underlying presheaves of rings, we
show that the restriction of scalars functor
`PresheafOfModules.restrictScalars α : PresheafOfModules (R' ⋙ forget₂ _ _) ⥤
PresheafOfModules (R ⋙ forget₂ _ _)` is lax monoidal. The structure maps are obtained
objectwise from the lax monoidal structure on `ModuleCat.restrictScalars`, and the content of
the statement is their naturality in the object of `C`.

## Main declarations

* `PresheafOfModules.restrictScalarsLaxMonoidal`: `restrictScalars α` is lax monoidal;
* `PresheafOfModules.restrictScalars_ε_app` and `PresheafOfModules.restrictScalars_μ_app`
  identify the structure maps objectwise.

-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe v₁ u₁ u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R R' : Cᵒᵖ ⥤ CommRingCat.{u}}
  (α : R ⋙ forget₂ CommRingCat RingCat ⟶ R' ⋙ forget₂ CommRingCat RingCat)

open ModuleCat.MonoidalCategory in
/-- The restriction of scalars along a morphism `α` of presheaves of rings is lax monoidal:
the structure map `μ` is objectwise the one of `ModuleCat.restrictScalars (α.app X)`, and the
content of the statement is that these maps are natural in `X`, i.e. that for `f : X ⟶ Y`
in `Cᵒᵖ` the square

```
                             μ_X
  M₁(X) ⊗_{R'(X)} M₂(X) ─────────────→ (M₁ ⊗ M₂)(X)
            │                                │
   M₁(f) ⊗ M₂(f) │                           │ (M₁ ⊗ M₂)(f)
            ↓                                ↓
  M₁(Y) ⊗_{R'(Y)} M₂(Y) ─────────────→ (M₁ ⊗ M₂)(Y)
                             μ_Y
```

commutes, all modules being read over `R` via `α`. -/
noncomputable instance restrictScalarsLaxMonoidal : (restrictScalars.{u} α).LaxMonoidal where
  ε :=
    { app X := ε (ModuleCat.restrictScalars (α.app X).hom)
      naturality {X Y} f := by
        refine ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
          ModuleCat.restrictScalars.map_apply, Functor.comp_obj, CommRingCat.forgetToRingCat_obj,
          Functor.comp_map, CommRingCat.forgetToRingCat_map_hom]
        -- `rw` and `simp only` fail here: the `Module` instances carried by `R.obj Y` and by
        -- `(R ⋙ forget₂ CommRingCat RingCat).obj Y` are only definitionally equal
        erw [ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η]
        exact RingHom.congr_fun (congrArg RingCat.Hom.hom (α.naturality f)) r }
  μ M₁ M₂ :=
    { app X := μ (ModuleCat.restrictScalars (α.app X).hom) (M₁.obj X) (M₂.obj X)
      naturality {X Y} f := by
        refine tensor_ext fun m₁ m₂ ↦ ?_
        simp only [Functor.comp_obj, CommRingCat.forgetToRingCat_obj, Functor.comp_map,
          CommRingCat.forgetToRingCat_map_hom, ModuleCat.hom_comp, LinearMap.coe_comp,
          Function.comp_apply, ModuleCat.restrictScalars.map_apply]
        -- as above, the two `Module` instances on `R.obj Y` are only definitionally equal
        erw [ModuleCat.restrictScalars_μ_tmul, ModuleCat.restrictScalars_μ_tmul]
        rfl }
  μ_natural_left {M₁ M₂} f M₃ := by
    ext1 X
    exact μ_natural_left (F := ModuleCat.restrictScalars (α.app X).hom) (f.app X) (M₃.obj X)
  μ_natural_right M₁ f := by
    ext1 X
    exact μ_natural_right (F := ModuleCat.restrictScalars (α.app X).hom) (M₁.obj X) (f.app X)
  associativity M₁ M₂ M₃ := by
    ext1 X
    exact associativity (F := ModuleCat.restrictScalars (α.app X).hom)
      (M₁.obj X) (M₂.obj X) (M₃.obj X)
  left_unitality M := by
    ext1 X
    exact left_unitality (F := ModuleCat.restrictScalars (α.app X).hom) (M.obj X)
  right_unitality M := by
    ext1 X
    exact right_unitality (F := ModuleCat.restrictScalars (α.app X).hom) (M.obj X)

@[simp]
lemma restrictScalars_ε_app (X : Cᵒᵖ) :
    (ε (restrictScalars.{u} α)).app X = ε (ModuleCat.restrictScalars (α.app X).hom) :=
  rfl

@[simp]
lemma restrictScalars_μ_app
    (M₁ M₂ : PresheafOfModules.{u} (R' ⋙ forget₂ CommRingCat RingCat)) (X : Cᵒᵖ) :
    (μ (restrictScalars.{u} α) M₁ M₂).app X =
      μ (ModuleCat.restrictScalars (α.app X).hom) (M₁.obj X) (M₂.obj X) :=
  rfl

end PresheafOfModules
