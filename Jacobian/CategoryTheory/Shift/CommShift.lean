import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.Algebra.Group.Int.Defs

/-!
# Detecting compatibility with shifts

Compatibility of natural transformations with shifts can be detected after faithful postcomposition or suitable resolving precomposition.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CategoryTheory.NatTrans.CommShift

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] {A : Type*} [AddMonoid A]
  [HasShift C A] [HasShift D A] [HasShift E A]
  {F₁ F₂ : C ⥤ D} (τ : F₁ ⟶ F₂) [F₁.CommShift A] [F₂.CommShift A]

/-- A natural transformation commutes with shifts if it does after composition with a
faithful functor commuting with shifts. -/
lemma of_whiskerRight (G : D ⥤ E) [G.CommShift A] [G.Faithful]
    [NatTrans.CommShift (Functor.whiskerRight τ G) A] : NatTrans.CommShift τ A where
  shift_comm a := by
    ext X
    apply G.map_injective
    have h := NatTrans.shift_app_comm (Functor.whiskerRight τ G) a X
    simp only [Functor.comp_obj, Functor.whiskerRight_app, Functor.commShiftIso_comp_hom_app,
      Category.assoc] at h
    rw [← Functor.commShiftIso_hom_naturality, ← G.map_comp_assoc, ← G.map_comp_assoc] at h
    simpa using (cancel_mono _).1 h

/-- A natural transformation `τ : F₁ ⟶ F₂` commutes with shifts if it does after
precomposition with a functor `L` commuting with shifts, provided every object `X` maps to
an object `L.obj Y` by a morphism `f` such that `F₂.map f` is an isomorphism. -/
lemma of_whiskerLeft (L : E ⥤ C) [L.CommShift A]
    [NatTrans.CommShift (Functor.whiskerLeft L τ) A]
    (h : ∀ X, ∃ (Y : E) (f : X ⟶ L.obj Y), IsIso (F₂.map f)) : NatTrans.CommShift τ A where
  shift_comm a := by
    ext X
    obtain ⟨Y, f, hf⟩ := h X
    have hY : (F₁.commShiftIso a).hom.app (L.obj Y) ≫ (τ.app (L.obj Y))⟦a⟧' =
        τ.app ((L.obj Y)⟦a⟧) ≫ (F₂.commShiftIso a).hom.app (L.obj Y) := by
      have h := NatTrans.shift_app_comm (Functor.whiskerLeft L τ) a Y
      simp only [Functor.comp_obj, Functor.whiskerLeft_app, Functor.commShiftIso_comp_hom_app,
        Category.assoc] at h
      rw [← τ.naturality_assoc] at h
      exact (cancel_epi _).1 h
    dsimp
    rw [← cancel_mono ((F₂.map f)⟦a⟧'), Category.assoc, ← Functor.map_comp,
      ← τ.naturality, Functor.map_comp, ← Functor.commShiftIso_hom_naturality_assoc, hY,
      Category.assoc, ← Functor.commShiftIso_hom_naturality, τ.naturality_assoc]

end CategoryTheory.NatTrans.CommShift

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]

/-- A degree-two composite `X⟦1⟧ ⟶ Y⟦1⟧⟦1⟧ ≅ Y⟦2⟧` pushed through a functor commuting with
shifts, followed by a map `ψ : F Y ⟶ Z`, is the degree-one composite shifted by one:

```
F (X⟦1⟧) ──F(δ⟦1⟧ ≫ add⁻¹)──▶ F (Y⟦2⟧) ──≅──▶ (F Y)⟦2⟧ ──ψ⟦2⟧──▶ Z⟦2⟧
    │                                                            ▲
  ≅ │                                                            │ add⁻¹
    ▼                                                            │
(F X)⟦1⟧ ─────────(F δ ≫ ≅ ≫ ψ⟦1⟧)⟦1⟧─────────────────────▶ Z⟦1⟧⟦1⟧
```
-/
lemma map_shift_comp_shiftFunctorAdd'_inv (F : C ⥤ D) [F.CommShift ℤ] {X Y : C} {Z : D}
    (δ : X ⟶ Y⟦(1 : ℤ)⟧) (ψ : F.obj Y ⟶ Z) :
    F.map (δ⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' C (1 : ℤ) 1 2 rfl).inv.app Y) ≫
        (F.commShiftIso (2 : ℤ)).hom.app Y ≫ ψ⟦(2 : ℤ)⟧' =
      (F.commShiftIso (1 : ℤ)).hom.app X ≫
        (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app Y ≫ ψ⟦(1 : ℤ)⟧')⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' D (1 : ℤ) 1 2 rfl).inv.app Z := by
  rw [F.commShiftIso_add' (show (1 : ℤ) + 1 = 2 from rfl)]
  simp only [CommShift.isoAdd'_hom_app, Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc ((shiftFunctorAdd' C 1 1 2 _).inv.app Y), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, F.commShiftIso_hom_naturality_assoc,
    ← NatTrans.naturality]
  rfl

end CategoryTheory.Functor
