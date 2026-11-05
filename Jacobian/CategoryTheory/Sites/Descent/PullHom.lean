import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Pullback of morphisms in a pseudofunctor

Pullback of morphisms respects composition, identities, isomorphisms and coherent iterated pullback.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe v' v u' u

namespace CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

open Opposite Bicategory

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

@[reassoc]
lemma pullHom_comp ⦃X₁ X₂ X₃ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃M₃ : F.obj (.mk (op X₃))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ ⦃f₃ : Y ⟶ X₃⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch)
    (hgf₃ : g ≫ f₃ = gf₃ := by cat_disch) :
    pullHom (φ ≫ ψ) g gf₁ gf₃ hgf₁ hgf₃ =
      pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫ pullHom ψ g gf₂ gf₃ hgf₂ hgf₃ := by
  simp [pullHom]

@[simp]
lemma pullHom_id_eq_id ⦃X₁ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) :
    pullHom (𝟙 ((F.map f₁.op.toLoc).toFunctor.obj M₁)) g gf₁ gf₁ hgf₁ hgf₁ = 𝟙 _ := by
  simp [pullHom]

instance isIso_pullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) [IsIso φ]
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    IsIso (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) :=
  ⟨pullHom (inv φ) g gf₂ gf₁ hgf₂ hgf₁, by
    rw [← pullHom_comp, IsIso.hom_inv_id, pullHom_id_eq_id], by
    rw [← pullHom_comp, IsIso.inv_hom_id, pullHom_id_eq_id]⟩

lemma pullHom_congr_left ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    {g g' : Y' ⟶ Y} (h : g = g') (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ = pullHom φ g' gf₁ gf₂ (h ▸ hgf₁) (h ▸ hgf₂) := by
  subst h
  rfl

/-- Pulling back the image `f₁^* a` of a morphism `a : M₁ ⟶ M₂` along `g` gives `(g ≫ f₁)^* a`. -/
@[simp]
lemma pullHom_map ⦃X₁ : C⦄ ⦃M₁ M₂ : F.obj (.mk (op X₁))⦄ (a : M₁ ⟶ M₂) ⦃Y : C⦄ (f₁ : Y ⟶ X₁)
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) :
    pullHom ((F.map f₁.op.toLoc).toFunctor.map a) g gf₁ gf₁ hgf₁ hgf₁ =
      (F.map gf₁.op.toLoc).toFunctor.map a := by
  simp [pullHom]

/-- The pullback `pullHom φ l (p₁ ≫ r₁) (p₂ ≫ r₂)` of a morphism `φ : w₁^* M₁ ⟶ w₂^* M₂` along
`l`, seen as a morphism `p₁^* (r₁^* M₁) ⟶ p₂^* (r₂^* M₂)` via the comparison isomorphisms
`(p₁ ≫ r₁)^* ≅ p₁^* r₁^*` and `(p₂ ≫ r₂)^* ≅ p₂^* r₂^*`.
The two squares commute (`hl₁`, `hl₂`):
```
         p₁        p₂
   X₁' ←──── Y ────→ X₂'
    │        │        │
 r₁ │        │ l      │ r₂
    ↓        ↓        ↓
   X₁ ←───── Z ─────→ X₂
         w₁        w₂
```
Compare `pullHom_mapComp'_conj`, which computes the pullback of a morphism conjugated by
`mapComp'`; here it is the pullback that is conjugated. -/
noncomputable def pullHomMapComp' ⦃X₁ X₂ Z : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃w₁ : Z ⟶ X₁⦄ ⦃w₂ : Z ⟶ X₂⦄
    (φ : (F.map w₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map w₂.op.toLoc).toFunctor.obj M₂)
    ⦃X₁' X₂' : C⦄ (r₁ : X₁' ⟶ X₁) (r₂ : X₂' ⟶ X₂) ⦃Y : C⦄ (l : Y ⟶ Z) (p₁ : Y ⟶ X₁')
    (p₂ : Y ⟶ X₂') (hl₁ : l ≫ w₁ = p₁ ≫ r₁) (hl₂ : l ≫ w₂ = p₂ ≫ r₂) :
    (F.map p₁.op.toLoc).toFunctor.obj ((F.map r₁.op.toLoc).toFunctor.obj M₁) ⟶
      (F.map p₂.op.toLoc).toFunctor.obj ((F.map r₂.op.toLoc).toFunctor.obj M₂) :=
  (F.mapComp' r₁.op.toLoc p₁.op.toLoc (p₁ ≫ r₁).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app M₁ ≫
    pullHom φ l (p₁ ≫ r₁) (p₂ ≫ r₂) hl₁ hl₂ ≫
    (F.mapComp' r₂.op.toLoc p₂.op.toLoc (p₂ ≫ r₂).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app M₂

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back `pullHomMapComp' φ r₁ r₂ l p₁ p₂` along `g` gives
`pullHomMapComp' φ r₁ r₂ (g ≫ l) (g ≫ p₁) (g ≫ p₂)`. -/
lemma pullHom_pullHomMapComp' ⦃X₁ X₂ Z : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃w₁ : Z ⟶ X₁⦄ ⦃w₂ : Z ⟶ X₂⦄
    (φ : (F.map w₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map w₂.op.toLoc).toFunctor.obj M₂)
    ⦃X₁' X₂' : C⦄ (r₁ : X₁' ⟶ X₁) (r₂ : X₂' ⟶ X₂) ⦃Y : C⦄ (l : Y ⟶ Z) (p₁ : Y ⟶ X₁')
    (p₂ : Y ⟶ X₂') (hl₁ : l ≫ w₁ = p₁ ≫ r₁) (hl₂ : l ≫ w₂ = p₂ ≫ r₂) ⦃Y' : C⦄ (g : Y' ⟶ Y)
    (gp₁ : Y' ⟶ X₁') (gp₂ : Y' ⟶ X₂') (hgp₁ : g ≫ p₁ = gp₁) (hgp₂ : g ≫ p₂ = gp₂)
    (gl : Y' ⟶ Z) (hgl : g ≫ l = gl) (hgl₁ : gl ≫ w₁ = gp₁ ≫ r₁)
    (hgl₂ : gl ≫ w₂ = gp₂ ≫ r₂) :
    pullHom (pullHomMapComp' φ r₁ r₂ l p₁ p₂ hl₁ hl₂) g gp₁ gp₂ hgp₁ hgp₂ =
      pullHomMapComp' φ r₁ r₂ gl gp₁ gp₂ hgl₁ hgl₂ := by
  subst hgp₁ hgp₂ hgl
  dsimp only [pullHomMapComp']
  rw [← pullHom_pullHom φ l (p₁ ≫ r₁) (p₂ ≫ r₂) g ((g ≫ p₁) ≫ r₁) ((g ≫ p₂) ≫ r₂) hl₁ hl₂
    (by simp) (by simp)]
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ _ _ (by cat_disch),
    mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _ _ _ _ _ (by cat_disch)]

end CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
