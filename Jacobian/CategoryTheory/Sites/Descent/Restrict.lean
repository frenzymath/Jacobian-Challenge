import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Restriction of descent data

Descent data restrict along a change of base and a compatible family of morphisms.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Bicategory

namespace CategoryTheory.Pseudofunctor.DescentData

variable {C : Type*} [Category* C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat}
  {ι : Type*} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- The restriction of a descent datum `D` relative to `f` along `p : S' ⟶ S`, to a family
`f' j : X (β j) ⟶ S'` with `f' j ≫ p = f (β j)`: the objects are those of `D`, and the
comparison morphisms over `q : Y ⟶ S'` are those of `D` over `q ≫ p`. -/
@[simps]
def restrict (D : F.DescentData f) {S' : C} (p : S' ⟶ S) {ι' : Type*} (β : ι' → ι)
    (f' : ∀ j, X (β j) ⟶ S') (h : ∀ j, f' j ≫ p = f (β j)) : F.DescentData f' where
  obj j := D.obj (β j)
  hom Y q j₁ j₂ f₁ f₂ hf₁ hf₂ := D.hom (q ≫ p) f₁ f₂ (by rw [← h, ← hf₁, Category.assoc])
    (by rw [← h, ← hf₂, Category.assoc])
  pullHom_hom Y' Y g q q' hq j₁ j₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    D.pullHom_hom g (q ≫ p) (q' ≫ p) (by rw [← hq, Category.assoc]) f₁ f₂
      (by rw [← h, ← hf₁, Category.assoc]) (by rw [← h, ← hf₂, Category.assoc]) gf₁ gf₂ hgf₁ hgf₂
  hom_self Y q j g hg := D.hom_self _ _ (by rw [← h, ← hg, Category.assoc])
  hom_comp Y q j₁ j₂ j₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := D.hom_comp _ _ _ _
    (by rw [← h, ← hf₁, Category.assoc]) (by rw [← h, ← hf₂, Category.assoc])
    (by rw [← h, ← hf₃, Category.assoc])

/-- A morphism of descent data whose components are isomorphisms is an isomorphism. -/
lemma isIso_of_isIso_hom {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂) [∀ i, IsIso (φ.hom i)] :
    IsIso φ :=
  (isoMk (fun i ↦ asIso (φ.hom i)) (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ φ.comm q f₁ f₂ hf₁ hf₂)).isIso_hom

end CategoryTheory.Pseudofunctor.DescentData
