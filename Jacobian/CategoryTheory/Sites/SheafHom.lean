import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Restriction of sections of `presheafHom`

A section `α` of `presheafHom F G` over `X` is compatible with restriction along a morphism
`h : Z ⟶ W.left` for `W : Over X`: restricting `α.app W` along `h` is the same as evaluating the
restriction of `α` to `Z` at `Over.mk (𝟙 Z)`.
-/


universe v v' u u'

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] {F G : Cᵒᵖ ⥤ A}

/-- For a section `α` of `presheafHom F G` over `X`, `W : Over X` and `h : Z ⟶ W.left`, the
square
```
  F(W.left) ---α_W---> G(W.left)
     |                     |
  F(h)                  G(h)
     v                     v
    F(Z) -----β------->  G(Z)
```
commutes, where `β` is the component at `Over.mk (𝟙 Z)` of the restriction of `α` along
`h ≫ W.hom`. -/
@[reassoc]
lemma presheafHom_app_comp_map {X : C} (α : (presheafHom F G).obj (op X)) (W : (Over X)ᵒᵖ)
    {Z : C} (h : Z ⟶ W.unop.left) :
    α.app W ≫ G.map h.op =
      F.map h.op ≫ ((presheafHom F G).map (h ≫ W.unop.hom).op α).app (op (Over.mk (𝟙 Z))) :=
  (α.naturality (Over.homMk h : Over.mk (h ≫ W.unop.hom) ⟶ W.unop).op).symm.trans
    (congrArg (F.map h.op ≫ ·) (presheafHom_map_app (𝟙 Z) _ _ (Category.id_comp _) α).symm)

end CategoryTheory
