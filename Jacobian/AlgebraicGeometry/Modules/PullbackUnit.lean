import Jacobian.AlgebraicGeometry.Modules.PullbackSections
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.Tactic.IrreducibleDef

/-!
# Pullback units and coherent pullback of modules

The pullback adjunction units commute with composition and restriction. Their coherence gives the module pseudofunctor.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite CategoryTheory.Bicategory
  CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

open Scheme.Modules

/-- The pseudofunctor sending a scheme `X` to its category `X.Modules` of sheaves of
modules and a morphism to the pullback functor. This is the pseudofunctor underlying
`AlgebraicGeometry.Scheme.Modules.pseudofunctor`, which also records the pushforward
functors and the adjunctions; here we only keep the contravariant part, which is the
shape required by `CategoryTheory.Pseudofunctor.DescentData`. -/
noncomputable abbrev modulesPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Scheme.Modules.pseudofunctor.comp Adj.forget₁

variable {X Y Z : Scheme.{u}}

lemma modulesPseudofunctor_mapComp_hom_app (f : Y ⟶ X) (g : Z ⟶ Y) (M : X.Modules) :
    (modulesPseudofunctor.mapComp f.op.toLoc g.op.toLoc).hom.toNatTrans.app M =
      (pullbackComp g f).inv.app M :=
  rfl

lemma modulesPseudofunctor_mapComp_inv_app (f : Y ⟶ X) (g : Z ⟶ Y) (M : X.Modules) :
    (modulesPseudofunctor.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app M =
      (pullbackComp g f).hom.app M :=
  rfl

/-- The comparison `mapComp'` of `modulesPseudofunctor` on the image of the unit:

```
  Γ((g ≫ f)^* M) ─── mapComp'.hom ───▶ Γ(g^* f^* M)
        ▲                                   ▲
   η_(g ≫ f)                               η_g
        │                                   │
     Γ(M) ─────────────── η_f ─────────▶ Γ(f^* M)
``` -/
lemma modulesPseudofunctor_mapComp'_hom_app_pullbackUnit (f : Y ⟶ X) (g : Z ⟶ Y)
    (M : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    ((modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc).hom.toNatTrans.app
      M).app ((g ≫ f) ⁻¹ᵁ U) ((pullbackUnit (g ≫ f) M).app U m) =
      (pullbackUnit g ((pullback f).obj M)).app (f ⁻¹ᵁ U) ((pullbackUnit f M).app U m) := by
  have : modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc =
      modulesPseudofunctor.mapComp f.op.toLoc g.op.toLoc :=
    Pseudofunctor.mapComp'_eq_mapComp _ _ _
  rw [this, modulesPseudofunctor_mapComp_hom_app]
  exact pullbackUnit_comp_app_apply g f M U m

/-- `pullHom` of `modulesPseudofunctor` in terms of `pullbackComp`. -/
lemma modulesPseudofunctor_pullHom_eq {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules}
    {M₂ : X₂.Modules} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂) (g : Y' ⟶ Y) :
    pullHom (F := modulesPseudofunctor) φ g (g ≫ f₁) (g ≫ f₂) =
      (pullbackComp g f₁).inv.app M₁ ≫ (pullback g).map φ ≫ (pullbackComp g f₂).hom.app M₂ := by
  have h₁ : modulesPseudofunctor.mapComp' f₁.op.toLoc g.op.toLoc (g ≫ f₁).op.toLoc =
      modulesPseudofunctor.mapComp f₁.op.toLoc g.op.toLoc :=
    Pseudofunctor.mapComp'_eq_mapComp _ _ _
  have h₂ : modulesPseudofunctor.mapComp' f₂.op.toLoc g.op.toLoc (g ≫ f₂).op.toLoc =
      modulesPseudofunctor.mapComp f₂.op.toLoc g.op.toLoc :=
    Pseudofunctor.mapComp'_eq_mapComp _ _ _
  dsimp only [pullHom]
  rw [h₁, h₂]
  rfl

/-- The comparison `mapComp'` of `modulesPseudofunctor` on global sections in the image of the
unit, for a factorization `g ≫ f = fg`: the square of the previous lemma with `g ≫ f`
replaced by `fg`. -/
lemma modulesPseudofunctor_mapComp'_hom_app_top (f : Y ⟶ X) (g : Z ⟶ Y) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : X.Modules) (m : Γ(M, ⊤)) :
    ((modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
      (by rw [← h]; rfl)).hom.toNatTrans.app M).app ⊤ (pullbackUnitApp fg M ⊤ m) =
      pullbackUnitApp g ((pullback f).obj M) ⊤ (pullbackUnitApp f M ⊤ m) := by
  subst h
  exact modulesPseudofunctor_mapComp'_hom_app_pullbackUnit f g M ⊤ m

/-- The comparison `mapComp'` of `modulesPseudofunctor` on global sections in the image of the
unit, for a factorization `g ≫ f = fg`, inverse direction. -/
lemma modulesPseudofunctor_mapComp'_inv_app_top (f : Y ⟶ X) (g : Z ⟶ Y) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : X.Modules) (m : Γ(M, ⊤)) :
    ((modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
      (by rw [← h]; rfl)).inv.toNatTrans.app M).app ⊤
        (pullbackUnitApp g ((pullback f).obj M) ⊤ (pullbackUnitApp f M ⊤ m)) =
      pullbackUnitApp fg M ⊤ m := by
  rw [← modulesPseudofunctor_mapComp'_hom_app_top f g fg h M m]
  have k := Cat.Hom.hom_inv_id_toNatTrans_app (modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc
    fg.op.toLoc (by rw [← h]; rfl)) M
  exact congr(Hom.app (X := Z) $k ⊤ (pullbackUnitApp fg M ⊤ m))

/-- `pullbackComp` followed by `pullbackCongr`, for a factorization `g ≫ f = fg`:

```
  g^* f^* M ──(pullbackComp g f).app M──▶ (g ≫ f)^* M ──(pullbackCongr h).app M──▶ fg^* M
``` -/
noncomputable def pullbackCompOfEq (g : Z ⟶ Y) (f : Y ⟶ X) (fg : Z ⟶ X) (h : g ≫ f = fg)
    (M : X.Modules) : (pullback g).obj ((pullback f).obj M) ≅ (pullback fg).obj M :=
  (pullbackComp g f).app M ≪≫ (pullbackCongr h).app M

/-- The inverse comparison `mapComp'` of `modulesPseudofunctor` is `pullbackCompOfEq`:
`(mapComp' f g fg).inv.app M = (pullbackCompOfEq g f fg h M).hom : g^* f^* M ⟶ fg^* M`. -/
lemma modulesPseudofunctor_mapComp'_inv_app_eq (f : Y ⟶ X) (g : Z ⟶ Y) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : X.Modules) :
    (modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
      (by rw [← h]; rfl)).inv.toNatTrans.app M = (pullbackCompOfEq g f fg h M).hom := by
  subst h
  have : modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc =
      modulesPseudofunctor.mapComp f.op.toLoc g.op.toLoc :=
    Pseudofunctor.mapComp'_eq_mapComp _ _ _
  rw [this, modulesPseudofunctor_mapComp_inv_app]
  simp [pullbackCompOfEq, pullbackCongr]
  try rfl

/-- The comparison `mapComp'` of `modulesPseudofunctor` is the inverse of `pullbackCompOfEq`:
`(mapComp' f g fg).hom.app M = (pullbackCompOfEq g f fg h M).inv : fg^* M ⟶ g^* f^* M`. -/
lemma modulesPseudofunctor_mapComp'_hom_app_eq (f : Y ⟶ X) (g : Z ⟶ Y) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : X.Modules) :
    (modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
      (by rw [← h]; rfl)).hom.toNatTrans.app M = (pullbackCompOfEq g f fg h M).inv := by
  subst h
  have : modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc =
      modulesPseudofunctor.mapComp f.op.toLoc g.op.toLoc :=
    Pseudofunctor.mapComp'_eq_mapComp _ _ _
  rw [this, modulesPseudofunctor_mapComp_hom_app]
  simp [pullbackCompOfEq, pullbackCongr]
  try rfl

/-- `pullbackCompOfEq` on global sections in the image of the units:

```
  Γ(M) ──η_f──▶ Γ(f^* M) ──η_g──▶ Γ(g^* f^* M) ──pullbackCompOfEq──▶ Γ(fg^* M)
     └─────────────────────────── η_fg ──────────────────────────────────┘
``` -/
lemma pullbackCompOfEq_hom_app_top (g : Z ⟶ Y) (f : Y ⟶ X) (fg : Z ⟶ X) (h : g ≫ f = fg)
    (M : X.Modules) (m : Γ(M, ⊤)) :
    ((pullbackCompOfEq g f fg h M).hom).app ⊤
      (pullbackUnitApp g ((pullback f).obj M) ⊤ (pullbackUnitApp f M ⊤ m)) =
      pullbackUnitApp fg M ⊤ m := by
  rw [← modulesPseudofunctor_mapComp'_inv_app_eq f g fg h]
  exact modulesPseudofunctor_mapComp'_inv_app_top f g fg h M m

/-- Naturality of `pullbackΓ`: `(f^* φ) (η_f m) = η_f (φ m)`. -/
lemma pullbackΓ_naturality (f : Y ⟶ X) {M N : X.Modules} (φ : M ⟶ N) (m : Γ(M, ⊤)) :
    ((pullback f).map φ).app ⊤ (pullbackΓ f M m) = pullbackΓ f N (φ.app ⊤ m) := by
  rw [pullbackΓ_apply, pullbackΓ_apply]
  exact pullbackUnit_naturality_apply f φ ⊤ m

/-- `pullbackCompOfEq` on global sections in the image of the units, in terms of `pullbackΓ`:
`pullbackCompOfEq (η_g (η_f m)) = η_fg m`. -/
lemma pullbackCompOfEq_hom_app_pullbackΓ (g : Z ⟶ Y) (f : Y ⟶ X) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : X.Modules) (m : Γ(M, ⊤)) :
    ((pullbackCompOfEq g f fg h M).hom).app ⊤ (pullbackΓ g _ (pullbackΓ f M m)) =
      pullbackΓ fg M m := by
  rw [pullbackΓ_apply, pullbackΓ_apply, pullbackΓ_apply]
  exact pullbackCompOfEq_hom_app_top g f fg h M m

/-- The inverse of `pullbackCompOfEq` on global sections in the image of the units:
`(pullbackCompOfEq)⁻¹ (η_fg m) = η_g (η_f m)`. -/
lemma pullbackCompOfEq_inv_app_pullbackΓ (g : Z ⟶ Y) (f : Y ⟶ X) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : X.Modules) (m : Γ(M, ⊤)) :
    ((pullbackCompOfEq g f fg h M).inv).app ⊤ (pullbackΓ fg M m) =
      pullbackΓ g _ (pullbackΓ f M m) := by
  rw [← pullbackCompOfEq_hom_app_pullbackΓ g f fg h M m]
  exact congr($((pullbackCompOfEq g f fg h M).hom_inv_id).app ⊤ _)

end AlgebraicGeometry
