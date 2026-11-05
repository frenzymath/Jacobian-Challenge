import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Pushforward and open restriction

In a cartesian square with an open immersion on the base, restriction of a pushforward is the pushforward of the restriction.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Direct images commute with restriction to open subschemes

Consider a cartesian square of schemes
```
X' --g'--> X
|          |
f'         f
v          v
T' --g---> T
```
in which `g` (hence `g'`) is an open immersion. For an `𝒪_X`-module `M` the restriction of the
direct image `(f_* M)|_{T'}` is the direct image `f'_* (M|_{X'})`: over an open `V` of `T'` both
sides are the sections of `M` over `f⁻¹(g(V)) = g'(f'⁻¹(V))`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.pushforwardRestrictHom`: the base change morphism
  `(f_* M)|_{T'} ⟶ f'_* (M|_{X'})` of a commutative square of schemes.
- `AlgebraicGeometry.Scheme.Modules.pushforwardRestrictIso`: the natural isomorphism
  `(f_* M)|_{T'} ≅ f'_* (M|_{X'})`.
-/

section
universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X T T' X' : Scheme.{u}} (f : X ⟶ T) (g : T' ⟶ T) [IsOpenImmersion g] (g' : X' ⟶ X)
  (f' : X' ⟶ T')

/-- A restriction map of an `𝒪`-module between equal opens is an isomorphism. -/
lemma isIso_presheaf_map_of_le {Z : Scheme.{u}} (M : Z.Modules) {A B : Z.Opens} (h : A ⟶ B)
    (h' : B ≤ A) : IsIso (M.presheaf.map h.op) := by
  obtain rfl : A = B := le_antisymm (leOfHom h) h'
  rw [Subsingleton.elim h (𝟙 _), op_id, M.presheaf.map_id]
  infer_instance

variable [IsOpenImmersion g']

/-- The base change morphism `(f_* M)|_{T'} ⟶ f'_* (M|_{X'})` for a commutative square
`g' ≫ f = f' ≫ g` of schemes with `g` and `g'` open immersions. It is adjoint to the direct
image under `f` of the unit `M ⟶ g'_* (M|_{X'})`. -/
noncomputable def pushforwardRestrictHom (w : g' ≫ f = f' ≫ g) :
    pushforward f ⋙ restrictFunctor g ⟶ restrictFunctor g' ⋙ pushforward f' :=
  Functor.whiskerRight (Functor.whiskerRight (restrictAdjunction g').unit (pushforward f) ≫
      Functor.whiskerLeft (restrictFunctor g') ((pushforwardComp g' f).hom ≫
        (pushforwardCongr w).hom ≫ (pushforwardComp f' g).inv)) (restrictFunctor g) ≫
    Functor.whiskerLeft (restrictFunctor g' ⋙ pushforward f') (restrictAdjunction g).counit

/-- On an open `V` of `T'` the base change morphism is the restriction map of `M` from
`f⁻¹(g(V))` to `g'(g'⁻¹(f⁻¹(g(V))))` followed by isomorphisms, hence is an isomorphism as soon as
`f⁻¹(g(V)) ⊆ g'(f'⁻¹(V))`. -/
lemma isIso_pushforwardRestrictHom_app_app (w : g' ≫ f = f' ≫ g) (M : X.Modules) (V : T'.Opens)
    (hV : f ⁻¹ᵁ g ''ᵁ V ≤ g' ''ᵁ f' ⁻¹ᵁ V) :
    IsIso (((pushforwardRestrictHom f g g' f' w).app M).app V) := by
  simp only [Functor.comp_obj, pushforward_obj_obj, pushforwardRestrictHom,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Functor.whiskerRight_twice,
    Category.assoc, NatTrans.comp_app, Functor.id_obj, Functor.associator_hom_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Category.id_comp, Hom.comp_app, restrictAdjunction_counit_app_app,
    eqToHom_op, isIso_comp_right_iff]
  change IsIso (((restrictAdjunction g').unit.app M).app (f ⁻¹ᵁ g ''ᵁ V))
  rw [restrictAdjunction_unit_app_app]
  refine isIso_presheaf_map_of_le M _ ?_
  rw [g'.image_preimage_eq_opensRange_inf]
  exact le_inf (hV.trans (g'.image_le_opensRange _)) le_rfl

variable {f g g' f'}

/-- **Direct images commute with restriction to an open subscheme of the base.** For a cartesian
square `sq` with `g` an open immersion, `(f_* M)|_{T'} ≅ f'_* (M|_{X'})` naturally in `M`. -/
noncomputable def pushforwardRestrictIso (sq : IsPullback g' f' f g) :
    pushforward f ⋙ restrictFunctor g ≅ restrictFunctor g' ⋙ pushforward f' :=
  have : ∀ M, IsIso ((pushforwardRestrictHom f g g' f' sq.w).app M) := fun M ↦ by
    have : ∀ V, IsIso (((toPresheaf T').map ((pushforwardRestrictHom f g g' f' sq.w).app M)).app
        V) := fun V ↦ isIso_pushforwardRestrictHom_app_app f g g' f' sq.w M V.unop
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq.flip V.unop).ge
    have := NatIso.isIso_of_isIso_app ((toPresheaf T').map
      ((pushforwardRestrictHom f g g' f' sq.w).app M))
    exact isIso_of_reflects_iso _ (toPresheaf T')
  have := NatIso.isIso_of_isIso_app (pushforwardRestrictHom f g g' f' sq.w)
  asIso (pushforwardRestrictHom f g g' f' sq.w)

end AlgebraicGeometry.Scheme.Modules
