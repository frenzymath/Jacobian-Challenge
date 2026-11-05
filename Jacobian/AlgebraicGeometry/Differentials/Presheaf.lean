import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Sheaves.CommRingCat

/-!
# Inverse images of structure presheaves

A morphism of schemes induces a map from the presheaf inverse image of the
structure sheaf to the structure sheaf of the source. Its adjunction identity
expresses the usual maps on sections through this map of presheaves.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- `Spec` of a ring map acts on global sections by the ring map. -/
lemma specMap_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (φ r) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The presheaf inverse image `f⁻¹𝒪_S` of the structure sheaf of `S`, a presheaf of
commutative rings on `X`. -/
noncomputable abbrev pullbackPresheaf : TopCat.Presheaf CommRingCat.{u} X :=
  (TopCat.Presheaf.pullback CommRingCat f.base).obj S.presheaf

/-- The morphism `f⁻¹𝒪_S ⟶ 𝒪_X` of presheaves of commutative rings on `X`, the transpose of
`f♯ : 𝒪_S ⟶ f_*𝒪_X` under the adjunction `f⁻¹ ⊣ f_*`:
```
  𝒪_S ──f♯──▶ f_* 𝒪_X          (on S)
  ─────────────────────
  f⁻¹𝒪_S ─────▶ 𝒪_X            (on X)
```
-/
noncomputable def pullbackPresheafToPresheaf : f.pullbackPresheaf ⟶ X.presheaf :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).homEquiv _ _).symm f.c

/-- `f♯` is the adjunction unit followed by the pushforward of `f⁻¹𝒪_S ⟶ 𝒪_X`. -/
@[reassoc (attr := simp)]
lemma unit_app_comp_pushforward_map_pullbackPresheafToPresheaf :
    (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).unit.app S.presheaf ≫
      (TopCat.Presheaf.pushforward CommRingCat f.base).map f.pullbackPresheafToPresheaf = f.c :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- The map `f.appLE U V e : Γ(S, U) ⟶ Γ(X, V)` factors through `(f⁻¹𝒪_S)(V)`. -/
lemma appLE_eq_pullbackPresheafToPresheaf_app (U : S.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e =
      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).unit.app
          S.presheaf).app (Opposite.op U) ≫
        f.pullbackPresheaf.map (homOfLE e).op ≫
          f.pullbackPresheafToPresheaf.app (Opposite.op V) := by
  rw [f.pullbackPresheafToPresheaf.naturality, ← Category.assoc]
  have := NatTrans.congr_app f.unit_app_comp_pushforward_map_pullbackPresheafToPresheaf
    (Opposite.op U)
  rw [NatTrans.comp_app] at this
  erw [this]
  rfl

end AlgebraicGeometry.Scheme.Hom
