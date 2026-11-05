import Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Global sections of base changes of affine space

The polynomial coordinate map identifies the global sections of affine space
over an affine scheme with its polynomial ring. It commutes with base change.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite MvPolynomial

namespace AlgebraicGeometry

namespace AffineSpace

variable (n : Type u) {S T : Scheme.{u}}

/-- For `g : T ⟶ S`, the ring map `Γ(T)[n] ⟶ Γ(𝔸(n; S) ×[S] T)` sending a variable to the
pullback of the corresponding coordinate. It is an isomorphism when `T` is affine
(`AlgebraicGeometry.AffineSpace.toΓPullback_bijective`). -/
noncomputable def toΓPullback (g : T ⟶ S) :
    MvPolynomial n Γ(T, ⊤) →+* Γ(Limits.pullback (𝔸(n; S) ↘ S) g, ⊤) :=
  eval₂Hom (Limits.pullback.snd (𝔸(n; S) ↘ S) g).appTop.hom
    fun i ↦ (Limits.pullback.fst (𝔸(n; S) ↘ S) g).appTop (coord S i)

/-- Over an affine scheme `T`, the ring map `Γ(T)[n] ⟶ Γ(𝔸(n; S) ×[S] T)` is bijective: the
pullback is `𝔸(n; T) ≅ Spec Γ(T)[n]`. -/
theorem toΓPullback_bijective (g : T ⟶ S) [IsAffine T] :
    Function.Bijective (toΓPullback n g) := by
  let e := (isPullback_map (n := n) g).isoPullback
  have he : Function.Bijective e.hom.appTop :=
    ConcreteCategory.bijective_of_isIso _
  have key : e.hom.appTop.hom.comp (toΓPullback n g) =
      eval₂Hom (𝔸(n; T) ↘ T).appTop.hom (coord T) := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · simp [toΓPullback, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e]
    · simp [toΓPullback, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e]
  rw [← Function.Bijective.of_comp_iff' he, ← RingHom.coe_comp, key]
  have : eval₂Hom (𝔸(n; T) ↘ T).appTop.hom (coord T) =
      ((Scheme.ΓSpecIso _).inv ≫ (isoOfIsAffine n T).hom.appTop).hom := by
    rw [isoOfIsAffine_hom_appTop, Iso.inv_hom_id_assoc, CommRingCat.hom_ofHom]
  rw [this]
  exact ConcreteCategory.bijective_of_isIso _

/-- The ring maps `AlgebraicGeometry.AffineSpace.toΓPullback` are compatible with base change
along a morphism `h : T' ⟶ T` of schemes over `S`. -/
theorem appTop_pullbackMap_toΓPullback {T' : Scheme.{u}} (g : T ⟶ S) (g' : T' ⟶ S)
    (h : T' ⟶ T) (hh : h ≫ g = g') (p : MvPolynomial n Γ(T, ⊤)) :
    (Limits.pullback.map (𝔸(n; S) ↘ S) g' (𝔸(n; S) ↘ S) g (𝟙 _) h (𝟙 S) (by simp)
        (by simp [hh])).appTop (toΓPullback n g p) =
      toΓPullback n g' (MvPolynomial.map h.appTop.hom p) := by
  refine RingHom.congr_fun (f := RingHom.comp (CommRingCat.Hom.hom _) (toΓPullback n g))
    (g := (toΓPullback n g').comp (MvPolynomial.map h.appTop.hom)) ?_ p
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
  · simp only [toΓPullback, RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C,
      coe_eval₂Hom, eval₂_C]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, pullback.lift_snd]
  · simp only [toΓPullback, RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_X,
      coe_eval₂Hom, eval₂_X]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_fst,
      Category.comp_id]

end AffineSpace


end AlgebraicGeometry
