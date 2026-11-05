import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Coordinates on sections of finite free sheaves

The sections of a finite free module sheaf are the finite product of the sections of the coefficient sheaf.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v₁ u₁

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The `i`-th coordinate projection `free I ⟶ unit R` of a free sheaf of modules. -/
noncomputable def freeπ {I : Type u} [DecidableEq I] (i : I) : free (R := R) I ⟶ unit R :=
  Sigma.desc fun j ↦ if j = i then 𝟙 _ else 0

@[reassoc (attr := simp)]
lemma ιFree_freeπ {I : Type u} [DecidableEq I] (i j : I) :
    ιFree j ≫ (freeπ i : free (R := R) I ⟶ _) = if j = i then 𝟙 _ else 0 :=
  Sigma.ι_desc _ _

lemma free_hom_ext {I : Type u} {M : SheafOfModules.{u} R} {f g : free (R := R) I ⟶ M}
    (h : ∀ i, ιFree i ≫ f = ιFree i ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (isColimitFreeCofan I) _ _ h

lemma sum_freeπ_ιFree {I : Type u} [Fintype I] [DecidableEq I] :
    ∑ i : I, freeπ i ≫ ιFree i = 𝟙 (free (R := R) I) :=
  free_hom_ext fun j ↦ by
    rw [Preadditive.comp_sum, Finset.sum_eq_single j (fun i _ hi ↦ by simp [Ne.symm hi])
      (by simp)]
    simp

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
lemma sum_val_app_apply {M N : SheafOfModules.{u} R} {ι : Type*} (s : Finset ι)
    (φ : ι → (M ⟶ N)) (X : Cᵒᵖ) (x : M.val.obj X) :
    (∑ i ∈ s, φ i).val.app X x = ∑ i ∈ s, (φ i).val.app X x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/-- The sections of the free sheaf of modules `free I` of finite rank over `X` are `R(X)^I`. -/
noncomputable def freeSectionsLinearEquiv (I : Type u) [Fintype I] [DecidableEq I] (X : Cᵒᵖ) :
    (free (R := R) I).val.obj X ≃ₗ[R.obj.obj X] (I → R.obj.obj X) where
  toFun x i := (freeπ i).val.app X x
  map_add' x y := by ext i; exact map_add _ x y
  map_smul' a x := by ext i; exact ((freeπ i).val.app X).hom.map_smul a x
  invFun c := ∑ i, (ιFree (R := R) (I := I) i).val.app X (c i)
  left_inv x := by
    dsimp only
    simp_rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app, ← comp_val]
    rw [← sum_val_app_apply, sum_freeπ_ιFree]
    rfl
  right_inv c := by
    ext j
    dsimp only
    rw [map_sum, Finset.sum_eq_single j (fun i _ hi ↦ ?_) (by simp)]
    · change (ιFree j ≫ freeπ j).val.app X (c j) = c j
      rw [ιFree_freeπ, if_pos rfl]
      rfl
    · change (ιFree i ≫ freeπ j).val.app X (c i) = 0
      rw [ιFree_freeπ, if_neg hi]
      rfl

/-- An isomorphism `N ≅ free I` identifies the sections of `N` over `X` with `R(X)^I`. -/
noncomputable def sectionsLinearEquivOfIsoFree {N : SheafOfModules.{u} R} {I : Type u} [Fintype I]
    [DecidableEq I] (e : N ≅ free I) (X : Cᵒᵖ) :
    N.val.obj X ≃ₗ[R.obj.obj X] (I → R.obj.obj X) :=
  ((evaluation R X).mapIso e).toLinearEquiv.trans (freeSectionsLinearEquiv I X)

end SheafOfModules
