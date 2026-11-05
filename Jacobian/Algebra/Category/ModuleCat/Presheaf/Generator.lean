import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator

/-!
# Universal sections of a presheaf of modules

Let `R` be a presheaf of rings on a category `C`. A section `m` of a presheaf of `R`-modules
`M` over an object `Z` is *universal* if for every presheaf of `R`-modules `N`, the map which
sends a morphism `M ⟶ N` to the image of `m` is bijective: in other words, `M` is free of rank
one on the section `m`. The basic example is the free presheaf of modules on a Yoneda presheaf,
with its tautological section.

Two presheaves of modules with universal sections over the same object are canonically
isomorphic; this is used to recognize isomorphisms, see
`PresheafOfModules.IsUniversalSection.isIso`.

We also record an induction principle for presheaves of modules: a natural transformation
between two colimit-preserving functors out of the category of presheaves of modules is an
isomorphism as soon as it is one on the free presheaves of modules on Yoneda presheaves.

## Main declarations

- `PresheafOfModules.IsUniversalSection`
- `PresheafOfModules.IsUniversalSection.isIso`
- `PresheafOfModules.isIso_app_of_freeYoneda`

-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁

open CategoryTheory Limits Opposite

namespace PresheafOfModules

variable {C : Type u₁} [Category.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

section

variable {X : C}

variable (R X) in
/-- The tautological section of the free presheaf of modules on a Yoneda presheaf. -/
noncomputable def freeYonedaGen : ((free R).obj (yoneda.obj X)).obj (op X) :=
  ModuleCat.freeMk (𝟙 X)

lemma freeYonedaEquiv_apply {M : PresheafOfModules.{u} R} (m : (free R).obj (yoneda.obj X) ⟶ M) :
    freeYonedaEquiv m = m.app (op X) (freeYonedaGen R X) := by
  have h := freeYonedaEquiv_symm_app M X (freeYonedaEquiv m)
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma freeYoneda_map_freeYonedaGen {Y : C} (f : Y ⟶ X) :
    (show ((free R).obj (yoneda.obj X)).obj (op Y) from
      ((free R).obj (yoneda.obj X)).map (op f) (freeYonedaGen R X)) = ModuleCat.freeMk f := by
  dsimp [freeYonedaGen]
  erw [ModuleCat.freeDesc_apply]
  simp


end

section

variable {M N : PresheafOfModules.{u} R} {Z : Cᵒᵖ}

/-- A section `m` of a presheaf of modules `M` over an object `Z` is *universal* if `M` is
free of rank one on `m`, i.e. if for every presheaf of modules `N`, a morphism `M ⟶ N` is
uniquely determined by the image of `m`, which may be an arbitrary section of `N` over `Z`. -/
def IsUniversalSection (m : M.obj Z) : Prop :=
  ∀ (N : PresheafOfModules.{u} R), Function.Bijective fun (g : M ⟶ N) ↦ g.app Z m

namespace IsUniversalSection

variable {m : M.obj Z} {n : N.obj Z}

/-- A universal section is transported along an isomorphism. -/
lemma of_iso (hm : IsUniversalSection m) (e : M ≅ N) :
    IsUniversalSection (e.hom.app Z m) := fun P ↦ by
  have : (fun (g : N ⟶ P) ↦ g.app Z (e.hom.app Z m)) =
      (fun (g : M ⟶ P) ↦ g.app Z m) ∘ fun (g : N ⟶ P) ↦ e.hom ≫ g := by
    funext g
    exact (ConcreteCategory.congr_hom (comp_app e.hom g Z) m).symm
  rw [this]
  exact (hm P).comp ((Iso.homCongr e (Iso.refl P)).symm.bijective.comp
    (Equiv.refl _).bijective)

/-- A morphism which sends a universal section to a universal section is an isomorphism. -/
lemma isIso (hm : IsUniversalSection m) (hn : IsUniversalSection n) (w : M ⟶ N)
    (hw : w.app Z m = n) : IsIso w := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro P
  have : (fun (g : N ⟶ P) ↦ w ≫ g) =
      fun (g : N ⟶ P) ↦ (Equiv.ofBijective _ (hm P)).symm (g.app Z n) := by
    funext g
    refine (Equiv.ofBijective _ (hm P)).injective ?_
    rw [Equiv.apply_symm_apply]
    change (w ≫ g).app Z m = g.app Z n
    rw [ConcreteCategory.congr_hom (comp_app w g Z) m]
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, hw]
  exact this ▸ (Equiv.ofBijective _ (hm P)).symm.bijective.comp (hn P)

/-- A universal section restricts to a universal section along an isomorphism. -/
lemma map {Z' : Cᵒᵖ} (hm : IsUniversalSection m) (α : Z ⟶ Z') [IsIso α] :
    IsUniversalSection (show M.obj Z' from M.map α m) := fun P ↦ by
  have hbij : ∀ (Q : PresheafOfModules.{u} R),
      Function.Bijective (fun x : Q.obj Z ↦ (show Q.obj Z' from Q.map α x)) := by
    intro Q
    have : IsIso (Q.presheaf.map α) := Q.presheaf.map_isIso α
    exact ConcreteCategory.bijective_of_isIso (Q.presheaf.map α)
  have : (fun (g : M ⟶ P) ↦ g.app Z' (show M.obj Z' from M.map α m)) =
      fun (g : M ⟶ P) ↦ (show P.obj Z' from P.map α (g.app Z m)) := by
    funext g
    exact naturality_apply g α m
  rw [this]
  exact (hbij P).comp (hm P)

end IsUniversalSection

end

section

variable {X : C}

lemma isUniversalSection_freeYonedaGen :
    IsUniversalSection (freeYonedaGen R X) := fun N ↦ by
  have : (fun (g : (free R).obj (yoneda.obj X) ⟶ N) ↦ g.app (op X) (freeYonedaGen R X)) =
      freeYonedaEquiv := by
    funext g
    exact (freeYonedaEquiv_apply g).symm
  rw [this]
  exact freeYonedaEquiv.bijective


/-- The isomorphism from the free presheaf of modules on a Yoneda presheaf determined by a
universal section. -/
noncomputable def IsUniversalSection.freeYonedaIso {M : PresheafOfModules.{u} R}
    {m : M.obj (op X)} (hm : IsUniversalSection m) : (free R).obj (yoneda.obj X) ≅ M :=
  have : IsIso (freeYonedaEquiv.symm m) :=
    isUniversalSection_freeYonedaGen.isIso hm _ (freeYonedaEquiv_symm_app M X m)
  asIso (freeYonedaEquiv.symm m)

@[simp]
lemma IsUniversalSection.freeYonedaIso_hom_app_freeYonedaGen {M : PresheafOfModules.{u} R}
    {m : M.obj (op X)} (hm : IsUniversalSection m) :
    hm.freeYonedaIso.hom.app (op X) (freeYonedaGen R X) = m :=
  freeYonedaEquiv_symm_app M X m
end

section Induction

variable {C : Type u} [SmallCategory C] {S : Cᵒᵖ ⥤ RingCat.{u}}
  {E : Type*} [Category* E] {Φ Ψ : PresheafOfModules.{u} S ⥤ E} (α : Φ ⟶ Ψ)
  [PreservesColimitsOfSize.{u, u} Φ] [PreservesColimitsOfSize.{u, u} Ψ]

include α in
/-- A natural transformation between two colimit-preserving functors out of the category of
presheaves of modules is an isomorphism as soon as it is one on the free presheaves of modules
on Yoneda presheaves: indeed, any presheaf of modules is a cokernel of a morphism between
coproducts of such. -/
lemma isIso_app_of_freeYoneda
    (h : ∀ X : C, IsIso (α.app ((free S).obj (yoneda.obj X)))) (M : PresheafOfModules.{u} S) :
    IsIso (α.app M) := by
  have h₁ : PreservesColimitsOfSize.{0, 0} Φ := preservesColimitsOfSize_shrink.{0, u, 0, u} Φ
  have h₂ : PreservesColimitsOfSize.{0, 0} Ψ := preservesColimitsOfSize_shrink.{0, u, 0, u} Ψ
  have hcop : ∀ (N : PresheafOfModules.{u} S), IsIso (α.app N.freeYonedaCoproduct) := fun N ↦ by
    let K := Discrete.functor (Elements.freeYoneda (M := N))
    have : ∀ j, IsIso ((Functor.whiskerLeft K α).app j) := fun _ ↦ h _
    have : IsIso (Functor.whiskerLeft K α) := NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit K α _ (colimit.isColimit K)
  let K := parallelPair M.toFreeYonedaCoproduct 0
  have : ∀ j, IsIso ((Functor.whiskerLeft K α).app j) := fun j ↦ by
    obtain (_ | _) := j <;> apply hcop
  have : IsIso (Functor.whiskerLeft K α) := NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit K α _ M.isColimitFreeYonedaCoproductsCokernelCofork

end Induction

end PresheafOfModules
