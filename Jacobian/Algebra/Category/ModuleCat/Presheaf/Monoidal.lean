import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Jacobian.Algebra.Category.ModuleCat.Presheaf.Generator

/-!
# Tensor products of presheaves of modules: free presheaves, and sections

Let `R` be a presheaf of commutative rings on a category `C`, and let `U` and `V` be two
objects of `C` which admit a binary product. The tensor product of the free presheaves of
modules on the Yoneda presheaves of `U` and of `V` is the free presheaf of modules on the
Yoneda presheaf of `U ⨯ V`: indeed, the Yoneda embedding turns the product into the product
of presheaves of types, and the free module functor is monoidal. Dually, the free presheaf of
modules on the Yoneda presheaf of a terminal object is the tensor unit.

In terms of universal sections (see
`Jacobian.Algebra.Category.ModuleCat.Presheaf.Generator`), this says that the
tensor product of two presheaves of modules which are free of rank one on a section over `U`,
resp. over `V`, is free of rank one over `U ⨯ V`.

## Main declarations

- `PresheafOfModules.freeYonedaProdIso` and
  `PresheafOfModules.IsUniversalSection.tensorObj`
- `PresheafOfModules.freeYonedaTerminalIso` and
  `PresheafOfModules.isUniversalSection_unit_one`

-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u u₁

open CategoryTheory MonoidalCategory Limits Opposite

namespace PresheafOfModules

variable {C : Type u₁} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}} (U V : C)
  [HasBinaryProduct U V]

set_option backward.isDefEq.respectTransparency false in
lemma tensorHom_app_tmul {M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})}
    (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (X : Cᵒᵖ) (m₁ : M₁.obj X) (m₃ : M₃.obj X) :
    (f ⊗ₘ g).app X (m₁ ⊗ₜ m₃) = f.app X m₁ ⊗ₜ g.app X m₃ := by
  exact ModuleCat.MonoidalCategory.tensorHom_tmul (f.app' X) (g.app' X) m₁ m₃

/-- The bijection between the morphisms to a binary product and the pairs of morphisms. -/
@[simps]
noncomputable def homProdEquiv (X : C) : (X ⟶ U ⨯ V) ≃ (X ⟶ U) × (X ⟶ V) where
  toFun f := (f ≫ prod.fst, f ≫ prod.snd)
  invFun p := prod.lift p.1 p.2
  left_inv _ := by apply prod.hom_ext <;> simp
  right_inv _ := by simp

set_option backward.isDefEq.respectTransparency false in
/-- The tensor product of the free presheaves of modules on the Yoneda presheaves of `U` and
of `V` is the free presheaf of modules on the Yoneda presheaf of `U ⨯ V`. -/
noncomputable def freeYonedaProdIso :
    (free (R ⋙ forget₂ CommRingCat RingCat.{u})).obj (yoneda.obj (U ⨯ V)) ≅
      (free (R ⋙ forget₂ CommRingCat RingCat.{u})).obj (yoneda.obj U) ⊗
        (free (R ⋙ forget₂ CommRingCat RingCat.{u})).obj (yoneda.obj V) :=
  PresheafOfModulesOfCommRing.isoMk (fun X ↦ (ModuleCat.free (R.obj X)).mapIso
      (homProdEquiv U V X.unop).toIso ≪≫
    (ModuleCat.FreeMonoidal.μIso (R.obj X) _ _).symm)
    (fun X Y f ↦ by
      refine ModuleCat.free_hom_ext (fun h ↦ ?_)
      dsimp
      erw [ModuleCat.freeDesc_apply]
      dsimp
      erw [ModuleCat.free_map_apply, ModuleCat.free_map_apply]
      erw [ModuleCat.FreeMonoidal.μIso_inv_freeMk, ModuleCat.FreeMonoidal.μIso_inv_freeMk]
      erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
      dsimp
      erw [ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
      simp)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma freeYonedaProdIso_hom_app_freeYonedaGen :
    (freeYonedaProdIso (R := R) U V).hom.app (op (U ⨯ V))
        (freeYonedaGen (R ⋙ forget₂ CommRingCat RingCat.{u}) (U ⨯ V)) =
      ModuleCat.freeMk (X := (yoneda.obj U).obj (op (U ⨯ V))) prod.fst ⊗ₜ
        ModuleCat.freeMk (X := (yoneda.obj V).obj (op (U ⨯ V))) prod.snd := by
  dsimp [freeYonedaProdIso, freeYonedaGen]
  erw [ConcreteCategory.comp_apply, ModuleCat.free_map_apply,
    ModuleCat.FreeMonoidal.μIso_inv_freeMk]
  simp

/-- The tensor product of the free presheaves of modules on the Yoneda presheaves of `U` and
of `V` is free of rank one on the tensor product of the two tautological sections over
`U ⨯ V`. -/
lemma isUniversalSection_freeYonedaProd :
    IsUniversalSection (M := (free (R ⋙ forget₂ CommRingCat RingCat.{u})).obj (yoneda.obj U) ⊗
        (free (R ⋙ forget₂ CommRingCat RingCat.{u})).obj (yoneda.obj V))
      (ModuleCat.freeMk (X := (yoneda.obj U).obj (op (U ⨯ V))) prod.fst ⊗ₜ
        ModuleCat.freeMk (X := (yoneda.obj V).obj (op (U ⨯ V))) prod.snd) := by
  rw [← freeYonedaProdIso_hom_app_freeYonedaGen]
  exact isUniversalSection_freeYonedaGen.of_iso _

section Terminal

variable (R) [HasTerminal C]

set_option backward.isDefEq.respectTransparency false in
/-- The free presheaf of modules on the Yoneda presheaf of a terminal object is the free
presheaf of modules of rank one. -/
noncomputable def freeYonedaTerminalIso :
    (free (R ⋙ forget₂ CommRingCat RingCat.{u})).obj (yoneda.obj (⊤_ C)) ≅
      unit (R ⋙ forget₂ CommRingCat RingCat.{u}) :=
  PresheafOfModulesOfCommRing.isoMk (fun X ↦ (ModuleCat.free (R.obj X)).mapIso
      (Equiv.equivPUnit.{u + 1} (X.unop ⟶ ⊤_ C)).toIso ≪≫
    (ModuleCat.FreeMonoidal.εIso (R.obj X)).symm)
    (fun X Y f ↦ by
      refine ModuleCat.free_hom_ext (fun h ↦ ?_)
      dsimp
      erw [ModuleCat.freeDesc_apply]
      dsimp
      erw [ModuleCat.free_map_apply,
        ModuleCat.FreeMonoidal.εIso_inv_freeMk, ModuleCat.free_map_apply,
        ModuleCat.FreeMonoidal.εIso_inv_freeMk]
      exact (R.map f).hom.map_one.symm)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma freeYonedaTerminalIso_hom_app_freeYonedaGen :
    (freeYonedaTerminalIso R).hom.app (op (⊤_ C))
        (freeYonedaGen (R ⋙ forget₂ CommRingCat RingCat.{u}) (⊤_ C)) =
      (1 : (R ⋙ forget₂ CommRingCat RingCat.{u}).obj (op (⊤_ C))) := by
  dsimp [freeYonedaTerminalIso, freeYonedaGen]
  erw [ConcreteCategory.comp_apply, ModuleCat.free_map_apply,
    ModuleCat.FreeMonoidal.εIso_inv_freeMk]

/-- The free presheaf of modules of rank one is free of rank one on the unit section over a
terminal object. -/
lemma isUniversalSection_unit_one :
    IsUniversalSection (M := unit (R ⋙ forget₂ CommRingCat RingCat.{u}))
      (show (unit (R ⋙ forget₂ CommRingCat RingCat.{u})).obj (op (⊤_ C)) from
        (1 : (R ⋙ forget₂ CommRingCat RingCat.{u}).obj (op (⊤_ C)))) := by
  rw [← freeYonedaTerminalIso_hom_app_freeYonedaGen R]
  exact isUniversalSection_freeYonedaGen.of_iso _

end Terminal

section

variable {U V}
variable {M M' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})}
  {m : M.obj (op U)} {m' : M'.obj (op V)}

/-- The tensor product of two presheaves of modules which are free of rank one on a section
over `U`, resp. over `V`, is free of rank one over `U ⨯ V`. -/
lemma IsUniversalSection.tensorObj (hm : IsUniversalSection m) (hm' : IsUniversalSection m')
    {x : M.obj (op (U ⨯ V))} {y : M'.obj (op (U ⨯ V))}
    (hx : x = M.map (Quiver.Hom.op (prod.fst : U ⨯ V ⟶ U)) m)
    (hy : y = M'.map (Quiver.Hom.op (prod.snd : U ⨯ V ⟶ V)) m') :
    IsUniversalSection (M := M ⊗ M') (x ⊗ₜ y) := by
  have h := (isUniversalSection_freeYonedaProd (R := R) U V).of_iso
    (MonoidalCategory.tensorIso hm.freeYonedaIso hm'.freeYonedaIso)
  convert h using 2
  have key : ∀ {N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u})} {W : C}
      {n : N.obj (op W)} (hn : IsUniversalSection n) (f : U ⨯ V ⟶ W),
      hn.freeYonedaIso.hom.app (op (U ⨯ V)) (ModuleCat.freeMk f) = N.map f.op n := by
    intro N W n hn f
    rw [← freeYoneda_map_freeYonedaGen (R := R ⋙ forget₂ CommRingCat RingCat.{u}) (X := W) f,
      naturality_apply, hn.freeYonedaIso_hom_app_freeYonedaGen]
    rfl
  rw [hx, hy, MonoidalCategory.tensorIso_hom]
  erw [tensorHom_app_tmul, key hm, key hm']

end

end PresheafOfModules
