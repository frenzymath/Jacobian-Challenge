import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
import Jacobian.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Jacobian.Algebra.Category.ModuleCat.Presheaf.PushforwardMonoidal

/-!
# The pullback of presheaves of modules is monoidal

Let `F : C ⥤ D` be a functor, `R : Dᵒᵖ ⥤ CommRingCat` and `S : Cᵒᵖ ⥤ CommRingCat` presheaves
of commutative rings, and `φ : S ⋙ forget₂ _ _ ⟶ (F.op ⋙ R) ⋙ forget₂ _ _` a morphism of the
underlying presheaves of rings. When `PresheafOfModules.pushforward φ` has a left adjoint,
`PresheafOfModules.pullback φ` is oplax monoidal, as the left adjoint of a lax monoidal
functor.

We show that its two structure maps are isomorphisms as soon as `F` preserves finite products,
so that `pullback φ` is then monoidal. The pullback functor is a left Kan extension, hence
preserves colimits, and both sides of the comparison
`pullback φ (M ⊗ N) ⟶ pullback φ M ⊗ pullback φ N` preserve colimits in each variable; as any
presheaf of modules is a cokernel of a morphism between coproducts of free presheaves of
modules on Yoneda presheaves, it is enough to treat the case of
`M = (free S).obj (yoneda.obj U)` and `N = (free S).obj (yoneda.obj V)`. There the tensor
product is the free presheaf of modules on `yoneda.obj (U ⨯ V)`, and the pullback sends the
free presheaf of modules on `yoneda.obj W` to the free presheaf of modules on
`yoneda.obj (F.obj W)`, so the comparison is an isomorphism because `F.obj (U ⨯ V)` is the
product of `F.obj U` and `F.obj V`. The unit is treated in the same way, `𝟙_` being the free
presheaf of modules on the Yoneda presheaf of a terminal object.

## Main declarations

* `PresheafOfModules.pullbackOplaxMonoidal`: `pullback φ` is oplax monoidal.
* `PresheafOfModules.pullbackOfCommRingCat`: the pullback functor, with the arguments spelled
  out so that the monoidal structures on both sides are found by instance resolution.
* `PresheafOfModules.isIso_δ_pullbackOfCommRingCat` and
  `PresheafOfModules.isIso_η_pullbackOfCommRingCat`: the structure maps are isomorphisms.
* `PresheafOfModules.pullbackMonoidal`: `pullback φ` is monoidal.

-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory Limits Opposite

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⋙ forget₂ CommRingCat RingCat ⟶ (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)

/-- When it exists, the pullback of presheaves of modules along `φ` is oplax monoidal, being
the left adjoint of the lax monoidal functor `pushforward φ`. Using this entry point makes
`pullbackPushforwardAdjunction φ` a monoidal adjunction. -/
noncomputable instance pullbackOplaxMonoidal
    [(pushforward.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
      (S := S ⋙ forget₂ CommRingCat RingCat) φ).IsRightAdjoint] :
    (pullback.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
      (S := S ⋙ forget₂ CommRingCat RingCat) φ).OplaxMonoidal :=
  (pullbackPushforwardAdjunction.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
    (S := S ⋙ forget₂ CommRingCat RingCat) φ).leftAdjointOplaxMonoidal

section FreeYoneda

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R) (W : C)

/-- The tautological section over `F.obj W` of the pullback along `φ` of the free presheaf of
modules on the Yoneda presheaf of `W`. -/
noncomputable def pullbackFreeYonedaGen :
    ((pullback.{u} φ).obj ((free S).obj (yoneda.obj W))).obj (op (F.obj W)) :=
  ((pullbackPushforwardAdjunction.{u} φ).unit.app ((free S).obj (yoneda.obj W))).app (op W)
    (freeYonedaGen S W)

variable {W} in
/-- A morphism out of the pullback of a free presheaf of modules on a Yoneda presheaf is
determined by the image of the tautological section. -/
lemma app_pullbackFreeYonedaGen {N : PresheafOfModules.{u} R}
    (g : (pullback.{u} φ).obj ((free S).obj (yoneda.obj W)) ⟶ N) :
    g.app (op (F.obj W)) (pullbackFreeYonedaGen φ W) =
      freeYonedaEquiv ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ g) := by
  rw [freeYonedaEquiv_apply, Adjunction.homEquiv_unit, comp_app]
  rfl

/-- The pullback of a free presheaf of modules on a Yoneda presheaf is again free of rank one,
on the tautological section over the image object. -/
lemma isUniversalSection_pullbackFreeYonedaGen :
    IsUniversalSection (pullbackFreeYonedaGen φ W) := by
  intro N
  have h : (fun (g : (pullback.{u} φ).obj ((free S).obj (yoneda.obj W)) ⟶ N) ↦
        g.app (op (F.obj W)) (pullbackFreeYonedaGen φ W)) =
      fun g ↦ freeYonedaEquiv ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ g) :=
    funext fun g ↦ app_pullbackFreeYonedaGen φ g
  rw [h]
  exact freeYonedaEquiv.bijective.comp (Equiv.bijective _)

end FreeYoneda

section Monoidal

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⋙ forget₂ CommRingCat RingCat ⟶ (F.op ⋙ R) ⋙ forget₂ CommRingCat RingCat)

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The pushforward functor on presheaves of modules over the underlying presheaves of rings of
presheaves of commutative rings. This is `PresheafOfModules.pushforward` with its arguments
spelled out, so that the monoidal structures on both sides are found by instance resolution. -/
noncomputable abbrev pushforwardOfCommRingCat :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u}) ⥤
      PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat.{u}) :=
  pushforward.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
    (S := S ⋙ forget₂ CommRingCat RingCat) φ

/-- The pullback functor on presheaves of modules over the underlying presheaves of rings of
presheaves of commutative rings. This is `PresheafOfModules.pullback` with its arguments
spelled out, so that the monoidal structures on both sides are found by instance resolution. -/
noncomputable abbrev pullbackOfCommRingCat :
    PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat.{u}) ⥤
      PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat.{u}) :=
  pullback.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
    (S := S ⋙ forget₂ CommRingCat RingCat) φ

/-- The adjunction between `PresheafOfModules.pullbackOfCommRingCat` and
`PresheafOfModules.pushforwardOfCommRingCat`. -/
noncomputable abbrev adjunctionOfCommRingCat :
    pullbackOfCommRingCat φ ⊣ pushforwardOfCommRingCat φ :=
  pullbackPushforwardAdjunction.{u} (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
    (S := S ⋙ forget₂ CommRingCat RingCat) φ

instance : (pullbackOfCommRingCat φ).IsLeftAdjoint :=
  (adjunctionOfCommRingCat φ).isLeftAdjoint

lemma adjunctionOfCommRingCat_homEquiv_δ
    (M N : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    (adjunctionOfCommRingCat φ).homEquiv _ _ (δ (pullbackOfCommRingCat φ) M N) =
      ((adjunctionOfCommRingCat φ).unit.app M ⊗ₘ (adjunctionOfCommRingCat φ).unit.app N) ≫
        μ (pushforwardOfCommRingCat φ) _ _ :=
  Equiv.apply_symm_apply _ _

lemma adjunctionOfCommRingCat_homEquiv_η :
    (adjunctionOfCommRingCat φ).homEquiv _ _ (η (pullbackOfCommRingCat φ)) =
      ε (pushforwardOfCommRingCat φ) :=
  Equiv.apply_symm_apply _ _

variable (U V : C) [HasBinaryProducts C] [PreservesLimitsOfShape (Discrete WalkingPair) F]

/-- The pullback of presheaves of modules turns the tensor product of two free presheaves of
modules on Yoneda presheaves into the tensor product of their pullbacks. -/
lemma isIso_δ_freeYoneda :
    IsIso (δ (pullbackOfCommRingCat φ)
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj U))
      ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj V))) := by
  have hU := isUniversalSection_pullbackFreeYonedaGen
    (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
    (S := S ⋙ forget₂ CommRingCat RingCat) φ U
  have hV := isUniversalSection_pullbackFreeYonedaGen
    (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
    (S := S ⋙ forget₂ CommRingCat RingCat) φ V
  have hW := isUniversalSection_pullbackFreeYonedaGen
    (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
    (S := S ⋙ forget₂ CommRingCat RingCat) φ (U ⨯ V)
  have h1 := hW.of_iso ((pullbackOfCommRingCat φ).mapIso (freeYonedaProdIso (R := S) U V))
  have h2 := (hU.tensorObj hV rfl rfl).map (prodComparison F U V).op
  refine h1.isIso h2 _ ?_
  have key := app_pullbackFreeYonedaGen (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
    (S := S ⋙ forget₂ CommRingCat RingCat) φ
    ((pullbackOfCommRingCat φ).map (freeYonedaProdIso (R := S) U V).hom ≫
      δ (pullbackOfCommRingCat φ) _ _)
  rw [ConcreteCategory.congr_hom (comp_app _ _ _) _] at key
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at key
  rw [Functor.mapIso_hom, key, Adjunction.homEquiv_naturality_left, freeYonedaEquiv_comp,
    freeYonedaEquiv_apply, freeYonedaProdIso_hom_app_freeYonedaGen,
    adjunctionOfCommRingCat_homEquiv_δ, ConcreteCategory.congr_hom (comp_app _ _ _) _]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  erw [tensorHom_app_tmul, pushforward_μ_app_tmul, Monoidal.tensorObj_map_tmul,
    ← map_comp_apply, ← map_comp_apply, ← op_comp, ← op_comp, prodComparison_fst,
    prodComparison_snd, ← freeYoneda_map_freeYonedaGen (R := S ⋙ forget₂ CommRingCat RingCat)
      (X := U) (prod.fst : U ⨯ V ⟶ U),
    ← freeYoneda_map_freeYonedaGen (R := S ⋙ forget₂ CommRingCat RingCat)
      (X := V) (prod.snd : U ⨯ V ⟶ V),
    naturality_apply, naturality_apply]
  simp only [pullbackFreeYonedaGen, Functor.comp_obj]
  rfl

variable {U V}

/-- The cotensorator of the pullback functor, as a natural transformation in the first
variable. -/
@[simps]
noncomputable def δNatTransLeft (N : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    MonoidalCategory.tensorRight N ⋙ pullbackOfCommRingCat φ ⟶
      pullbackOfCommRingCat φ ⋙
        MonoidalCategory.tensorRight ((pullbackOfCommRingCat φ).obj N) where
  app M := δ (pullbackOfCommRingCat φ) M N
  naturality _ _ f := (δ_natural_left _ f N).symm

/-- The cotensorator of the pullback functor, as a natural transformation in the second
variable. -/
@[simps]
noncomputable def δNatTransRight (M : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    MonoidalCategory.tensorLeft M ⋙ pullbackOfCommRingCat φ ⟶
      pullbackOfCommRingCat φ ⋙
        MonoidalCategory.tensorLeft ((pullbackOfCommRingCat φ).obj M) where
  app N := δ (pullbackOfCommRingCat φ) M N
  naturality _ _ f := (δ_natural_right _ M f).symm

/-- The cotensorator of the pullback functor of presheaves of modules is an isomorphism, as
soon as the underlying functor between the two categories preserves binary products:
```
δ M N : f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N
```
-/
instance isIso_δ_pullbackOfCommRingCat
    (M N : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :
    IsIso (δ (pullbackOfCommRingCat φ) M N) := by
  have h : ∀ (W : C) (M' : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)),
      IsIso (δ (pullbackOfCommRingCat φ) M'
        ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj W))) := fun W ↦
    isIso_app_of_freeYoneda
      (δNatTransLeft φ ((free (S ⋙ forget₂ CommRingCat RingCat)).obj (yoneda.obj W)))
      (fun U ↦ isIso_δ_freeYoneda φ U W)
  exact isIso_app_of_freeYoneda (δNatTransRight φ M) (fun W ↦ h W M) N

/-- The counit of the pullback functor of presheaves of modules is an isomorphism, as soon as
the underlying functor between the two categories preserves the terminal object:
```
η : f^*(𝟙_) ⟶ 𝟙_
```
-/
instance isIso_η_pullbackOfCommRingCat [HasTerminal C] [HasTerminal D]
    [PreservesLimitsOfShape (Discrete PEmpty.{1}) F] :
    IsIso (η (pullbackOfCommRingCat φ)) := by
  have hT := isUniversalSection_pullbackFreeYonedaGen (F := F)
    (R := R ⋙ forget₂ CommRingCat RingCat) (S := S ⋙ forget₂ CommRingCat RingCat) φ (⊤_ C)
  have h1 := hT.of_iso ((pullbackOfCommRingCat φ).mapIso (freeYonedaTerminalIso S))
  have h2 : IsUniversalSection (M := unit (R ⋙ forget₂ CommRingCat RingCat))
      (show (unit (R ⋙ forget₂ CommRingCat RingCat)).obj (op (F.obj (⊤_ C))) from
        (1 : (R ⋙ forget₂ CommRingCat RingCat).obj (op (F.obj (⊤_ C))))) := by
    have h := (isUniversalSection_unit_one R).map (terminalComparison F).op
    rwa [unit_map_one] at h
  refine h1.isIso h2 _ ?_
  have key := app_pullbackFreeYonedaGen (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
    (S := S ⋙ forget₂ CommRingCat RingCat) φ
    ((pullbackOfCommRingCat φ).map (freeYonedaTerminalIso S).hom ≫ η (pullbackOfCommRingCat φ))
  rw [ConcreteCategory.congr_hom (comp_app _ _ _) _] at key
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at key
  rw [Functor.mapIso_hom]
  erw [key]
  rw [Adjunction.homEquiv_naturality_left, freeYonedaEquiv_comp,
    freeYonedaEquiv_apply, freeYonedaTerminalIso_hom_app_freeYonedaGen]
  erw [adjunctionOfCommRingCat_homEquiv_η, pushforward_ε_app, ModuleCat.restrictScalars_η]
  exact map_one (φ.app (op (⊤_ C))).hom

/-- The pullback functor between categories of presheaves of modules is monoidal, as soon as
the underlying functor between the two categories preserves finite products. -/
noncomputable instance pullbackMonoidal [HasTerminal C] [HasTerminal D]
    [PreservesLimitsOfShape (Discrete PEmpty.{1}) F] :
    (pullbackOfCommRingCat φ).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal _

end Monoidal

end PresheafOfModules
