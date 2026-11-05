import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.Subsheaf
import Jacobian.Algebra.Category.ModuleCat.Presheaf.InternalHom
import Jacobian.CategoryTheory.Sites.SheafHom

/-!
# The internal hom of sheaves of modules

Let `R` be a sheaf of commutative rings on a site `(C, J)`. For sheaves of modules `M` and `N`
over `R`, we define the sheaf of modules `SheafOfModules.homObj M N`, whose underlying presheaf
is the internal hom presheaf `PresheafOfModules.homObj M.val N.val`.

The sheaf condition is `PresheafOfModules.isSheaf_homObj`: if `N` is a sheaf, then so is
`homObj M N`. The underlying presheaf of types of `homObj M N` identifies with the subpresheaf
`presheafHomLinearSubfunctor M N` of `R`-linear morphisms of `presheafHom M.presheaf N.presheaf`.
The presheaf `presheafHom M.presheaf N.presheaf` is a sheaf by `Presheaf.IsSheaf.hom`, and
`R`-linearity is a local condition if `N` is separated
(`PresheafOfModules.mem_presheafHomLinearSubfunctor_obj_of_isSeparated`).

## Main definitions and results

* `PresheafOfModules.isSheaf_homObj`: `homObj M N` is a sheaf if `N` is.
* `SheafOfModules.homObj M N`: the internal hom sheaf `U ↦ Hom_{R|_U}(M|_U, N|_U)`.
* `SheafOfModules.homObjSectionsEquiv`: the sections of `homObj M N` are the morphisms `M ⟶ N`.
* `SheafOfModules.homObjMap`, `SheafOfModules.homFunctor`: the functoriality of `homObj`.
-/


universe v v₁ u₁ u

open CategoryTheory Opposite

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Cᵒᵖ ⥤ CommRingCat.{u}} (M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _))

/-- The subpresheaf of `presheafHom M.presheaf N.presheaf` consisting of the `R`-linear
morphisms. -/
def presheafHomLinearSubfunctor : Subfunctor (presheafHom M.presheaf N.presheaf) where
  obj U := {α | ∀ (W : (Over U.unop)ᵒᵖ) (r : (R ⋙ forget₂ CommRingCat RingCat).obj (op W.unop.left))
    (m : M.obj (op W.unop.left)),
      α.app W (r • m) = r • show N.obj (op W.unop.left) from α.app W m}
  map f _ hα W r m := hα (op ((Over.map f.unop).obj W.unop)) r m

variable {M N} in
@[simp]
lemma mem_presheafHomLinearSubfunctor_obj {U : Cᵒᵖ}
    (α : (presheafHom M.presheaf N.presheaf).obj U) :
    α ∈ (presheafHomLinearSubfunctor M N).obj U ↔
      ∀ (W : (Over U.unop)ᵒᵖ) (r : (R ⋙ forget₂ CommRingCat RingCat).obj (op W.unop.left))
        (m : M.obj (op W.unop.left)),
        α.app W (r • m) = r • show N.obj (op W.unop.left) from α.app W m :=
  Iff.rfl

/-- The underlying presheaf of types of `homObj M N` is the subpresheaf of `R`-linear morphisms
of `presheafHom M.presheaf N.presheaf`:
```
  Cᵒᵖ --(homObj M N).presheaf--> AddCommGrpCat
   |                                   |
   | presheafHomLinearSubfunctor M N   | forget
   v                                   v
  Type ============================== Type
```
-/
@[simps!]
noncomputable def homObjCompForgetIso :
    (homObj M N).presheaf ⋙ forget _ ≅ (presheafHomLinearSubfunctor M N).toFunctor :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun φ := ⟨(toPresheaf _).map φ,
        (mem_presheafHomLinearSubfunctor_obj _).2 fun W r m ↦ (φ.app W).hom.map_smul r m⟩
      invFun α := homMk α.1 fun W r m ↦ (mem_presheafHomLinearSubfunctor_obj _).1 α.2 W r m
      left_inv _ := rfl
      right_inv _ := rfl }) (fun _ ↦ rfl)

variable {M N} in
/-- `R`-linearity of a section of `presheafHom M.presheaf N.presheaf` is a local condition if
`N` is separated. -/
lemma mem_presheafHomLinearSubfunctor_obj_of_isSeparated
    (hN : Presieve.IsSeparated J (N.presheaf ⋙ forget _)) {U : Cᵒᵖ}
    (α : (presheafHom M.presheaf N.presheaf).obj U)
    (hα : (presheafHomLinearSubfunctor M N).sieveOfSection α ∈ J U.unop) :
    α ∈ (presheafHomLinearSubfunctor M N).obj U := by
  refine (mem_presheafHomLinearSubfunctor_obj _).2 fun W r m ↦ ?_
  -- As `N` is separated, it suffices to check the equality after restriction along every
  -- `h : Z ⟶ W.left` in the pullback along `W.hom` of the sieve on which `α` is linear.
  refine (hN _ (J.pullback_stable W.unop.hom hα)).ext fun Z h hh ↦ ?_
  -- The restriction `β` of `α` along `h ≫ W.hom`, evaluated at `Over.mk (𝟙 Z)`, is linear.
  let β : M.obj (op Z) → N.obj (op Z) :=
    ((presheafHom M.presheaf N.presheaf).map (h ≫ W.unop.hom).op α).app (op (Over.mk (𝟙 Z)))
  have hβ := (mem_presheafHomLinearSubfunctor_obj _).1 hh (op (Over.mk (𝟙 Z))) (R.map h.op r)
    (M.map h.op m)
  -- Restricting `α.app W` along `h` is `β` of the restriction:
  --   M(W.left) --α_W--> N(W.left)
  --      |                   |
  --    M(h)                N(h)
  --      v                   v
  --     M(Z) ------β----->  N(Z)
  have hnat (x : M.obj (op W.unop.left)) : N.map h.op (α.app W x) = β (M.map h.op x) :=
    ConcreteCategory.congr_hom (presheafHom_app_comp_map α W h) x
  -- Move `r` through `N(h)`, `β` and `M(h)`, using the linearity of `β`.
  -- `N(h) (α_W (r • m)) = β (M(h) (r • m)) = β (r|_Z • M(h) m) = r|_Z • β (M(h) m)`
  -- `= r|_Z • N(h) (α_W m) = N(h) (r • α_W m)`.
  exact (hnat (r • m)).trans <|
    (congrArg β (M.map_smul h.op r m)).trans <|
    hβ.trans <|
    (congrArg (R.map h.op r • ·) (hnat m).symm).trans <|
    (N.map_smul h.op r _).symm

variable {M N} in
/-- The internal hom `homObj M N` is a sheaf if `N` is a sheaf. -/
theorem isSheaf_homObj (hN : Presheaf.IsSheaf J N.presheaf) :
    Presheaf.IsSheaf J (homObj M N).presheaf := by
  refine Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat.{max u₁ v₁ v}) ?_
  rw [isSheaf_iff_isSheaf_of_type]
  refine Presieve.isSheaf_iso J (homObjCompForgetIso M N).symm ?_
  have hH := Presheaf.IsSheaf.hom M.presheaf N.presheaf hN
  rw [isSheaf_iff_isSheaf_of_type] at hH
  have hN' : Presieve.IsSheaf J (N.presheaf ⋙ forget _) := (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf J _ (forget _) hN)
  exact (Subfunctor.isSheaf_iff _ hH).2 fun _ α hα ↦
    mem_presheafHomLinearSubfunctor_obj_of_isSeparated hN'.isSeparated α hα

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] {R : Sheaf J CommRingCat.{u}}
  (M N : SheafOfModules.{v} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))

/-- The internal hom sheaf of modules `U ↦ Hom_{R|_U}(M|_U, N|_U)`.
See `PresheafOfModules.homObj` for the underlying presheaf of modules. -/
@[simps]
noncomputable def homObj :
    SheafOfModules.{max u₁ v₁ v} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) where
  val := PresheafOfModules.homObj (R := R.obj) M.val N.val
  isSheaf := PresheafOfModules.isSheaf_homObj N.isSheaf

/-- The sections of the internal hom `homObj M N` are the morphisms `M ⟶ N`. -/
noncomputable def homObjSectionsEquiv : (homObj M N).sections ≃ (M ⟶ N) :=
  (PresheafOfModules.homObjSectionsEquiv M.val N.val).trans
    (fullyFaithfulForget _).homEquiv.symm

variable {M N}
  {M' N' : SheafOfModules.{v} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)}

/-- The functoriality of `homObj M N`: contravariant in `M` and covariant in `N`. -/
@[simps]
noncomputable def homObjMap (f : M' ⟶ M) (g : N ⟶ N') : homObj M N ⟶ homObj M' N' where
  val := PresheafOfModules.homObjMap f.val g.val

@[simp]
lemma homObjMap_id : homObjMap (𝟙 M) (𝟙 N) = 𝟙 (homObj M N) :=
  hom_ext (PresheafOfModules.homObjMap_id (M := M.val) (N := N.val))

@[reassoc (attr := simp)]
lemma homObjMap_comp_homObjMap
    {M'' N'' : SheafOfModules.{v} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)}
    (f : M' ⟶ M) (f' : M'' ⟶ M') (g : N ⟶ N') (g' : N' ⟶ N'') :
    homObjMap f g ≫ homObjMap f' g' = homObjMap (f' ≫ f) (g ≫ g') :=
  hom_ext (PresheafOfModules.homObjMap_comp_homObjMap f.val f'.val g.val g'.val)

variable (R) in
/-- The internal hom bifunctor on sheaves of modules, `(M, N) ↦ homObj M N`, contravariant in
`M` and covariant in `N`. -/
@[simps]
noncomputable def homFunctor :
    (SheafOfModules.{v} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))ᵒᵖ ⥤
      SheafOfModules.{v} ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) ⥤
        SheafOfModules.{max u₁ v₁ v}
          ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R) where
  obj M :=
    { obj N := homObj M.unop N
      map g := homObjMap (𝟙 M.unop) g }
  map f := { app N := homObjMap f.unop (𝟙 N) }

end SheafOfModules
