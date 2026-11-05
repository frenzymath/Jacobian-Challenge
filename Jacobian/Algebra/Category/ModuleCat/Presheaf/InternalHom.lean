import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Comma.Over.Basic
import Jacobian.LinearAlgebra.TensorProduct.Cyclic

/-!
# The internal hom of presheaves of modules

Let `R : Cᵒᵖ ⥤ CommRingCat` be a presheaf of commutative rings on a category `C`. For presheaves
of modules `M` and `N` over `R`, we define the presheaf of modules `homObj M N` which sends `U`
to the `R(U)`-module of morphisms between the restrictions of `M` and `N` to `Over U`. A section
`r` of `R` over `U` acts on such a morphism by post-composition with multiplication by the
restrictions of `r`. This is the presheaf of modules analogue of `presheafHom`.

The module structure comes from a more general fact: for a presheaf of commutative rings `S` on
any category, a compatible family of sections of `S` acts on every presheaf of modules over `S`
by multiplication (`sectionsSMul`), so the morphisms between two presheaves of modules form a
module over the ring of such families.

The presheaf `homObj M N` lives in `PresheafOfModules.{max u₁ v₁ v}`. For `C = X.Opens` of a
scheme `X : Scheme.{u}` and `M N : X.Modules` all universes are `u`, so `homObj M N` is again a
`PresheafOfModules.{u}`.

## Main definitions and results

* `PresheafOfModules.homObj M N`: the internal hom presheaf `U ↦ Hom_{R|_U}(M|_U, N|_U)`.
* `PresheafOfModules.homObjSectionsEquiv`: the sections of `homObj M N` are the morphisms
  `M ⟶ N`.
* `PresheafOfModules.homObjMap`: its functoriality, contravariant in `M` and covariant in `N`.
* `PresheafOfModules.homFunctor`: the internal hom bifunctor.
* `PresheafOfModules.homObjEquiv`: the tensor-hom adjunction `(M ⊗ P ⟶ N) ≃ (P ⟶ homObj M N)`,
  natural in `P` (`PresheafOfModules.homObjEquiv_whiskerLeft_comp`).
* `PresheafOfModules.tensorHomUncurry_id_app_bijective`: the evaluation `M ⊗ homObj M R ⟶ R` is
  bijective on sections over `W` if `M` is free of rank one on `W`.

If `N` is a sheaf, then so is `homObj M N`: this is `PresheafOfModules.isSheaf_homObj` in
`SheafOfModules.homObj`.

## TODO

* Use `homObjEquiv` to make `homFunctor` the internal hom of a monoidal closed structure.
-/


universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Opposite

namespace PresheafOfModules

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

section SectionsSMul

variable {D : Type u₂} [Category.{v₂} D] {S : Dᵒᵖ ⥤ CommRingCat.{u}}
  (N : PresheafOfModules.{v} (S ⋙ forget₂ _ _))

/-- Multiplication by a compatible family `s` of sections of a presheaf of commutative rings
`S`, as an endomorphism of a presheaf of modules over `S`. -/
noncomputable def sectionsSMul (s : RingCat.sectionsSubring (S ⋙ forget₂ _ RingCat)) : N ⟶ N where
  app X := ModuleCat.ofHom (LinearMap.lsmul (S.obj X) (N.obj X) (s.1 X))
  naturality {X Y} f := by
    ext x
    exact ((N.map_smul f (s.1 X) x).trans (congrArg (· • _) (s.2 f))).symm

@[simp]
lemma sectionsSMul_app_apply (s : RingCat.sectionsSubring (S ⋙ forget₂ _ RingCat)) (X : Dᵒᵖ)
    (x : N.obj X) : ((sectionsSMul N s).app X).hom x = s.1 X • x :=
  rfl

/-- Multiplication by compatible families of sections of `S`, as a ring homomorphism to the
endomorphisms of a presheaf of modules over `S`. -/
noncomputable def sectionsSMulHom : RingCat.sectionsSubring (S ⋙ forget₂ _ RingCat) →+* End N where
  toFun := sectionsSMul N
  map_one' := hom_ext fun _ ↦ by ext; exact one_smul _ _
  map_mul' _ _ := hom_ext fun _ ↦ by ext; exact mul_smul _ _ _
  map_zero' := hom_ext fun _ ↦ by ext; exact zero_smul _ _
  map_add' _ _ := hom_ext fun _ ↦ by ext; exact add_smul _ _ _

variable {N} in
/-- Multiplication by a compatible family `s` of sections commutes with morphisms `g : N ⟶ N'`:
```
  N  --g-->  N'
  |          |
s • ·      s • ·
  v          v
  N  --g-->  N'
```
-/
@[reassoc]
lemma sectionsSMul_naturality {N' : PresheafOfModules.{v} (S ⋙ forget₂ _ _)} (g : N ⟶ N')
    (s : RingCat.sectionsSubring (S ⋙ forget₂ _ RingCat)) :
    g ≫ sectionsSMul N' s = sectionsSMul N s ≫ g := by
  ext X x
  exact ((g.app X).hom.map_smul _ x).symm

end SectionsSMul

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (R) in
/-- The restriction of presheaves of modules to `Over U`. -/
noncomputable def restrictOver (U : C) :
    PresheafOfModules.{v} (R ⋙ forget₂ _ _) ⥤
      PresheafOfModules.{v} (((Over.forget U).op ⋙ R) ⋙ forget₂ _ _) :=
  pushforward₀OfCommRingCat (Over.forget U) R

variable {U : C} {M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _)}

@[simp]
lemma restrictOver_obj_obj (W : (Over U)ᵒᵖ) :
    ((restrictOver R U).obj M).obj W = M.obj (op W.unop.left) :=
  rfl

@[simp]
lemma restrictOver_obj_map_apply {W W' : (Over U)ᵒᵖ} (f : W ⟶ W') (x : M.obj (op W.unop.left)) :
    ((restrictOver R U).obj M).map f x = M.map f.unop.left.op x :=
  rfl

@[simp]
lemma restrictOver_map_app (g : M ⟶ N) (W : (Over U)ᵒᵖ) :
    ((restrictOver R U).map g).app W = g.app (op W.unop.left) :=
  rfl

/-- A morphism between restrictions to `Over U` has the same components at `Over.mk f` and
`Over.mk g` if `f = g`. -/
lemma restrictOver_hom_app_congr
    (φ : (restrictOver R U).obj M ⟶ (restrictOver R U).obj N) {X : C} {f g : X ⟶ U} (h : f = g)
    (x : M.obj (op X)) : φ.app (op (Over.mk f)) x = φ.app (op (Over.mk g)) x := by
  subst h
  rfl

variable (U) in
/-- A section `r` of `R` over `U` gives the compatible family of its restrictions to all
`W ∈ Over U`. This is a ring homomorphism. -/
noncomputable def overSections :
    R.obj (op U) →+* RingCat.sectionsSubring (((Over.forget U).op ⋙ R) ⋙ forget₂ _ RingCat) where
  toFun r := ⟨fun W ↦ R.map W.unop.hom.op r, fun {W W'} f ↦ by
    refine (CommRingCat.comp_apply (R.map W.unop.hom.op) (R.map f.unop.left.op) r).symm.trans ?_
    rw [← R.map_comp, ← op_comp, Over.w]⟩
  map_one' := Subtype.ext <| funext fun _ ↦ map_one _
  map_mul' _ _ := Subtype.ext <| funext fun _ ↦ map_mul _ _ _
  map_zero' := Subtype.ext <| funext fun _ ↦ map_zero _
  map_add' _ _ := Subtype.ext <| funext fun _ ↦ map_add _ _ _

@[simp]
lemma overSections_coe_apply (r : R.obj (op U)) (W : (Over U)ᵒᵖ) :
    (overSections U r).1 W = R.map W.unop.hom.op r :=
  rfl

/-- The `R(U)`-module structure on morphisms between restrictions to `Over U`: a section `r` acts
by post-composition with multiplication by the restrictions of `r`. Its underlying additive group
is the one coming from the preadditive structure of `PresheafOfModules`. -/
noncomputable instance :
    Module (R.obj (op U)) ((restrictOver R U).obj M ⟶ (restrictOver R U).obj N) :=
  Module.compHom _ ((sectionsSMulHom ((restrictOver R U).obj N)).comp (overSections U))

lemma smul_eq_comp_sectionsSMul (r : R.obj (op U))
    (φ : (restrictOver R U).obj M ⟶ (restrictOver R U).obj N) :
    r • φ = φ ≫ sectionsSMul _ (overSections U r) :=
  rfl

@[simp]
lemma smul_app (r : R.obj (op U)) (φ : (restrictOver R U).obj M ⟶ (restrictOver R U).obj N)
    (W : (Over U)ᵒᵖ) : (r • φ).app W = φ.app W ≫ (sectionsSMul _ (overSections U r)).app W :=
  rfl

/-- Restriction of a morphism between restrictions to `Over U` along `g : V ⟶ U`, using
`Over.map g ⋙ Over.forget U = Over.forget V`. -/
noncomputable def restrictOverMap {V : C} (g : V ⟶ U)
    (φ : (restrictOver R U).obj M ⟶ (restrictOver R U).obj N) :
    (restrictOver R V).obj M ⟶ (restrictOver R V).obj N :=
  (pushforward₀ (Over.map g) _).map φ

@[simp]
lemma restrictOverMap_app {V : C} (g : V ⟶ U)
    (φ : (restrictOver R U).obj M ⟶ (restrictOver R U).obj N) (W : (Over V)ᵒᵖ) :
    (restrictOverMap g φ).app W = φ.app (op ((Over.map g).obj W.unop)) :=
  rfl

@[simp]
lemma restrictOverMap_id (φ : (restrictOver R U).obj M ⟶ (restrictOver R U).obj N) :
    restrictOverMap (𝟙 U) φ = φ := by
  ext W x
  exact restrictOver_hom_app_congr φ (Category.comp_id W.unop.hom) x

lemma restrictOverMap_comp {V V' : C} (f : V ⟶ U) (g : V' ⟶ V)
    (φ : (restrictOver R U).obj M ⟶ (restrictOver R U).obj N) :
    restrictOverMap (g ≫ f) φ = restrictOverMap g (restrictOverMap f φ) := by
  ext W x
  exact restrictOver_hom_app_congr φ (Category.assoc W.unop.hom g f).symm x

lemma overSections_coe_map_obj {V : C} (g : V ⟶ U) (r : R.obj (op U)) (W : (Over V)ᵒᵖ) :
    (overSections U r).1 (op ((Over.map g).obj W.unop)) = (overSections V (R.map g.op r)).1 W := by
  rw [overSections_coe_apply, overSections_coe_apply, ← CommRingCat.comp_apply, ← R.map_comp,
    ← op_comp]
  rfl

variable (N) in
/-- Multiplication by `r` on the restriction of `N` to `Over U` is compatible with `Over.map g`
for `g : V ⟶ U`: at `W ∈ Over V`, it agrees with multiplication by `R.map g.op r` on the
restriction of `N` to `Over V`.
```
  N(W) --r • ·------------> N(W)
   ‖                          ‖
  N(W) --R.map g.op r • ·--> N(W)
```
-/
lemma sectionsSMul_overSections_app_map_obj {V : C} (g : V ⟶ U) (r : R.obj (op U))
    (W : (Over V)ᵒᵖ) :
    (sectionsSMul ((restrictOver R U).obj N) (overSections U r)).app
        (op ((Over.map g).obj W.unop)) =
      (sectionsSMul ((restrictOver R V).obj N) (overSections V (R.map g.op r))).app W := by
  ext x
  exact congrArg (· • x) (overSections_coe_map_obj g r W)

@[simp]
lemma restrictOverMap_smul {V : C} (g : V ⟶ U) (r : R.obj (op U))
    (φ : (restrictOver R U).obj M ⟶ (restrictOver R U).obj N) :
    restrictOverMap g (r • φ) = R.map g.op r • restrictOverMap g φ := by
  ext W : 1
  simp only [restrictOverMap_app, smul_app]
  exact congrArg (φ.app _ ≫ ·) (sectionsSMul_overSections_app_map_obj N g r W)

@[simp]
lemma restrictOverMap_restrictOver_map {V : C} (g : V ⟶ U) (φ : M ⟶ N) :
    restrictOverMap g ((restrictOver R U).map φ) = (restrictOver R V).map φ :=
  rfl

variable (M N)

/-- The internal hom presheaf of modules `U ↦ Hom_{R|_U}(M|_U, N|_U)`. -/
@[simps obj]
noncomputable def homObj : PresheafOfModules.{max u₁ v₁ v} (R ⋙ forget₂ _ _) where
  obj X := ModuleCat.of (R.obj (op X.unop))
    ((restrictOver R X.unop).obj M ⟶ (restrictOver R X.unop).obj N)
  map {X Y} g := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.map g).hom).obj (ModuleCat.of (R.obj (op Y.unop))
      ((restrictOver R Y.unop).obj M ⟶ (restrictOver R Y.unop).obj N)))
    { toFun φ := restrictOverMap g.unop φ
      map_add' _ _ := rfl
      map_smul' r φ := restrictOverMap_smul g.unop r φ }
  map_id X := by
    ext φ : 2
    exact restrictOverMap_id φ
  map_comp f g := by
    ext φ : 2
    exact restrictOverMap_comp f.unop g.unop φ

variable {M N}

@[simp]
lemma homObj_map_apply {X Y : Cᵒᵖ} (g : X ⟶ Y) (φ : (homObj M N).obj X) :
    ((homObj M N).map g).hom φ = restrictOverMap g.unop φ :=
  rfl

variable (M N) in
/-- The sections of the internal hom `homObj M N` are the morphisms `M ⟶ N`. -/
noncomputable def homObjSectionsEquiv : (homObj M N).sections ≃ (M ⟶ N) where
  toFun s :=
    { app X := (s.1 X).app (op (Over.mk (𝟙 X.unop)))
      naturality {X Y} f := by
        ext x
        have h := naturality_apply (s.1 X) (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 _)).op x
        simp only [restrictOver_obj_map_apply] at h
        rw [← s.2 f]
        exact (restrictOver_hom_app_congr (s.1 X) (Category.id_comp f.unop) _).trans h }
  invFun φ := sectionsMk (fun X ↦ (restrictOver R X.unop).map φ) (fun _ _ _ ↦ rfl)
  left_inv s := by
    refine sections_ext _ _ fun X ↦ hom_ext fun W ↦ ?_
    ext x
    exact (congrArg (fun ψ ↦ ψ.app (op (Over.mk (𝟙 _))) x) (s.2 W.unop.hom.op)).symm.trans
      (restrictOver_hom_app_congr (s.1 X) (Category.id_comp _) x)
  right_inv _ := rfl

variable {M' N' : PresheafOfModules.{v} (R ⋙ forget₂ _ _)}

/-- The functoriality of `homObj M N`: contravariant in `M` and covariant in `N`. -/
noncomputable def homObjMap (f : M' ⟶ M) (g : N ⟶ N') : homObj M N ⟶ homObj M' N' where
  app X := ModuleCat.ofHom
    { toFun φ := (restrictOver R X.unop).map f ≫ φ ≫ (restrictOver R X.unop).map g
      map_add' _ _ := by simp
      map_smul' r φ := by
        rw [smul_eq_comp_sectionsSMul, smul_eq_comp_sectionsSMul, RingHom.id_apply]
        simp only [Category.assoc]
        rw [sectionsSMul_naturality] }
  naturality _ := by ext; rfl

@[simp]
lemma homObjMap_app_apply (f : M' ⟶ M) (g : N ⟶ N') (X : Cᵒᵖ)
    (φ : (restrictOver R X.unop).obj M ⟶ (restrictOver R X.unop).obj N) :
    ((homObjMap f g).app X).hom φ =
      (restrictOver R X.unop).map f ≫ φ ≫ (restrictOver R X.unop).map g :=
  rfl

@[simp]
lemma homObjMap_id : homObjMap (𝟙 M) (𝟙 N) = 𝟙 (homObj M N) := by
  ext X : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun
    (φ : (restrictOver R X.unop).obj M ⟶ (restrictOver R X.unop).obj N) ↦ ?_)
  exact (Category.id_comp _).trans (Category.comp_id φ)

@[reassoc (attr := simp)]
lemma homObjMap_comp_homObjMap {M'' N'' : PresheafOfModules.{v} (R ⋙ forget₂ _ _)}
    (f : M' ⟶ M) (f' : M'' ⟶ M') (g : N ⟶ N') (g' : N' ⟶ N'') :
    homObjMap f g ≫ homObjMap f' g' = homObjMap (f' ≫ f) (g ≫ g') := by
  ext X : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun
    (φ : (restrictOver R X.unop).obj M ⟶ (restrictOver R X.unop).obj N) ↦ ?_)
  exact (by simp : (restrictOver R X.unop).map f' ≫ ((restrictOver R X.unop).map f ≫ φ ≫
    (restrictOver R X.unop).map g) ≫ (restrictOver R X.unop).map g' =
      (restrictOver R X.unop).map (f' ≫ f) ≫ φ ≫ (restrictOver R X.unop).map (g ≫ g'))

lemma homObjMap_comp {M'' N'' : PresheafOfModules.{v} (R ⋙ forget₂ _ _)} (f : M' ⟶ M)
    (f' : M'' ⟶ M') (g : N ⟶ N') (g' : N' ⟶ N'') :
    homObjMap (f' ≫ f) (g ≫ g') = homObjMap f g ≫ homObjMap f' g' :=
  (homObjMap_comp_homObjMap f f' g g').symm

variable (R) in
/-- The internal hom bifunctor on presheaves of modules, `(M, N) ↦ homObj M N`, contravariant in
`M` and covariant in `N`. -/
@[simps]
noncomputable def homFunctor :
    (PresheafOfModules.{v} (R ⋙ forget₂ _ _))ᵒᵖ ⥤
      PresheafOfModules.{v} (R ⋙ forget₂ _ _) ⥤
        PresheafOfModules.{max u₁ v₁ v} (R ⋙ forget₂ _ _) where
  obj M :=
    { obj N := homObj M.unop N
      map g := homObjMap (𝟙 M.unop) g }
  map f := { app N := homObjMap f.unop (𝟙 N) }

section TensorHom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MonoidalCategory

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable {M P N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}

variable (M) in
/-- The morphism `M(X) ⟶ (M ⊗ P)(X)` sending `m` to `m ⊗ p`, for a section `p` of `P` over
`X`. -/
noncomputable def tmulRight {X : Cᵒᵖ} (p : P.obj X) : M.obj X ⟶ (M ⊗ P).obj X :=
  ModuleCat.ofHom (R := R.obj X) ((TensorProduct.mk (R.obj X) (M.obj X) (P.obj X)).flip p)

@[simp]
lemma tmulRight_apply {X : Cᵒᵖ} (p : P.obj X) (m : M.obj X) :
    tmulRight M p m = m ⊗ₜ[R.obj X] p :=
  rfl

/-- Auxiliary definition for `homObjEquiv`: a morphism `φ : M ⊗ P ⟶ N` and a section `p` of `P`
over `U` give the morphism `M|_U ⟶ N|_U` sending a section `m` of `M` over `W ⟶ U` to
`φ (m ⊗ p|_W)`. -/
noncomputable def tensorHomCurryApp (φ : M ⊗ P ⟶ N) {U : C} (p : P.obj (op U)) :
    (restrictOver R U).obj M ⟶ (restrictOver R U).obj N where
  app W := tmulRight M (P.map W.unop.hom.op p) ≫ φ.app (op W.unop.left)
  naturality {W W'} f := by
    ext m
    refine (congrArg (φ.app (op W'.unop.left)) ?_).trans
      (naturality_apply φ f.unop.left.op (m ⊗ₜ[R.obj (op W.unop.left)] P.map W.unop.hom.op p))
    refine (congrArg (fun q : P.obj (op W'.unop.left) ↦
      M.map f.unop.left.op m ⊗ₜ[R.obj (op W'.unop.left)] q) ?_).trans
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul f.unop.left.op m _).symm
    exact (P.congr_map_apply (show W'.unop.hom.op =
        W.unop.hom.op ≫ f.unop.left.op by rw [← op_comp, Over.w]) p).trans
      (P.map_comp_apply W.unop.hom.op f.unop.left.op p)

@[simp]
lemma tensorHomCurryApp_app_apply (φ : M ⊗ P ⟶ N) {U : C} (p : P.obj (op U))
    (W : (Over U)ᵒᵖ) (m : M.obj (op W.unop.left)) :
    ((tensorHomCurryApp φ p).app W).hom m =
      φ.app (op W.unop.left) (m ⊗ₜ[R.obj (op W.unop.left)] P.map W.unop.hom.op p) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma tensorHomCurryApp_add (φ : M ⊗ P ⟶ N) {U : C} (p p' : P.obj (op U)) :
    tensorHomCurryApp φ (p + p') = tensorHomCurryApp φ p + tensorHomCurryApp φ p' := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [add_app, ModuleCat.hom_add, LinearMap.add_apply, tensorHomCurryApp_app_apply,
    tensorHomCurryApp_app_apply, tensorHomCurryApp_app_apply, map_add, TensorProduct.tmul_add,
    map_add]

set_option backward.isDefEq.respectTransparency false in
lemma tensorHomCurryApp_smul (φ : M ⊗ P ⟶ N) {U : C} (r : R.obj (op U)) (p : P.obj (op U)) :
    tensorHomCurryApp φ (r • p) = r • tensorHomCurryApp φ p := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [smul_app, ModuleCat.hom_comp, LinearMap.comp_apply, tensorHomCurryApp_app_apply,
    tensorHomCurryApp_app_apply, sectionsSMul_app_apply, overSections_coe_apply, map_smul]
  exact (congrArg _ (TensorProduct.tmul_smul (R.map W.unop.hom.op r) m _)).trans (map_smul _ _ _)

set_option backward.isDefEq.respectTransparency false in
lemma tensorHomCurryApp_map (φ : M ⊗ P ⟶ N) {U V : C} (g : V ⟶ U) (p : P.obj (op U)) :
    tensorHomCurryApp (U := V) φ (P.map g.op p) = restrictOverMap g (tensorHomCurryApp φ p) := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [restrictOverMap_app, tensorHomCurryApp_app_apply, ← map_comp_apply]
  rfl

/-- Auxiliary definition for `homObjEquiv`: the morphism `P ⟶ homObj M N` corresponding to a
morphism `φ : M ⊗ P ⟶ N`. -/
noncomputable def tensorHomCurry (φ : M ⊗ P ⟶ N) : P ⟶ homObj M N where
  app X := ModuleCat.ofHom (X := P.obj X) (Y := (homObj M N).obj X)
    { toFun p := tensorHomCurryApp φ p
      map_add' := tensorHomCurryApp_add φ
      map_smul' := tensorHomCurryApp_smul φ }
  naturality {X Y} g := by
    ext p : 2
    exact tensorHomCurryApp_map φ g.unop p

@[simp]
lemma tensorHomCurry_app_apply (φ : M ⊗ P ⟶ N) (X : Cᵒᵖ) (p : P.obj X) :
    (tensorHomCurry φ).app X p = tensorHomCurryApp φ p :=
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (M N) in
/-- Evaluation of a section of `homObj M N` over `U` at `Over.mk (𝟙 U)`, as a linear map. -/
noncomputable def homObjEvalId (U : C) :
    (homObj M N).obj (op U) →ₗ[R.obj (op U)] M.obj (op U) →ₗ[R.obj (op U)] N.obj (op U) where
  toFun φ := (φ.app (op (Over.mk (𝟙 U)))).hom
  map_add' _ _ := rfl
  map_smul' r φ := by
    ext m
    rw [smul_app, ModuleCat.hom_comp, LinearMap.comp_apply, sectionsSMul_app_apply,
      overSections_coe_apply]
    simp

@[simp]
lemma homObjEvalId_apply_apply (U : C) (φ : (homObj M N).obj (op U)) (m : M.obj (op U)) :
    homObjEvalId M N U φ m = φ.app (op (Over.mk (𝟙 U))) m :=
  rfl

/-- Auxiliary definition for `homObjEquiv`: the morphism `M ⊗ P ⟶ N` corresponding to a
morphism `ψ : P ⟶ homObj M N`, sending `m ⊗ p` to `ψ p` evaluated at `m`. -/
noncomputable def tensorHomUncurry (ψ : P ⟶ homObj M N) : M ⊗ P ⟶ N where
  app X := ModuleCat.ofHom
    (TensorProduct.lift ((homObjEvalId M N X.unop).comp (ψ.app X).hom).flip)
  naturality {X Y} f := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m p ↦ ?_
    refine (congrArg (fun ξ : (restrictOver R Y.unop).obj M ⟶ (restrictOver R Y.unop).obj N ↦
      ξ.app (op (Over.mk (𝟙 Y.unop))) (M.map f m)) (naturality_apply ψ f p)).trans ?_
    refine (restrictOver_hom_app_congr (ψ.app X p) (Category.id_comp f.unop) (M.map f m)).trans ?_
    exact naturality_apply (ψ.app X p) (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 _)).op m

@[simp]
lemma tensorHomUncurry_app_tmul (ψ : P ⟶ homObj M N) (X : Cᵒᵖ) (m : M.obj X) (p : P.obj X) :
    (tensorHomUncurry ψ).app X (m ⊗ₜ[R.obj X] p) =
      (ψ.app X p).app (op (Over.mk (𝟙 X.unop))) m :=
  rfl

/-- The tensor-hom adjunction for presheaves of modules: morphisms `M ⊗ P ⟶ N` correspond to
morphisms `P ⟶ homObj M N`. A morphism `φ : M ⊗ P ⟶ N` is sent to the morphism which sends a
section `p` of `P` over `U` to `m ↦ φ (m ⊗ p|_W)` for `W ⟶ U` and `m` a section of `M` over
`W`. -/
noncomputable def homObjEquiv (M P N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (M ⊗ P ⟶ N) ≃ (P ⟶ homObj M N) where
  toFun := tensorHomCurry
  invFun := tensorHomUncurry
  left_inv φ := by
    ext X : 1
    refine ModuleCat.MonoidalCategory.tensor_ext fun m p ↦ ?_
    refine congrArg (fun q : P.obj X ↦ φ.app X (m ⊗ₜ[R.obj X] q)) (?_ : P.map (𝟙 X) p = p)
    rw [map_id]
    rfl
  right_inv ψ := by
    ext X : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : P.obj X) ↦ ?_)
    refine hom_ext (M₁ := (restrictOver R X.unop).obj M) (M₂ := (restrictOver R X.unop).obj N)
      fun W ↦ ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
    refine (congrArg (fun ξ : (restrictOver R W.unop.left).obj M ⟶
        (restrictOver R W.unop.left).obj N ↦ ξ.app (op (Over.mk (𝟙 W.unop.left))) m)
      (naturality_apply ψ W.unop.hom.op p)).trans ?_
    exact restrictOver_hom_app_congr (ψ.app X p) (Category.id_comp W.unop.hom) m

/-- The tensor-hom adjunction `homObjEquiv` is natural in the second factor. -/
lemma homObjEquiv_whiskerLeft_comp {M P P' N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    (f : P ⟶ P') (φ : M ⊗ P' ⟶ N) :
    homObjEquiv M P N (M ◁ f ≫ φ) = f ≫ homObjEquiv M P' N φ := by
  ext X : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : P.obj X) ↦ ?_)
  refine hom_ext (M₁ := (restrictOver R X.unop).obj M) (M₂ := (restrictOver R X.unop).obj N)
    fun W ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  exact congrArg (fun q : P'.obj (op W.unop.left) ↦
    φ.app (op W.unop.left) (m ⊗ₜ[R.obj (op W.unop.left)] q)) (naturality_apply f W.unop.hom.op p)

/-- The evaluation `M ⊗ Hom(M, R) ⟶ R` of presheaves of modules is bijective on sections over
`W` if `M` is free of rank one on `W`: that is, if there is a section `m₀` over `W` restricting
to a generator over every `V ⟶ W`, and a morphism `φ₀ : M|_W ⟶ R|_W` with `φ₀ m₀ = 1`. -/
lemma tensorHomUncurry_id_app_bijective {W : C} (m₀ : M.obj (op W))
    (φ₀ : (restrictOver R W).obj M ⟶ (restrictOver R W).obj (unit _))
    (hφ₀ : φ₀.app (op (Over.mk (𝟙 W))) m₀ = (1 : R.obj (op W)))
    (hgen : ∀ (V : Over W) (x : M.obj (op V.left)),
      ∃ r : R.obj (op V.left), x = r • M.restrictₛₗ V.hom.op m₀) :
    Function.Bijective ((tensorHomUncurry (𝟙 (homObj M (unit _)))).app (op W)) := by
  refine TensorProduct.lift_bijective_of_forall_eq_smul _ m₀ (fun p ↦ ?_)
    ⟨?_, fun (a : R.obj (op W)) ↦ ⟨a • φ₀, ?_⟩⟩
  · obtain ⟨r, hr⟩ := hgen (Over.mk (𝟙 W)) p
    refine ⟨r, hr.trans (congrArg (r • ·) ?_)⟩
    rw [PresheafOfModules.restrictₛₗ_apply]
    change M.map (𝟙 (op W)) m₀ = m₀
    rw [M.map_id]
    simp only [ModuleCat.restrictScalarsId'_inv_app,
      ModuleCat.restrictScalarsId'App_inv_apply]
  · rw [injective_iff_map_eq_zero]
    intro (q : (restrictOver R W).obj M ⟶ (restrictOver R W).obj (unit _))
      (hq : q.app (op (Over.mk (𝟙 W))) m₀ = 0)
    refine hom_ext fun V ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    obtain ⟨r, rfl⟩ := hgen V.unop x
    have h0 : q.app V (M.restrictₛₗ V.unop.hom.op m₀) = 0 :=
      (naturality_apply q (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 W)).op m₀).trans
        ((congrArg _ hq).trans (map_zero _))
    refine ((q.app V).hom.map_smul r _).trans ?_
    rw [h0]
    exact smul_zero _
  · refine (LinearMap.map_smul _ a φ₀).trans ?_
    exact (congrArg (fun y : R.obj (op W) ↦ a • y) hφ₀).trans (mul_one a)

end TensorHom

end PresheafOfModules
