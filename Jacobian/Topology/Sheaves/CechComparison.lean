import Jacobian.Topology.Sheaves.Cech
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# Comparing the categorical and explicit Čech complexes

The product-based Čech complex of a presheaf of modules agrees, after forgetting
scalars, with the explicit complex of cochains on finite intersections. This
identification respects presheaf morphisms and scalar multiplication on homology.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u u'

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Presheaf

section Preadditive

variable {X : TopCat.{u}} {ι : Type w} (U : ι → Opens X) {A : Type u'} [Category.{v} A]
  [HasProducts.{w} A] [Preadditive A] (P : (Opens X)ᵒᵖ ⥤ A)

/-- The projection of the degree `k` term of `cechComplexFunctor U` onto the factor of the
tuple `y`, the value of `P` on the product of the `U (y l)`. -/
noncomputable def cechComplexFunctorπ (k : ℕ) (y : Fin (k + 1) → ι) :
    ((cechComplexFunctor U).obj P).X k ⟶ P.obj (op (∏ᶜ fun l ↦ U (y l))) :=
  Pi.π (fun y : Fin (k + 1) → ι ↦ P.obj (op (∏ᶜ fun l ↦ U (y l)))) y

/-- Morphisms to a term of `cechComplexFunctor U` are determined by their projections. -/
lemma cechComplexFunctor_hom_ext {k : ℕ} {Z : A} {f g : Z ⟶ ((cechComplexFunctor U).obj P).X k}
    (h : ∀ y, f ≫ cechComplexFunctorπ U P k y = g ≫ cechComplexFunctorπ U P k y) : f = g :=
  Pi.hom_ext _ _ h

/-- The differential of `cechComplexFunctor U`, through the projections of the product: the
alternating sum of the restrictions of the faces. -/
lemma cechComplexFunctor_d_π (k : ℕ) (y : Fin (k + 2) → ι) :
    ((cechComplexFunctor U).obj P).d k (k + 1) ≫ cechComplexFunctorπ U P (k + 1) y =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • (cechComplexFunctorπ U P k (y ∘ i.succAbove) ≫
        P.map (Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l)) (i.succAbove l)).op) := by
  have h : ((cechComplexFunctor U).obj P).d k (k + 1) = ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
      ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P).δ i :=
    CochainComplex.of_d _ (AlgebraicTopology.AlternatingCofaceMapComplex.objD _) k
  rw [h, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.zsmul_comp]
  congr 1
  dsimp [cechComplexFunctorπ, CosimplicialObject.δ,
    FormalCoproduct.cosimplicialObjectFunctor_obj_map, FormalCoproduct.evalOp_obj_map]
  erw [Pi.lift_comp_π]
  rfl

/-- A morphism of presheaves acts factorwise on `cechComplexFunctor U`. -/
lemma cechComplexFunctor_map_f_π {Q : (Opens X)ᵒᵖ ⥤ A} (φ : P ⟶ Q) (k : ℕ)
    (y : Fin (k + 1) → ι) :
    ((cechComplexFunctor U).map φ).f k ≫ cechComplexFunctorπ U Q k y =
      cechComplexFunctorπ U P k y ≫ φ.app _ := by
  change (Limits.Pi.map fun i ↦ φ.app _) ≫ Pi.π _ y = _
  exact Pi.map_π _ _

end Preadditive

section Restrictions

variable {X : TopCat.{u}} {R : Type u'} [Ring R]
  (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)

/-- Restriction maps of a presheaf of modules on `Opens X` compose to the restriction along the
composite inclusion. -/
lemma map_map_apply {V W Z : (Opens X)ᵒᵖ} (f : V ⟶ W) (g : W ⟶ Z) (h : V ⟶ Z) (x : P.obj V) :
    P.map g (P.map f x) = P.map h x := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  congr 2

/-- Restriction along an endomorphism of an open is the identity. -/
lemma map_apply_self {V : (Opens X)ᵒᵖ} (h : V ⟶ V) (x : P.obj V) : P.map h x = x := by
  rw [Subsingleton.elim h (𝟙 V), P.map_id]
  rfl

end Restrictions

section ModuleCat

variable {X : TopCat.{max u w}} {ι : Type w} (U : ι → Opens X) {R : Type u'} [Ring R]
  (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{max u w} R)

/-- The infimum of a finite family of opens is contained in its categorical product. -/
lemma iInf_le_piObj {k : ℕ} (y : Fin (k + 1) → ι) : ⨅ l, U (y l) ≤ ∏ᶜ fun l ↦ U (y l) :=
  (Pi.lift fun l ↦ homOfLE (iInf_le (fun l ↦ U (y l)) l)).le

/-- The categorical product of a finite family of opens is contained in its infimum. -/
lemma piObj_le_iInf {k : ℕ} (y : Fin (k + 1) → ι) : ∏ᶜ (fun l ↦ U (y l)) ≤ ⨅ l, U (y l) :=
  le_iInf fun l ↦ (Pi.π (fun l ↦ U (y l)) l).le

/-- Elements of a term of `cechComplexFunctor U` are determined by their projections. -/
lemma cechComplexFunctor_ext {k : ℕ} {x x' : ((cechComplexFunctor U).obj P).X k}
    (h : ∀ y, cechComplexFunctorπ U P k y x = cechComplexFunctorπ U P k y x') : x = x' := by
  let Z := fun y : Fin (k + 1) → ι ↦ P.obj (op (∏ᶜ fun l ↦ U (y l)))
  refine ConcreteCategory.injective_of_mono_of_preservesPullback (ModuleCat.piIsoPi Z).hom ?_
  funext y
  have h₁ := ModuleCat.piIsoPi_hom_ker_subtype_apply Z y x
  have h₂ := ModuleCat.piIsoPi_hom_ker_subtype_apply Z y x'
  exact h₁.trans ((h y).trans h₂.symm)

/-- The projections of the element of a product of modules given by a family of elements. -/
lemma cechComplexFunctorπ_piIsoPi_inv {k : ℕ}
    (c : ∀ y : Fin (k + 1) → ι, P.obj (op (∏ᶜ fun l ↦ U (y l)))) (y : Fin (k + 1) → ι) :
    cechComplexFunctorπ U P k y
      ((ModuleCat.piIsoPi (fun y : Fin (k + 1) → ι ↦ P.obj (op (∏ᶜ fun l ↦ U (y l))))).inv c) =
      c y :=
  ModuleCat.piIsoPi_inv_kernel_ι_apply _ y c

/-- The degree `k` term of `cechComplexFunctor U` is the group of Čech cochains: a family of
sections of `P` over the products `∏ᶜ (U ∘ y)` is a family of sections over the infima. -/
noncomputable def cechComplexFunctorXAddEquiv (k : ℕ) :
    ((cechComplexFunctor U).obj P).X k ≃+
      CechCochain U (P ⋙ forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w}) k where
  toFun x y := P.map (homOfLE (iInf_le_piObj U y)).op (cechComplexFunctorπ U P k y x)
  invFun c := (ModuleCat.piIsoPi (fun y : Fin (k + 1) → ι ↦ P.obj (op (∏ᶜ fun l ↦ U (y l))))).inv
    fun y ↦ P.map (homOfLE (piObj_le_iInf U y)).op (c y)
  left_inv x := cechComplexFunctor_ext U P fun y ↦ by
    rw [cechComplexFunctorπ_piIsoPi_inv, map_map_apply P _ _ (𝟙 _), map_apply_self]
  right_inv c := funext fun y ↦ by
    dsimp only
    rw [cechComplexFunctorπ_piIsoPi_inv, map_map_apply P _ _ (𝟙 _), map_apply_self]
  map_add' x x' := funext fun y ↦ by
    dsimp only
    rw [map_add, map_add]
    rfl

@[simp]
lemma cechComplexFunctorXAddEquiv_apply (k : ℕ) (x : ((cechComplexFunctor U).obj P).X k)
    (y : Fin (k + 1) → ι) :
    cechComplexFunctorXAddEquiv U P k x y =
      P.map (homOfLE (iInf_le_piObj U y)).op (cechComplexFunctorπ U P k y x) :=
  rfl

/-- `TopCat.Presheaf.cechComplexFunctor_d_π`, for elements. -/
lemma cechComplexFunctorπ_d_apply (k : ℕ) (y : Fin (k + 2) → ι)
    (x : ((cechComplexFunctor U).obj P).X k) :
    cechComplexFunctorπ U P (k + 1) y (((cechComplexFunctor U).obj P).d k (k + 1) x) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        P.map (Pi.lift fun l ↦ Pi.π (fun l ↦ U (y l)) (i.succAbove l)).op
          (cechComplexFunctorπ U P k (y ∘ i.succAbove) x) := by
  rw [← ConcreteCategory.comp_apply, cechComplexFunctor_d_π]
  simp

/-- For a presheaf of modules `P`, the complex of abelian groups underlying Mathlib's Čech
complex `(cechComplexFunctor U).obj P` is the explicit Čech complex of the underlying presheaf
of abelian groups. -/
noncomputable def cechComplexFunctorIso :
    ((forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w}).mapHomologicalComplex _).obj
      ((cechComplexFunctor U).obj P) ≅
      (cechComplex U).obj (P ⋙ forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w}) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ (cechComplexFunctorXAddEquiv U P k).toAddCommGrpIso) (by
      rintro k _ rfl
      refine AddCommGrpCat.ext fun (x : ((cechComplexFunctor U).obj P).X k) ↦ funext fun y ↦ ?_
      change ((cechComplex U).obj
        (P ⋙ forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w})).d k (k + 1)
        (cechComplexFunctorXAddEquiv U P k x) y =
        cechComplexFunctorXAddEquiv U P (k + 1) (((cechComplexFunctor U).obj P).d k (k + 1) x) y
      rw [cechComplex_d_apply, cechComplexFunctorXAddEquiv_apply, cechComplexFunctorπ_d_apply,
        map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_zsmul, cechComplexFunctorXAddEquiv_apply]
      change _ • P.map _ (P.map _ _) = _ • P.map _ (P.map _ _)
      have h := (homOfLE ((iInf_le_iInf_comp U y i.succAbove).trans
        (iInf_le_piObj U (y ∘ i.succAbove)))).op
      rw [map_map_apply P _ _ h]
      exact congrArg _ (map_map_apply P _ _ h _).symm)

/-- The identification `TopCat.Presheaf.cechComplexFunctorIso` is natural in the presheaf. -/
@[reassoc]
lemma cechComplexFunctorIso_hom_naturality {Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{max u w} R}
    (φ : P ⟶ Q) :
    ((forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w}).mapHomologicalComplex _).map
      ((cechComplexFunctor U).map φ) ≫ (cechComplexFunctorIso U Q).hom =
      (cechComplexFunctorIso U P).hom ≫
        (cechComplex U).map
          (Functor.whiskerRight φ
            (forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w})) := by
  ext k : 1
  refine AddCommGrpCat.ext fun (x : ((cechComplexFunctor U).obj P).X k) ↦ funext fun y ↦ ?_
  change Q.map _ (cechComplexFunctorπ U Q k y (((cechComplexFunctor U).map φ).f k x)) =
    φ.app _ (P.map _ (cechComplexFunctorπ U P k y x))
  rw [← ConcreteCategory.comp_apply (((cechComplexFunctor U).map φ).f k),
    cechComplexFunctor_map_f_π, ConcreteCategory.comp_apply, NatTrans.naturality_apply]

/-- Multiplication by a scalar on a presheaf of modules induces multiplication by the scalar on
its Čech complex. -/
lemma cechComplexFunctor_map_smul_id {R : Type u'} [CommRing R]
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{max u w} R) (r : R) :
    (cechComplexFunctor U).map (r • 𝟙 P) = r • 𝟙 _ := by
  ext k : 1
  refine cechComplexFunctor_hom_ext U P fun y ↦ ?_
  rw [cechComplexFunctor_map_f_π, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f,
    Linear.smul_comp, Category.id_comp, NatTrans.app_smul, NatTrans.id_app, Linear.comp_smul,
    Category.comp_id]

end ModuleCat

section Homology

variable {X : TopCat.{max u w}} {ι : Type w} (U : ι → Opens X) {R : Type u'} [Ring R]
  (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{max u w} R)

/-- The homology of Mathlib's Čech complex of a presheaf of modules, as an abelian group, is
the homology of the explicit Čech complex of the underlying presheaf of abelian groups. -/
noncomputable def cechComplexFunctorHomologyIso (q : ℕ) :
    (forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w}).obj
      (((cechComplexFunctor U).obj P).homology q) ≅
      ((cechComplex U).obj
        (P ⋙ forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w})).homology q :=
  ((((cechComplexFunctor U).obj P).sc q).mapHomologyIso (forget₂ _ _)).symm ≪≫
    HomologicalComplex.homologyMapIso (cechComplexFunctorIso U P) q

/-- The identification `TopCat.Presheaf.cechComplexFunctorHomologyIso` is natural in the
presheaf. -/
lemma cechComplexFunctorHomologyIso_hom_naturality
    {Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{max u w} R}
    (φ : P ⟶ Q) (q : ℕ) :
    (forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w}).map
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map φ) q) ≫
      (cechComplexFunctorHomologyIso U Q q).hom =
      (cechComplexFunctorHomologyIso U P q).hom ≫ HomologicalComplex.homologyMap
        ((cechComplex U).map (Functor.whiskerRight φ
          (forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w})))
          q := by
  have h := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ q).map ((cechComplexFunctor U).map φ))
    (forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w})
  have h₂ := congrArg (fun f ↦ HomologicalComplex.homologyMap f q)
    (cechComplexFunctorIso_hom_naturality U P φ)
  simp only [HomologicalComplex.homologyMap_comp] at h₂
  dsimp only [cechComplexFunctorHomologyIso, Iso.trans_hom, Iso.symm_hom,
    HomologicalComplex.homologyMapIso_hom]
  rw [Category.assoc]
  erw [reassoc_of% h]
  exact congrArg _ h₂

set_option maxHeartbeats 800000 in
/-- Under `TopCat.Presheaf.cechComplexFunctorHomologyIso`, multiplication by a scalar on the
homology of Mathlib's Čech complex is the map induced by multiplication by the scalar on the
presheaf. -/
lemma cechComplexFunctorHomologyIso_hom_smul {R : Type u'} [CommRing R]
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{max u w} R) (q : ℕ) (r : R)
    (x : ((cechComplexFunctor U).obj P).homology q) :
    (cechComplexFunctorHomologyIso U P q).hom
        (r • x : ((cechComplexFunctor U).obj P).homology q) =
      HomologicalComplex.homologyMap ((cechComplex U).map
        (Functor.whiskerRight (r • 𝟙 P)
          (forget₂ (ModuleCat.{max u w} R) AddCommGrpCat.{max u w}))) q
          ((cechComplexFunctorHomologyIso U P q).hom x) := by
  have h := ConcreteCategory.congr_hom
    (cechComplexFunctorHomologyIso_hom_naturality U P (r • 𝟙 P) q) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  rw [← h, cechComplexFunctor_map_smul_id]
  congr 1
  have e : (HomologicalComplex.shortComplexFunctor _ _ q).map
      (r • 𝟙 ((cechComplexFunctor U).obj P)) =
        r • 𝟙 (((cechComplexFunctor U).obj P).sc q) := by
    ext <;> rfl
  have : HomologicalComplex.homologyMap (r • 𝟙 ((cechComplexFunctor U).obj P)) q =
      r • 𝟙 (((cechComplexFunctor U).obj P).homology q) := by
    change ShortComplex.homologyMap _ = _
    rw [e, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
    rfl
  rw [this]
  rfl

end Homology

end TopCat.Presheaf
