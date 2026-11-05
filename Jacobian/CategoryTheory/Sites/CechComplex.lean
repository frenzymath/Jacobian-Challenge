import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

set_option backward.isDefEq.respectTransparency false

/-!
# Functoriality of the Čech complex in the coefficients

Let `U : ι → C` be a family of objects of a category with finite products, and let
`cechComplexFunctor U : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` be the Čech complex functor. For an
additive functor `G : A ⥤ B` preserving products, applying `G` degreewise to the Čech complex of
a presheaf `P` gives the Čech complex of `P ⋙ G`.

When `C` has a terminal object `T`, the Čech complex of `P` is augmented by
`P(T) ⟶ ∏ᵢ P(U i)`, the product of the restriction maps.

## Main definitions

- `CategoryTheory.cechComplexFunctorMapIso`: the isomorphism
  `G(Č(U, P)) ≅ Č(U, P ⋙ G)`.
- `CategoryTheory.cechAugmentation`: the augmentation `P(T) ⟶ Č⁰(U, P)`.
-/

section
universe w v u

namespace CategoryTheory

open Limits Opposite Simplicial

namespace Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C] {A B : Type*} [Category* A] [Category* B]
  [HasProducts.{w} A] [HasProducts.{w} B] (G : A ⥤ B)
  [∀ J : Type w, PreservesLimitsOfShape (Discrete J) G]

/-- A functor preserving products commutes with the evaluation of presheaves on formal
coproducts. -/
noncomputable def evalOpCompIso (P : Cᵒᵖ ⥤ A) :
    (evalOp.{w} C A).obj P ⋙ G ≅ (evalOp.{w} C B).obj (P ⋙ G) :=
  NatIso.ofComponents (fun X ↦ asIso (piComparison G _)) (fun {X Y} f ↦ by
    refine Pi.hom_ext _ _ fun i ↦ ?_
    simp only [Functor.comp_obj, Functor.comp_map, asIso_hom, Category.assoc,
      piComparison_comp_π, ← G.map_comp, evalOp_obj_map, Pi.lift_comp_π, Functor.comp_map]
    rw [G.map_comp, ← Category.assoc, piComparison_comp_π])

@[simp]
lemma evalOpCompIso_hom_app (P : Cᵒᵖ ⥤ A) (X : (FormalCoproduct.{w} C)ᵒᵖ) :
    (evalOpCompIso G P).hom.app X = piComparison G _ :=
  rfl

end Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} (U : ι → C)
  {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  [HasProducts.{w} A] [HasProducts.{w} B]

section

/-- The differential of the Čech complex is the alternating sum of the coface maps. -/
lemma cechComplexFunctor_obj_d (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    ((cechComplexFunctor U).obj P).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P).δ i :=
  CochainComplex.of_d (fun m ↦ ((FormalCoproduct.cosimplicialObjectFunctor
    (FormalCoproduct.mk _ U).cech).obj P).obj ⦋m⦌)
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD _) n

variable (G : A ⥤ B) [G.Additive] [∀ J : Type w, PreservesLimitsOfShape (Discrete J) G]

/-- An additive functor `G` preserving products commutes with the Čech complex functor:
`G(Č(U, P)) ≅ Č(U, P ⋙ G)`. -/
noncomputable def cechComplexFunctorMapIso (P : Cᵒᵖ ⥤ A) :
    (G.mapHomologicalComplex _).obj ((cechComplexFunctor U).obj P) ≅
      (cechComplexFunctor U).obj (P ⋙ G) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ asIso (piComparison G
      (fun i ↦ P.obj (op (((FormalCoproduct.mk _ U).cech.obj (op ⦋n⦌)).obj i))))) (by
      rintro i j (rfl : i + 1 = j)
      rw [Functor.mapHomologicalComplex_obj_d, cechComplexFunctor_obj_d,
        cechComplexFunctor_obj_d, Functor.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Functor.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
      congr 1
      exact ((FormalCoproduct.evalOpCompIso G P).hom.naturality _).symm)

@[simp]
lemma cechComplexFunctorMapIso_hom_f (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    (cechComplexFunctorMapIso U G P).hom.f n = piComparison G _ :=
  rfl

end

variable {T : C} (hT : IsTerminal T)

/-- The augmentation `P(T) ⟶ Č⁰(U, P) = ∏ᵢ P(U i)` of the Čech complex, for a terminal
object `T`: the product of the restriction maps. -/
noncomputable def cechAugmentation (P : Cᵒᵖ ⥤ A) :
    P.obj (op T) ⟶ ((cechComplexFunctor U).obj P).X 0 :=
  Pi.lift fun _ ↦ P.map (hT.from _).op

@[reassoc (attr := simp)]
lemma cechAugmentation_π (P : Cᵒᵖ ⥤ A) (i) :
    cechAugmentation U hT P ≫ Pi.π _ i = P.map (hT.from _).op :=
  Pi.lift_comp_π _ _

lemma cechAugmentation_δ (P : Cᵒᵖ ⥤ A) (i : Fin 2) :
    cechAugmentation U hT P ≫
      ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P).δ i =
      Pi.lift fun _ ↦ P.map (hT.from _).op := by
  refine Pi.hom_ext _ _ fun j ↦ ?_
  rw [Category.assoc, Pi.lift_comp_π]
  erw [Pi.lift_comp_π]
  rw [← Category.assoc, cechAugmentation_π, ← P.map_comp, ← op_comp]
  congr 2
  exact hT.hom_ext _ _

@[reassoc (attr := simp)]
lemma cechAugmentation_d (P : Cᵒᵖ ⥤ A) :
    cechAugmentation U hT P ≫ ((cechComplexFunctor U).obj P).d 0 1 = 0 := by
  rw [cechComplexFunctor_obj_d U P 0, Fin.sum_univ_two, Preadditive.comp_add,
    Preadditive.comp_zsmul, Preadditive.comp_zsmul, cechAugmentation_δ, cechAugmentation_δ]
  simp

lemma cechComplexFunctor_map_f {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) (n : ℕ) :
    ((cechComplexFunctor U).map φ).f n =
      Limits.Pi.map (fun i ↦ φ.app (op (((FormalCoproduct.mk _ U).cech.obj (op ⦋n⦌)).obj i))) :=
  rfl

@[reassoc]
lemma cechAugmentation_naturality {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) :
    cechAugmentation U hT P ≫ ((cechComplexFunctor U).map φ).f 0 =
      φ.app _ ≫ cechAugmentation U hT Q := by
  refine Pi.hom_ext _ _ fun j ↦ ?_
  rw [Category.assoc, cechComplexFunctor_map_f]
  erw [Pi.map_π, Pi.lift_π_assoc, Category.assoc, Pi.lift_comp_π]
  exact φ.naturality _

lemma map_cechAugmentation_comp (G : A ⥤ B) [G.Additive]
    [∀ J : Type w, PreservesLimitsOfShape (Discrete J) G] (P : Cᵒᵖ ⥤ A) :
    G.map (cechAugmentation U hT P) ≫ (cechComplexFunctorMapIso U G P).hom.f 0 =
      cechAugmentation U hT (P ⋙ G) := by
  refine Pi.hom_ext _ _ fun j ↦ ?_
  rw [Category.assoc, cechComplexFunctorMapIso_hom_f]
  erw [piComparison_comp_π, Pi.lift_comp_π]
  rw [← G.map_comp]
  erw [Pi.lift_comp_π]
  rfl

end CategoryTheory
