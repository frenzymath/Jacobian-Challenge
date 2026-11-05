import Jacobian.AlgebraicGeometry.Modules.Free
import Jacobian.AlgebraicGeometry.Modules.FreeGeneratorPullback
import Jacobian.AlgebraicGeometry.Modules.Sections
import Jacobian.Algebra.Category.ModuleCat.Sheaf.FreeSections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrices of morphisms of finite free module sheaves

Morphisms of finite free module sheaves are matrices of global functions. Their matrices commute with composition and pullback; coordinates on sections identify their rank with the rank of the induced linear map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits SheafOfModules
open scoped Matrix

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable def freeMatrix {I J : Type u} [DecidableEq J]
    (φ : free (R := Y.ringCatSheaf) I ⟶ free J) : Matrix J I Γ(Y, ⊤) :=
  Matrix.of fun j i ↦ Hom.app (ιFree i ≫ φ ≫ freeπ j) ⊤ (1 : Γ(Y, ⊤))

@[simp]
lemma freeMatrix_zero {I J : Type u} [DecidableEq J] :
    freeMatrix (0 : free (R := Y.ringCatSheaf) I ⟶ free J) = 0 := by
  ext j i
  simp [freeMatrix]

@[reassoc (attr := simp)]
lemma pullback_map_ιFree_pullbackFreeIso_hom (g : Y ⟶ X) {I : Type u} (i : I) :
    (pullback g).map (ιFree i) ≫ (pullbackFreeIso g I).hom =
      (pullbackObjUnitIso g).hom ≫ ιFree i :=
  SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ i

/-- The inverse form of `pullback_map_ιFree_pullbackFreeIso_hom`. -/
lemma ιFree_pullbackFreeIso_inv (g : Y ⟶ X) {I : Type u} (i : I) :
    ιFree i ≫ (pullbackFreeIso g I).inv =
      (pullbackObjUnitIso g).inv ≫ (pullback g).map (ιFree i) := by
  rw [Iso.comp_inv_eq, Category.assoc, pullback_map_ιFree_pullbackFreeIso_hom,
    Iso.inv_hom_id_assoc]

/-- The pullback of the projection onto the `i`-th summand of a free module is the projection onto
the `i`-th summand of the pulled back free module: the square
```
g^* 𝒪_X^{(I)}
     |                               |
pullbackFreeIso                      ≅
     v                               v
  𝒪_Y^{(I)}
```
commutes. -/
@[reassoc]
lemma pullbackFreeIso_hom_freeπ (g : Y ⟶ X) {I : Type u} [DecidableEq I] (i : I) :
    (pullbackFreeIso g I).hom ≫ freeπ i =
      (pullback g).map (freeπ i) ≫ (pullbackObjUnitIso g).hom := by
  rw [← cancel_epi (pullbackFreeIso g I).inv, Iso.inv_hom_id_assoc]
  refine free_hom_ext fun k ↦ ?_
  rw [ιFree_freeπ, reassoc_of% (ιFree_pullbackFreeIso_inv g k), ← Functor.map_comp_assoc,
    ιFree_freeπ]
  split_ifs
  · rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  · have hz : (pullback g).map (0 : Modules.unit X ⟶ Modules.unit X) = 0 :=
      (pullback g).map_zero _ _
    rw [hz, zero_comp, comp_zero]

/-- The matrix of the pullback `g^* φ` of a morphism `φ` of free modules is the image of the matrix
of `φ` under `g^♯ : Γ(X, ⊤) → Γ(Y, ⊤)`. -/
lemma freeMatrix_pullback (g : Y ⟶ X) {I J : Type u} [DecidableEq J]
    (φ : free (R := X.ringCatSheaf) I ⟶ free J) :
    freeMatrix ((pullbackFreeIso g I).inv ≫ (pullback g).map φ ≫ (pullbackFreeIso g J).hom) =
      (freeMatrix φ).map g.appTop := by
  ext j i
  simp only [freeMatrix, Matrix.of_apply, Matrix.map_apply, Category.assoc,
    pullbackFreeIso_hom_freeπ, reassoc_of% (ιFree_pullbackFreeIso_inv g i)]
  simp only [← Functor.map_comp_assoc]
  exact pullbackObjUnitIso_conj_app_top g _

lemma unit_hom_app_top (e : Modules.unit Y ⟶ Modules.unit Y) (c : Γ(Y, ⊤)) :
    Hom.app e ⊤ c = c • Hom.app e ⊤ (1 : Γ(Y, ⊤)) := by
  rw [← Hom.app_smul]
  congr 1
  exact (mul_one c).symm

lemma unit_hom_app_opens (e : Modules.unit Y ⟶ Modules.unit Y) (W : Y.Opens) (c : Γ(Y, W)) :
    Hom.app e W c = c * Y.presheaf.map (homOfLE le_top).op (Hom.app e ⊤ (1 : Γ(Y, ⊤))) := by
  have h1 : Hom.app e W c = c • Hom.app e W (1 : Γ(Y, W)) := by
    rw [← Hom.app_smul]
    congr 1
    exact (mul_one c).symm
  rw [h1]
  congr 1
  have h2 : Hom.app e W
      ((Modules.unit Y).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (1 : Γ(Y, ⊤))) =
      (Modules.unit Y).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (Hom.app e ⊤ (1 : Γ(Y, ⊤))) :=
    PresheafOfModules.naturality_apply e.val (homOfLE (le_top : W ≤ ⊤)).op (1 : Γ(Y, ⊤))
  rw [show (Modules.unit Y).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (1 : Γ(Y, ⊤)) =
    (1 : Γ(Y, W)) from map_one (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom] at h2
  exact h2

/-- In the coordinates `freeSectionsLinearEquiv`, a morphism of free modules acts on sections over
`W` as multiplication by its matrix, restricted to `W`. -/
lemma freeSectionsLinearEquiv_app_opens (W : Y.Opens) {I J : Type u} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (φ : free (R := Y.ringCatSheaf) I ⟶ free J)
    (x : Γ(free I, W)) :
    (freeSectionsLinearEquiv (R := Y.ringCatSheaf) J (Opposite.op W)) (Hom.app φ W x) =
      (freeMatrix φ).map (Y.presheaf.map (homOfLE le_top).op).hom *ᵥ
        (freeSectionsLinearEquiv (R := Y.ringCatSheaf) I (Opposite.op W)) x := by
  obtain ⟨c, rfl⟩ := ((freeSectionsLinearEquiv (R := Y.ringCatSheaf) I (Opposite.op W))).symm.surjective x
  rw [LinearEquiv.apply_symm_apply]
  ext j
  change Hom.app (freeπ j) W (Hom.app φ W
    (∑ i, Hom.app (ιFree (R := Y.ringCatSheaf) i) W (c i))) = _
  rw [map_sum, map_sum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change Hom.app (ιFree i ≫ φ ≫ freeπ j) W (c i) = _
  rw [unit_hom_app_opens, mul_comm]
  rfl

/-- The global function by which an endomorphism of `𝒪_Y` multiplies: its value at `1`. -/
noncomputable def unitValue (a : Modules.unit Y ⟶ Modules.unit Y) : Γ(Y, ⊤) :=
  Hom.app a ⊤ (1 : Γ(Y, ⊤))

/-- The value at `1` of a composite of endomorphisms of `𝒪_Y` is the product of the values. -/
lemma unitValue_comp (a b : Modules.unit Y ⟶ Modules.unit Y) :
    unitValue (a ≫ b) = unitValue a * unitValue b := by
  unfold unitValue
  rw [Hom.comp_app, ConcreteCategory.comp_apply, unit_hom_app_top]
  rfl

lemma freeMatrix_apply {I J : Type u} [DecidableEq J]
    (φ : free (R := Y.ringCatSheaf) I ⟶ free J) (j : J) (i : I) :
    freeMatrix φ j i = unitValue (ιFree i ≫ φ ≫ freeπ j) :=
  rfl

lemma unitValue_sum {ι : Type*} (s : Finset ι) (a : ι → (Modules.unit Y ⟶ Modules.unit Y)) :
    unitValue (∑ i ∈ s, a i) = ∑ i ∈ s, unitValue (a i) :=
  SheafOfModules.sum_val_app_apply s a (Opposite.op ⊤) _

/-- The matrix of a composite is the product of the matrices. -/
lemma freeMatrix_comp {I J K : Type u} [Fintype J] [DecidableEq J] [DecidableEq K]
    (φ : free (R := Y.ringCatSheaf) I ⟶ free J) (ψ : free (R := Y.ringCatSheaf) J ⟶ free K) :
    freeMatrix (φ ≫ ψ) = freeMatrix ψ * freeMatrix φ := by
  ext k i
  have h : ιFree i ≫ (φ ≫ ψ) ≫ freeπ k =
      ∑ j, (ιFree i ≫ φ ≫ freeπ j) ≫ (ιFree j ≫ ψ ≫ freeπ k) := by
    calc ιFree i ≫ (φ ≫ ψ) ≫ freeπ k =
        ιFree i ≫ φ ≫ (∑ j, freeπ j ≫ ιFree j) ≫ ψ ≫ freeπ k := by
          rw [sum_freeπ_ιFree, Category.id_comp, Category.assoc]
      _ = _ := by simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  rw [Matrix.mul_apply, freeMatrix_apply, h, unitValue_sum]
  exact Finset.sum_congr rfl fun j _ ↦ (unitValue_comp _ _).trans (mul_comm _ _)

@[simp]
lemma unitValue_id : unitValue (𝟙 (Modules.unit Y)) = 1 :=
  rfl

@[simp]
lemma unitValue_zero : unitValue (0 : Modules.unit Y ⟶ Modules.unit Y) = 0 :=
  rfl

lemma unitValue_add (a b : Modules.unit Y ⟶ Modules.unit Y) :
    unitValue (a + b) = unitValue a + unitValue b :=
  rfl

lemma unitValue_sub (a b : Modules.unit Y ⟶ Modules.unit Y) :
    unitValue (a - b) = unitValue a - unitValue b :=
  rfl

@[simp]
lemma unitValue_smulHom (a : Γ(Y, ⊤)) : unitValue ((Modules.unit Y).smulHom a) = a := by
  unfold unitValue
  rw [smulHom_app_apply, Subsingleton.elim (homOfLE le_top) (𝟙 (⊤ : Y.Opens)), op_id,
    CategoryTheory.Functor.map_id]
  exact mul_one a

/-- The matrix of the identity is the identity matrix. -/
@[simp]
lemma freeMatrix_id {I : Type u} [DecidableEq I] :
    freeMatrix (𝟙 (free (R := Y.ringCatSheaf) I)) = 1 := by
  ext j i
  rw [freeMatrix_apply, Category.id_comp, ιFree_freeπ, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl]
    exact unitValue_id
  · simp [h, Ne.symm h]

/-- The matrix of a sum is the sum of the matrices. -/
lemma freeMatrix_add {I J : Type u} [DecidableEq J] (φ ψ : free (R := Y.ringCatSheaf) I ⟶ free J) :
    freeMatrix (φ + ψ) = freeMatrix φ + freeMatrix ψ := by
  ext j i
  rw [freeMatrix_apply, Preadditive.add_comp, Preadditive.comp_add, unitValue_add]
  rfl

/-- The matrix of a difference is the difference of the matrices. -/
lemma freeMatrix_sub {I J : Type u} [DecidableEq J] (φ ψ : free (R := Y.ringCatSheaf) I ⟶ free J) :
    freeMatrix (φ - ψ) = freeMatrix φ - freeMatrix ψ := by
  ext j i
  rw [freeMatrix_apply, Preadditive.sub_comp, Preadditive.comp_sub, unitValue_sub]
  rfl

/-- A morphism of free modules of finite rank is determined by its matrix. -/
lemma freeMatrix_injective {I J : Type u} [Finite I] [Finite J] [DecidableEq J] :
    Function.Injective
      (freeMatrix : (free (R := Y.ringCatSheaf) I ⟶ free J) → Matrix J I Γ(Y, ⊤)) := by
  classical
  have := Fintype.ofFinite I
  have := Fintype.ofFinite J
  intro φ ψ h
  refine hom_ext _ _ fun W ↦ ?_
  ext x
  apply (freeSectionsLinearEquiv (R := Y.ringCatSheaf) J (Opposite.op W)).injective
  rw [freeSectionsLinearEquiv_app_opens, freeSectionsLinearEquiv_app_opens, h]

/-- The morphism of free modules of finite rank with a given matrix. -/
noncomputable def freeHomOfMatrix {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix J I Γ(Y, ⊤)) : free (R := Y.ringCatSheaf) I ⟶ free J :=
  ∑ i, ∑ j, freeπ i ≫ (Modules.unit Y).smulHom (A j i) ≫ ιFree j

@[simp]
lemma freeMatrix_freeHomOfMatrix {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (A : Matrix J I Γ(Y, ⊤)) : freeMatrix (freeHomOfMatrix A) = A := by
  ext j i
  rw [freeMatrix_apply, freeHomOfMatrix]
  simp_rw [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  rw [unitValue_sum, Finset.sum_eq_single i, unitValue_sum, Finset.sum_eq_single j]
  · rw [ιFree_freeπ_assoc, if_pos rfl, Category.id_comp, ιFree_freeπ, if_pos rfl,
      Category.comp_id, unitValue_smulHom]
  · intro j' _ hj
    rw [ιFree_freeπ, if_neg hj, comp_zero, comp_zero, comp_zero, unitValue_zero]
  · simp
  · intro i' _ hi
    rw [unitValue_sum]
    refine Finset.sum_eq_zero fun j' _ ↦ ?_
    rw [ιFree_freeπ_assoc, if_neg (Ne.symm hi), zero_comp, unitValue_zero]
  · simp

/-- Every morphism of free modules of finite rank is the morphism of its matrix. -/
@[simp]
lemma freeHomOfMatrix_freeMatrix {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (φ : free (R := Y.ringCatSheaf) I ⟶ free J) :
    freeHomOfMatrix (freeMatrix φ) = φ :=
  freeMatrix_injective (freeMatrix_freeHomOfMatrix _)

/-- In the coordinates `freeSectionsLinearEquiv`, a morphism of free modules acts on global sections as
multiplication by its matrix. -/
lemma freeSectionsLinearEquiv_app {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (φ : free (R := Y.ringCatSheaf) I ⟶ free J) (x : Γ(free I, ⊤)) :
    (freeSectionsLinearEquiv (R := Y.ringCatSheaf) J (Opposite.op (⊤ : Y.Opens))) (Hom.app φ ⊤ x) = freeMatrix φ *ᵥ (freeSectionsLinearEquiv (R := Y.ringCatSheaf) I (Opposite.op (⊤ : Y.Opens))) x := by
  simpa using freeSectionsLinearEquiv_app_opens (Y := Y) ⊤ φ x

/-- The rank of the matrix of a morphism of free modules of finite rank is the dimension of the
image of the global sections. -/
lemma rank_freeMatrix {I J : Type u} [Fintype I] [Finite J] [DecidableEq J]
    (φ : free (R := Y.ringCatSheaf) I ⟶ free J) :
    (freeMatrix φ).rank = Module.finrank Γ(Y, ⊤) (LinearMap.range (Hom.appₗ φ ⊤)) := by
  classical
  have := Fintype.ofFinite J
  let sourceCoordinates : Γ(free (R := Y.ringCatSheaf) I, ⊤) ≃ₗ[Γ(Y, ⊤)] (I → Γ(Y, ⊤)) :=
    freeSectionsLinearEquiv (R := Y.ringCatSheaf) I (Opposite.op ⊤)
  let targetCoordinates : Γ(free (R := Y.ringCatSheaf) J, ⊤) ≃ₗ[Γ(Y, ⊤)] (J → Γ(Y, ⊤)) :=
    freeSectionsLinearEquiv (R := Y.ringCatSheaf) J (Opposite.op ⊤)
  have h : (freeMatrix φ).mulVecLin = targetCoordinates.toLinearMap ∘ₗ Hom.appₗ φ ⊤ ∘ₗ
      sourceCoordinates.symm.toLinearMap := by
    refine LinearMap.ext fun c ↦ ?_
    change (freeMatrix φ).mulVec c =
      targetCoordinates (Hom.app φ ⊤ (sourceCoordinates.symm c))
    have action := (freeSectionsLinearEquiv_app φ (sourceCoordinates.symm c)).symm
    change freeMatrix φ *ᵥ sourceCoordinates (sourceCoordinates.symm c) =
      targetCoordinates (Hom.app φ ⊤ (sourceCoordinates.symm c)) at action
    rw [sourceCoordinates.apply_symm_apply] at action
    exact action
  rw [Matrix.rank, h, LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq]

end AlgebraicGeometry.Scheme.Modules
