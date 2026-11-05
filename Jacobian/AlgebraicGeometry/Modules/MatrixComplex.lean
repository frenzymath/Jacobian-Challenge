import Jacobian.AlgebraicGeometry.Modules.FiniteFreeComplex
import Jacobian.AlgebraicGeometry.Modules.HomSection
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Complexes of free module sheaves from matrices

Matrices of global functions define differentials between finite free module
sheaves. Pullback applies the map on global functions to the matrices. Chosen
bases of an algebraic complex therefore give a finite free sheaf complex after
any homomorphism from the coefficient ring to global functions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits SheafOfModules

namespace CochainComplex

variable {R : Type u} [CommRing R] {indices : ℤ → Type u}
  [∀ degree, Fintype (indices degree)] [∀ degree, DecidableEq (indices degree)]
  (complex : CochainComplex (ModuleCat.{u} R) ℤ)
  (basis : ∀ degree, Module.Basis (indices degree) R (complex.X degree))

/-- The matrix of a differential in chosen bases. -/
def differentialMatrix (degree : ℤ) : Matrix (indices (degree + 1)) (indices degree) R :=
  LinearMap.toMatrix (basis degree) (basis (degree + 1))
    (complex.d degree (degree + 1)).hom

lemma differentialMatrix_mul (degree : ℤ) :
    complex.differentialMatrix basis (degree + 1) * complex.differentialMatrix basis degree = 0 := by
  rw [differentialMatrix, differentialMatrix, ← LinearMap.toMatrix_comp,
    ← ModuleCat.hom_comp, complex.d_comp_d, ModuleCat.hom_zero, map_zero]

end CochainComplex

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}}

/-- The morphism from a finite free sheaf with prescribed images of its basis vectors. -/
def freeHomOfSections (M : Y.Modules) {indices : Type u} [Fintype indices]
    [DecidableEq indices] (sections : indices → Γ(M, ⊤)) :
    free (R := Y.ringCatSheaf) indices ⟶ M :=
  ∑ index, freeπ index ≫ homOfGlobalSection M (sections index)

@[reassoc (attr := simp)]
lemma ιFree_freeHomOfSections (M : Y.Modules) {indices : Type u} [Fintype indices]
    [DecidableEq indices] (sections : indices → Γ(M, ⊤)) (index : indices) :
    ιFree index ≫ freeHomOfSections M sections = homOfGlobalSection M (sections index) := by
  rw [freeHomOfSections, Preadditive.comp_sum, Finset.sum_eq_single index]
  · rw [ιFree_freeπ_assoc, if_pos rfl, Category.id_comp]
  · intro otherIndex _ distinct
    rw [ιFree_freeπ_assoc, if_neg (Ne.symm distinct), zero_comp]
  · simp

/-- Sections of the morphism with prescribed global basis images. -/
lemma freeHomOfSections_app (M : Y.Modules) {indices : Type u} [Fintype indices]
    [DecidableEq indices] (sections : indices → Γ(M, ⊤)) (openSubset : Y.Opens)
    (sectionValue : Γ(free (R := Y.ringCatSheaf) indices, openSubset)) :
    Hom.app (freeHomOfSections M sections) openSubset sectionValue =
      ∑ index, @SMul.smul Γ(Y, openSubset) Γ(M, openSubset) inferInstance
        (freeSectionsLinearEquiv (R := Y.ringCatSheaf) indices
          (Opposite.op openSubset) sectionValue index)
        (M.presheaf.map (homOfLE (le_top : openSubset ≤ ⊤)).op (sections index)) := by
  rw [freeHomOfSections, Hom.sum_app_apply]
  refine Finset.sum_congr rfl fun index _ ↦ ?_
  rw [Hom.comp_app, ConcreteCategory.comp_apply, homOfGlobalSection_app]
  rfl

/-- A column of a matrix specifies the image of the corresponding free summand. -/
@[reassoc]
lemma ιFree_freeHomOfMatrix {sourceIndices targetIndices : Type u}
    [Fintype sourceIndices] [DecidableEq sourceIndices] [Fintype targetIndices]
    (matrix : Matrix targetIndices sourceIndices Γ(Y, ⊤)) (index : sourceIndices) :
    ιFree index ≫ freeHomOfMatrix matrix =
      ∑ targetIndex, (Modules.unit Y).smulHom (matrix targetIndex index) ≫ ιFree targetIndex := by
  rw [freeHomOfMatrix, Preadditive.comp_sum, Finset.sum_eq_single index]
  · rw [Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun targetIndex _ ↦ ?_
    rw [ιFree_freeπ_assoc, if_pos rfl, Category.id_comp]
  · intro otherIndex _ distinct
    rw [Preadditive.comp_sum]
    refine Finset.sum_eq_zero fun targetIndex _ ↦ ?_
    rw [ιFree_freeπ_assoc, if_neg (Ne.symm distinct), zero_comp]
  · simp

lemma homOfGlobalSection_app_top_one (M : Y.Modules) (sectionValue : Γ(M, ⊤)) :
    (homOfGlobalSection M sectionValue).app ⊤ (1 : Γ(Y, ⊤)) = sectionValue := by
  rw [homOfGlobalSection_app_one, presheaf_map_id_apply]

variable {indices : ℤ → Type u} [∀ degree, Fintype (indices degree)]
  [∀ degree, DecidableEq (indices degree)]

/-- The free sheaf complex whose successive differentials have the given matrices. -/
def freeComplex (matrices : ∀ degree : ℤ,
    Matrix (indices (degree + 1)) (indices degree) Γ(Y, ⊤))
    (square_zero : ∀ degree, matrices (degree + 1) * matrices degree = 0) :
    CochainComplex Y.Modules ℤ :=
  CochainComplex.of (fun degree ↦ free (R := Y.ringCatSheaf) (indices degree))
    (fun degree ↦ freeHomOfMatrix (matrices degree))
    (fun degree ↦ freeMatrix_injective (by
      rw [freeMatrix_comp, freeMatrix_freeHomOfMatrix, freeMatrix_freeHomOfMatrix,
        square_zero, freeMatrix_zero]))

variable (matrices : ∀ degree : ℤ,
    Matrix (indices (degree + 1)) (indices degree) Γ(Y, ⊤))
  (square_zero : ∀ degree, matrices (degree + 1) * matrices degree = 0)

lemma freeComplex_X (degree : ℤ) :
    (freeComplex matrices square_zero).X degree = free (R := Y.ringCatSheaf) (indices degree) :=
  rfl

lemma freeComplex_d (degree : ℤ) :
    (freeComplex matrices square_zero).d degree (degree + 1) =
      freeHomOfMatrix (matrices degree) :=
  CochainComplex.of_d (fun degree ↦ free (R := Y.ringCatSheaf) (indices degree))
    (fun degree ↦ freeHomOfMatrix (matrices degree)) degree

lemma freeComplex_d_natCast (degree : ℕ) :
    (freeComplex matrices square_zero).d degree (degree + 1 : ℕ) =
      freeHomOfMatrix (matrices degree) :=
  freeComplex_d matrices square_zero degree

omit [∀ degree, DecidableEq (indices degree)] in
include square_zero in
lemma map_appTop_mul_eq_zero {Z : Scheme.{u}} (morphism : Z ⟶ Y) (degree : ℤ) :
    (matrices (degree + 1)).map morphism.appTop.hom *
      (matrices degree).map morphism.appTop.hom = 0 := by
  rw [← Matrix.map_mul, square_zero degree, Matrix.map_zero _ (map_zero _)]

/-- Pullback of a matrix complex applies the map on global functions to each matrix. -/
def pullbackFreeComplexIso {Z : Scheme.{u}} (morphism : Z ⟶ Y) :
    ((pullback morphism).mapHomologicalComplex _).obj (freeComplex matrices square_zero) ≅
      freeComplex (fun degree ↦ (matrices degree).map morphism.appTop.hom)
        (map_appTop_mul_eq_zero matrices square_zero morphism) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun degree ↦ pullbackFreeIso morphism (indices degree)) (by
      rintro degree _ rfl
      have compatibility :
          (pullbackFreeIso morphism (indices degree)).inv ≫
            (pullback morphism).map (freeHomOfMatrix (matrices degree)) ≫
              (pullbackFreeIso morphism (indices (degree + 1))).hom =
                freeHomOfMatrix ((matrices degree).map morphism.appTop.hom) :=
        freeMatrix_injective (by
          rw [freeMatrix_pullback, freeMatrix_freeHomOfMatrix, freeMatrix_freeHomOfMatrix])
      rw [Functor.mapHomologicalComplex_obj_d, freeComplex_d, freeComplex_d,
        ← compatibility, Iso.hom_inv_id_assoc])

/-- A morphism from a matrix complex, specified by global basis images satisfying
the differential relations. -/
def freeComplexHom (target : CochainComplex Y.Modules ℕ)
    (sections : ∀ degree : ℕ, indices degree → Γ(target.X degree, ⊤))
    (compatibility : ∀ (degree : ℕ) (index : indices degree),
      (target.d degree (degree + 1)).app ⊤ (sections degree index) =
        ∑ targetIndex : indices ((degree : ℤ) + 1),
          matrices degree targetIndex index • sections (degree + 1) targetIndex) :
    (freeComplex matrices square_zero).restriction ComplexShape.embeddingUpNat ⟶ target where
  f degree := freeHomOfSections (target.X degree) (sections degree)
  comm' := by
    rintro degree _ rfl
    have differential :
        ((freeComplex matrices square_zero).restriction ComplexShape.embeddingUpNat).d
          degree (degree + 1) = freeHomOfMatrix (matrices degree) :=
      freeComplex_d_natCast matrices square_zero degree
    rw [differential]
    symm
    refine free_hom_ext fun index ↦ unit_hom_ext ?_
    rw [ιFree_freeHomOfSections_assoc, ιFree_freeHomOfMatrix_assoc, Preadditive.sum_comp,
      Hom.sum_app_apply, Hom.comp_app (homOfGlobalSection _ _),
      ConcreteCategory.comp_apply,
      homOfGlobalSection_app_top_one, compatibility]
    refine Finset.sum_congr rfl fun targetIndex _ ↦ ?_
    rw [Category.assoc, ιFree_freeHomOfSections, Hom.comp_app, ConcreteCategory.comp_apply,
      smulHom_app_apply, homOfGlobalSection_app, presheaf_map_id_apply]
    rw [smul_eq_mul, mul_one]
    rw [Subsingleton.elim (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)) (𝟙 (⊤ : Y.Opens)),
      CategoryTheory.op_id,
      CategoryTheory.Functor.map_id Y.presheaf (Opposite.op ⊤), ConcreteCategory.id_apply]

section Basis

variable {R : Type u} [CommRing R] (complex : CochainComplex (ModuleCat.{u} R) ℤ)
  (basis : ∀ degree, Module.Basis (indices degree) R (complex.X degree))

/-- The sheaf complex given by matrices of a based algebraic complex. -/
abbrev freeComplexOfBasis (coefficients : R →+* Γ(Y, ⊤)) : CochainComplex Y.Modules ℤ :=
  freeComplex (fun degree ↦ (complex.differentialMatrix basis degree).map coefficients)
    (fun degree ↦ by
      rw [← Matrix.map_mul, complex.differentialMatrix_mul basis,
        Matrix.map_zero _ (map_zero _)])

/-- A based complex with zero ranks outside `[0, bound]` gives a bounded finite
free sheaf complex. -/
lemma isFiniteFreeComplex_freeComplexOfBasis {ranks : ℤ → ℕ}
    (finiteBasis : ∀ degree, Module.Basis (ULift.{u} (Fin (ranks degree))) R (complex.X degree))
    (coefficients : R →+* Γ(Y, ⊤)) (bound : ℕ)
    (vanishing : ∀ degree, degree < 0 ∨ (bound : ℤ) < degree → ranks degree = 0) :
    IsFiniteFreeComplex (freeComplexOfBasis complex finiteBasis coefficients) bound where
  isStrictlyGE := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro degree negative
    have : IsEmpty (ULift.{u} (Fin (ranks degree))) := by
      rw [vanishing degree (Or.inl negative)]
      infer_instance
    exact isZero_free_of_isEmpty _
  isStrictlyLE := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro degree above
    have : IsEmpty (ULift.{u} (Fin (ranks degree))) := by
      rw [vanishing degree (Or.inr above)]
      infer_instance
    exact isZero_free_of_isEmpty _
  exists_iso_free degree := ⟨ranks degree, ⟨Iso.refl _⟩⟩

end Basis

end AlgebraicGeometry.Scheme.Modules
