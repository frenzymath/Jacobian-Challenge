import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechResolutionAffine
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechSectionsBaseChange
import Jacobian.AlgebraicGeometry.Modules.MatrixComplexSections
import Jacobian.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-!
# Free complexes computing higher direct images after base change

Let a based finite free complex map to a scalar extension of the Cech complex
of a quasi-coherent sheaf. For any cartesian base change, its matrices define
a free sheaf complex and its basis images define a comparison to the
pushforward Cech resolution. On affine opens this is the scalar extension
of the original map. A universal quasi-isomorphism therefore gives an actual
comparison computing the higher direct images.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits TensorProduct Opposite SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {sourceScheme pulledScheme baseScheme targetScheme : Scheme.{u}} {sourceMap : sourceScheme ⟶ baseScheme} {pulledMap : pulledScheme ⟶ targetScheme} {baseMap : targetScheme ⟶ baseScheme} {pullbackMap : pulledScheme ⟶ sourceScheme}
  (square : IsPullback pullbackMap pulledMap sourceMap baseMap) (moduleSheaf : sourceScheme.Modules)
  {coverIndex : Type u} (cover : coverIndex → sourceScheme.Opens)
  {baseRing : Type u} [CommRing baseRing] [Algebra Γ(baseScheme, ⊤) baseRing]

/-- The pushforward Cech resolution on the cartesian base change. -/
abbrev mumfordCech : CochainComplex targetScheme.Modules ℕ :=
  ((pushforward pulledMap).mapHomologicalComplex _).obj
    (cechResolution (fun index ↦ pullbackMap ⁻¹ᵁ cover index) ((pullback pullbackMap).obj moduleSheaf))

include square in
/-- Preimages of affine opens in a cartesian square over an affine scheme are relatively affine. -/
private lemma isAffineHom_ι_comp_of_isPullback [IsAffine baseScheme] {openSubset : sourceScheme.Opens}
    (affine : IsAffineOpen openSubset) {pulledOpen : pulledScheme.Opens}
    (identification : pulledOpen = pullbackMap ⁻¹ᵁ openSubset) : IsAffineHom (pulledOpen.ι ≫ pulledMap) := by
  subst identification
  have : IsAffine openSubset := affine
  exact MorphismProperty.of_isPullback (P := @IsAffineHom)
    ((isPullback_morphismRestrict pullbackMap openSubset).paste_vert square) inferInstance

section Sections

variable (openSubset : targetScheme.Opens) [Algebra Γ(baseScheme, ⊤) Γ(targetScheme, openSubset)]
  [Algebra baseRing Γ(targetScheme, openSubset)] [IsScalarTower Γ(baseScheme, ⊤) baseRing Γ(targetScheme, openSubset)]
  (compatible : algebraMap Γ(baseScheme, ⊤) Γ(targetScheme, openSubset) =
    (baseMap.appLE ⊤ openSubset (le_top.trans baseMap.preimage_top.ge)).hom)

/-- The tensor comparison to sections of the base-changed pushforward Cech complex. -/
def mumfordSectionsMap (degree : ℕ) :
    Γ(targetScheme, openSubset) ⊗[baseRing]
        (ModuleCat.extendScalars (algebraMap Γ(baseScheme, ⊤) baseRing)).obj
          ((cechModuleComplexNat sourceMap moduleSheaf cover).X degree) →+
      Γ((mumfordCech (pulledMap := pulledMap) (pullbackMap := pullbackMap) moduleSheaf cover).X degree, openSubset) :=
  ((sectionsCechResolutionIso (fun index ↦ pullbackMap ⁻¹ᵁ cover index)
      ((pullback pullbackMap).obj moduleSheaf) (pulledMap ⁻¹ᵁ openSubset)).inv.f degree).hom.comp
    ((cechSectionsBaseChangeX square moduleSheaf cover openSubset compatible degree).comp
      (ModuleCat.tensorExtendScalarsCancel Γ(baseScheme, ⊤) baseRing Γ(targetScheme, openSubset)
        ((cechModuleComplexNat sourceMap moduleSheaf cover).X degree)).toAddMonoidHom)

lemma mumfordSectionsMap_apply (degree : ℕ) (element) :
    mumfordSectionsMap (baseRing := baseRing) square moduleSheaf cover openSubset compatible degree
        element =
      (sectionsCechResolutionIso (fun index ↦ pullbackMap ⁻¹ᵁ cover index) ((pullback pullbackMap).obj moduleSheaf)
        (pulledMap ⁻¹ᵁ openSubset)).inv.f degree
          (cechSectionsBaseChangeX square moduleSheaf cover openSubset compatible degree
            (ModuleCat.tensorExtendScalarsCancel Γ(baseScheme, ⊤) baseRing Γ(targetScheme, openSubset)
              ((cechModuleComplexNat sourceMap moduleSheaf cover).X degree) element)) :=
  rfl

/-- The tensor comparison is bijective on affine opens. -/
lemma bijective_mumfordSectionsMap [IsAffine baseScheme] [moduleSheaf.IsQuasicoherent] [Finite coverIndex]
    (affine : IsAffineOpen openSubset)
    (affine_intersections : ∀ (degree : ℕ) (indices : Fin (degree + 1) → coverIndex),
      IsAffineOpen (⨅ position, cover (indices position))) (degree : ℕ) :
    Function.Bijective (mumfordSectionsMap (baseRing := baseRing) square moduleSheaf cover openSubset
      compatible degree) :=
  ((ConcreteCategory.bijective_of_isIso
      ((sectionsCechResolutionIso (fun index ↦ pullbackMap ⁻¹ᵁ cover index) ((pullback pullbackMap).obj moduleSheaf)
        (pulledMap ⁻¹ᵁ openSubset)).inv.f degree)).comp
      (bijective_cechSectionsBaseChangeX square moduleSheaf cover openSubset compatible affine
        affine_intersections degree)).comp
    (ModuleCat.tensorExtendScalarsCancel Γ(baseScheme, ⊤) baseRing Γ(targetScheme, openSubset)
      ((cechModuleComplexNat sourceMap moduleSheaf cover).X degree)).bijective

/-- The tensor comparison commutes with the differentials of the native scalar extension. -/
lemma mumfordSectionsMap_d (degree : ℕ)
    (element : Γ(targetScheme, openSubset) ⊗[baseRing]
      (ModuleCat.extendScalars (algebraMap Γ(baseScheme, ⊤) baseRing)).obj
        ((cechModuleComplexNat sourceMap moduleSheaf cover).X degree)) :
    Hom.app ((mumfordCech (pulledMap := pulledMap) (pullbackMap := pullbackMap) moduleSheaf cover).d degree (degree + 1))
        openSubset (mumfordSectionsMap square moduleSheaf cover openSubset compatible degree element) =
      mumfordSectionsMap square moduleSheaf cover openSubset compatible (degree + 1)
        (((((ModuleCat.extendScalars (algebraMap Γ(baseScheme, ⊤) baseRing)).mapHomologicalComplex _).obj
          (cechModuleComplexNat sourceMap moduleSheaf cover)).d degree (degree + 1)).hom.baseChange
            Γ(targetScheme, openSubset) element) := by
  have differential :
      ((((ModuleCat.extendScalars (algebraMap Γ(baseScheme, ⊤) baseRing)).mapHomologicalComplex _).obj
        (cechModuleComplexNat sourceMap moduleSheaf cover)).d degree (degree + 1)) =
      (ModuleCat.extendScalars (algebraMap Γ(baseScheme, ⊤) baseRing)).map
        ((cechModuleComplexNat sourceMap moduleSheaf cover).d degree (degree + 1)) := rfl
  rw [mumfordSectionsMap_apply, mumfordSectionsMap_apply, differential]
  erw [ModuleCat.tensorExtendScalarsCancel_naturality]
  erw [cechModuleComplexNat_d]
  erw [ModuleCat.hom_ofHom]
  exact (sectionsCechResolutionIso_inv_f_d (fun index ↦ pullbackMap ⁻¹ᵁ cover index)
    ((pullback pullbackMap).obj moduleSheaf) (pulledMap ⁻¹ᵁ openSubset) degree _).symm.trans
    (congrArg
      ((sectionsCechResolutionIso (fun index ↦ pullbackMap ⁻¹ᵁ cover index)
        ((pullback pullbackMap).obj moduleSheaf) (pulledMap ⁻¹ᵁ openSubset)).inv.f (degree + 1))
      (cechSectionsBaseChangeX_d square moduleSheaf cover openSubset compatible degree
        (ModuleCat.tensorExtendScalarsCancel Γ(baseScheme, ⊤) baseRing Γ(targetScheme, openSubset)
          ((cechModuleComplexNat sourceMap moduleSheaf cover).X degree) element)).symm)

/-- The sections comparison, with native scalar extension on both algebraic stages. -/
def mumfordSectionsHom :
    ((forget₂ (ModuleCat.{u} Γ(targetScheme, openSubset)) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
      (((ModuleCat.extendScalars (algebraMap baseRing Γ(targetScheme, openSubset))).mapHomologicalComplex _).obj
        (((ModuleCat.extendScalars (algebraMap Γ(baseScheme, ⊤) baseRing)).mapHomologicalComplex _).obj
          (cechModuleComplexNat sourceMap moduleSheaf cover))) ⟶
      ((sectionsAb openSubset).mapHomologicalComplex _).obj
        (mumfordCech (pulledMap := pulledMap) (pullbackMap := pullbackMap) moduleSheaf cover) where
  f degree := AddCommGrpCat.ofHom
    ((mumfordSectionsMap square moduleSheaf cover openSubset compatible degree).comp
      (ModuleCat.tensorEquivExtendScalars baseRing Γ(targetScheme, openSubset)
        ((ModuleCat.extendScalars (algebraMap Γ(baseScheme, ⊤) baseRing)).obj
          ((cechModuleComplexNat sourceMap moduleSheaf cover).X degree))).symm.toAddMonoidHom)
  comm' := by
    rintro degree _ rfl
    ext element
    change Hom.app ((mumfordCech (pulledMap := pulledMap) (pullbackMap := pullbackMap) moduleSheaf cover).d degree (degree + 1))
        openSubset (mumfordSectionsMap square moduleSheaf cover openSubset compatible degree
          ((ModuleCat.tensorEquivExtendScalars baseRing Γ(targetScheme, openSubset)
            ((ModuleCat.extendScalars (algebraMap Γ(baseScheme, ⊤) baseRing)).obj
              ((cechModuleComplexNat sourceMap moduleSheaf cover).X degree))).symm element)) =
      mumfordSectionsMap square moduleSheaf cover openSubset compatible (degree + 1)
        ((ModuleCat.tensorEquivExtendScalars baseRing Γ(targetScheme, openSubset)
          ((ModuleCat.extendScalars (algebraMap Γ(baseScheme, ⊤) baseRing)).obj
            ((cechModuleComplexNat sourceMap moduleSheaf cover).X (degree + 1)))).symm
          ((ModuleCat.extendScalars (algebraMap baseRing Γ(targetScheme, openSubset))).map
            ((((ModuleCat.extendScalars (algebraMap Γ(baseScheme, ⊤) baseRing)).mapHomologicalComplex _).obj
              (cechModuleComplexNat sourceMap moduleSheaf cover)).d degree (degree + 1)) element))
    erw [ModuleCat.tensorEquivExtendScalars_symm_naturality]
    exact mumfordSectionsMap_d square moduleSheaf cover openSubset compatible degree _

/-- The sections comparison is an isomorphism over affine opens. -/
lemma isIso_mumfordSectionsHom [IsAffine baseScheme] [moduleSheaf.IsQuasicoherent] [Finite coverIndex]
    (affine : IsAffineOpen openSubset)
    (affine_intersections : ∀ (degree : ℕ) (indices : Fin (degree + 1) → coverIndex),
      IsAffineOpen (⨅ position, cover (indices position))) :
    IsIso (mumfordSectionsHom (baseRing := baseRing) square moduleSheaf cover openSubset compatible) := by
  have (degree : ℕ) : IsIso
      ((mumfordSectionsHom (baseRing := baseRing) square moduleSheaf cover openSubset compatible).f
        degree) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      ((bijective_mumfordSectionsMap square moduleSheaf cover openSubset compatible affine
        affine_intersections degree).comp
          (ModuleCat.tensorEquivExtendScalars baseRing Γ(targetScheme, openSubset)
            ((ModuleCat.extendScalars (algebraMap Γ(baseScheme, ⊤) baseRing)).obj
              ((cechModuleComplexNat sourceMap moduleSheaf cover).X degree))).symm.bijective)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The tensor comparison respects the scalar action on pushforward sections. -/
lemma mumfordSectionsMap_smul (degree : ℕ) (scalar : Γ(targetScheme, openSubset))
    (element : Γ(targetScheme, openSubset) ⊗[baseRing]
      (ModuleCat.extendScalars (algebraMap Γ(baseScheme, ⊤) baseRing)).obj
        ((cechModuleComplexNat sourceMap moduleSheaf cover).X degree)) :
    mumfordSectionsMap square moduleSheaf cover openSubset compatible degree (scalar • element) =
      scalar • mumfordSectionsMap square moduleSheaf cover openSubset compatible degree element := by
  rw [mumfordSectionsMap_apply, mumfordSectionsMap_apply, LinearEquiv.map_smul]
  exact sectionsCechResolutionIso_inv_cechSectionsBaseChangeX_smul square moduleSheaf cover openSubset
    compatible degree scalar _

/-- Compatibility with restriction on elements of the form `1 ⊗ cochain`. -/
lemma presheaf_map_mumfordSectionsMap_one_tmul {largerOpen : targetScheme.Opens}
    (inclusion : openSubset ≤ largerOpen) [Algebra Γ(baseScheme, ⊤) Γ(targetScheme, largerOpen)]
    [Algebra baseRing Γ(targetScheme, largerOpen)] [IsScalarTower Γ(baseScheme, ⊤) baseRing Γ(targetScheme, largerOpen)]
    (larger_compatible : algebraMap Γ(baseScheme, ⊤) Γ(targetScheme, largerOpen) =
      (baseMap.appLE ⊤ largerOpen (le_top.trans baseMap.preimage_top.ge)).hom)
    (scalar_restriction : ∀ scalar : baseRing,
      targetScheme.presheaf.map (homOfLE inclusion).op (algebraMap baseRing Γ(targetScheme, largerOpen) scalar) =
        algebraMap baseRing Γ(targetScheme, openSubset) scalar) (degree : ℕ)
    (cochain : (ModuleCat.extendScalars (algebraMap Γ(baseScheme, ⊤) baseRing)).obj
      ((cechModuleComplexNat sourceMap moduleSheaf cover).X degree)) :
    ((mumfordCech (pulledMap := pulledMap) (pullbackMap := pullbackMap) moduleSheaf cover).X degree).presheaf.map
        (homOfLE inclusion).op
        (mumfordSectionsMap square moduleSheaf cover largerOpen larger_compatible degree
          (1 ⊗ₜ cochain)) =
      mumfordSectionsMap square moduleSheaf cover openSubset compatible degree (1 ⊗ₜ cochain) := by
  obtain ⟨cochain, rfl⟩ := (ModuleCat.tensorEquivExtendScalars Γ(baseScheme, ⊤) baseRing
    ((cechModuleComplexNat sourceMap moduleSheaf cover).X degree)).surjective cochain
  induction cochain using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.tmul_zero]
  | add left right left_eq right_eq =>
    simp only [map_add, TensorProduct.tmul_add, left_eq, right_eq]
  | tmul scalar coefficient =>
    have decomposition (extensionRing : Type u) [CommRing extensionRing]
        [Algebra baseRing extensionRing] :
        (1 : extensionRing) ⊗ₜ[baseRing]
            ModuleCat.tensorEquivExtendScalars Γ(baseScheme, ⊤) baseRing
              ((cechModuleComplexNat sourceMap moduleSheaf cover).X degree) (scalar ⊗ₜ coefficient) =
          algebraMap baseRing extensionRing scalar • ((1 : extensionRing) ⊗ₜ[baseRing]
            ModuleCat.tensorEquivExtendScalars Γ(baseScheme, ⊤) baseRing
              ((cechModuleComplexNat sourceMap moduleSheaf cover).X degree) (1 ⊗ₜ coefficient)) := by
      rw [← TensorProduct.one_tmul_smul_eq_algebraMap_smul]
      congr 1
      rw [← LinearEquiv.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [decomposition Γ(targetScheme, largerOpen), decomposition Γ(targetScheme, openSubset), mumfordSectionsMap_smul,
      mumfordSectionsMap_smul, Scheme.Modules.map_smul, scalar_restriction]
    congr 1
    rw [mumfordSectionsMap_apply, mumfordSectionsMap_apply,
      ModuleCat.tensorExtendScalarsCancel_tmul, ModuleCat.tensorExtendScalarsCancel_tmul]
    simp only [AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
    exact presheaf_map_sectionsCechResolutionIso_inv_one_tmul square moduleSheaf cover openSubset
      compatible inclusion larger_compatible degree coefficient

end Sections

section Comparison

variable [Algebra Γ(baseScheme, ⊤) Γ(targetScheme, ⊤)] [Algebra baseRing Γ(targetScheme, ⊤)]
  [IsScalarTower Γ(baseScheme, ⊤) baseRing Γ(targetScheme, ⊤)]
  (compatible : algebraMap Γ(baseScheme, ⊤) Γ(targetScheme, ⊤) =
    (baseMap.appLE ⊤ ⊤ (le_top.trans baseMap.preimage_top.ge)).hom)
  {indices : ℤ → Type u} [∀ degree, Fintype (indices degree)]
  [∀ degree, DecidableEq (indices degree)]
  (complex : CochainComplex (ModuleCat.{u} baseRing) ℤ)
  (basis : ∀ degree, Module.Basis (indices degree) baseRing (complex.X degree))
  (comparison : complex.restriction ComplexShape.embeddingUpNat ⟶
    ((ModuleCat.extendScalars (algebraMap Γ(baseScheme, ⊤) baseRing)).mapHomologicalComplex _).obj
      (cechModuleComplexNat sourceMap moduleSheaf cover))

/-- Basis images defining the comparison with the base-changed Cech resolution. -/
def mumfordSections (degree : ℕ) (index : indices degree) :
    Γ((mumfordCech (pulledMap := pulledMap) (pullbackMap := pullbackMap) moduleSheaf cover).X degree, ⊤) :=
  mumfordSectionsMap square moduleSheaf cover ⊤ compatible degree
    (1 ⊗ₜ (comparison.f degree).hom (basis degree index))

lemma mumfordSections_d (degree : ℕ) (index : indices degree) :
    ((mumfordCech (pulledMap := pulledMap) (pullbackMap := pullbackMap) moduleSheaf cover).d degree (degree + 1)).app ⊤
        (mumfordSections square moduleSheaf cover compatible complex basis comparison degree index) =
      ∑ targetIndex : indices ((degree : ℤ) + 1),
        (complex.differentialMatrix basis degree).map (algebraMap baseRing Γ(targetScheme, ⊤)) targetIndex index •
          mumfordSections square moduleSheaf cover compatible complex basis comparison
            (degree + 1) targetIndex := by
  have commutes :
      ((((ModuleCat.extendScalars (algebraMap Γ(baseScheme, ⊤) baseRing)).mapHomologicalComplex _).obj
        (cechModuleComplexNat sourceMap moduleSheaf cover)).d degree (degree + 1)).hom
          ((comparison.f degree).hom (basis degree index)) =
        (comparison.f (degree + 1)).hom
          ((complex.d degree (degree + 1 : ℕ)).hom (basis degree index)) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, comparison.comm, ModuleCat.hom_comp,
      LinearMap.comp_apply]
    rfl
  rw [mumfordSections, mumfordSectionsMap_d, LinearMap.baseChange_tmul, commutes,
    ← (basis ((degree : ℤ) + 1)).sum_repr ((complex.d degree (degree + 1 : ℕ)).hom
      (basis degree index)), map_sum, TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun targetIndex _ ↦ ?_
  rw [_root_.map_smul, TensorProduct.one_tmul_smul_eq_algebraMap_smul, mumfordSectionsMap_smul,
    Matrix.map_apply, CochainComplex.differentialMatrix, LinearMap.toMatrix_apply]
  rfl

/-- The actual morphism from the free sheaf complex to the pushforward Cech resolution. -/
def mumfordFreeHom :
    (freeComplexOfBasis complex basis (algebraMap baseRing Γ(targetScheme, ⊤))).restriction
        ComplexShape.embeddingUpNat ⟶ mumfordCech (pulledMap := pulledMap) (pullbackMap := pullbackMap) moduleSheaf cover :=
  freeComplexHom _ _ _ (mumfordSections square moduleSheaf cover compatible complex basis comparison)
    (mumfordSections_d square moduleSheaf cover compatible complex basis comparison)

private lemma mumfordFreeHom_sections_tensor (openSubset : targetScheme.Opens)
    [Algebra Γ(baseScheme, ⊤) Γ(targetScheme, openSubset)]
    [Algebra baseRing Γ(targetScheme, openSubset)] [IsScalarTower Γ(baseScheme, ⊤) baseRing Γ(targetScheme, openSubset)]
    (open_compatible : algebraMap Γ(baseScheme, ⊤) Γ(targetScheme, openSubset) =
      (baseMap.appLE ⊤ openSubset (le_top.trans baseMap.preimage_top.ge)).hom)
    (scalar_compatible : algebraMap baseRing Γ(targetScheme, openSubset) =
      (targetScheme.presheaf.map (homOfLE le_top).op).hom.comp (algebraMap baseRing Γ(targetScheme, ⊤)))
    (degree : ℕ) (element : Γ(targetScheme, openSubset) ⊗[baseRing] complex.X degree) :
    Hom.app (freeHomOfSections _
      (mumfordSections square moduleSheaf cover compatible complex basis comparison degree))
      openSubset (freeSectionsTensorEquiv complex basis openSubset degree element) =
      mumfordSectionsMap square moduleSheaf cover openSubset open_compatible degree
        ((comparison.f degree).hom.baseChange Γ(targetScheme, openSubset) element) := by
  induction element using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add left right left_eq right_eq =>
    rw [map_add, map_add, map_add, map_add, left_eq, right_eq]
  | tmul scalar coefficient =>
    rw [freeHomOfSections_app, freeSectionsLinearEquiv_freeSectionsTensorEquiv,
      LinearMap.baseChange_tmul]
    conv_rhs => rw [← (basis degree).sum_repr coefficient, map_sum, TensorProduct.tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun index _ ↦ ?_
    rw [_root_.map_smul, TensorProduct.tmul_smul_eq_mul_algebraMap_smul, mumfordSectionsMap_smul,
      mumfordSections,
      presheaf_map_mumfordSectionsMap_one_tmul square moduleSheaf cover openSubset open_compatible
        le_top compatible (fun coefficient ↦ by rw [scalar_compatible]; rfl),
      Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    rfl

/-- On sections, the free-sheaf comparison is the native scalar extension of the algebraic map. -/
lemma mumfordFreeHom_sections (openSubset : targetScheme.Opens) [Algebra Γ(baseScheme, ⊤) Γ(targetScheme, openSubset)]
    [Algebra baseRing Γ(targetScheme, openSubset)] [IsScalarTower Γ(baseScheme, ⊤) baseRing Γ(targetScheme, openSubset)]
    (open_compatible : algebraMap Γ(baseScheme, ⊤) Γ(targetScheme, openSubset) =
      (baseMap.appLE ⊤ openSubset (le_top.trans baseMap.preimage_top.ge)).hom)
    (scalar_compatible : algebraMap baseRing Γ(targetScheme, openSubset) =
      (targetScheme.presheaf.map (homOfLE le_top).op).hom.comp (algebraMap baseRing Γ(targetScheme, ⊤))) :
    freeSectionsTensorHom complex basis (algebraMap baseRing Γ(targetScheme, ⊤)) openSubset scalar_compatible ≫
        ((sectionsAb openSubset).mapHomologicalComplex _).map
          (mumfordFreeHom square moduleSheaf cover compatible complex basis comparison) =
      ((forget₂ (ModuleCat.{u} Γ(targetScheme, openSubset)) AddCommGrpCat.{u}).mapHomologicalComplex _).map
          (((ModuleCat.extendScalars (algebraMap baseRing Γ(targetScheme, openSubset))).mapHomologicalComplex
            _).map comparison) ≫
        mumfordSectionsHom square moduleSheaf cover openSubset open_compatible := by
  apply HomologicalComplex.hom_ext
  intro degree
  apply ConcreteCategory.hom_ext
  intro native_element
  exact (mumfordFreeHom_sections_tensor square moduleSheaf cover compatible complex basis comparison
    openSubset open_compatible scalar_compatible degree
    ((ModuleCat.tensorEquivExtendScalars baseRing Γ(targetScheme, openSubset)
      (complex.X degree)).symm native_element)).trans
    (congrArg (mumfordSectionsMap square moduleSheaf cover openSubset open_compatible degree)
      (ModuleCat.tensorEquivExtendScalars_symm_naturality baseRing Γ(targetScheme, openSubset)
        (comparison.f degree) native_element)).symm

/-- A universally quasi-isomorphic algebraic comparison gives a sheaf quasi-isomorphism. -/
theorem quasiIso_mumfordFreeHom [IsAffine baseScheme] [moduleSheaf.IsQuasicoherent] [Finite coverIndex]
    (affine_intersections : ∀ (degree : ℕ) (coverIndices : Fin (degree + 1) → coverIndex),
      IsAffineOpen (⨅ position, cover (coverIndices position)))
    (universal_comparison : ∀ (extensionRing : Type u) [CommRing extensionRing]
      [Algebra baseRing extensionRing],
      QuasiIso (((ModuleCat.extendScalars (algebraMap baseRing extensionRing)).mapHomologicalComplex
        _).map comparison)) :
    QuasiIso (mumfordFreeHom square moduleSheaf cover compatible complex basis comparison) := by
  refine quasiIso_of_quasiIso_sectionsAb_nat _ fun point neighborhood member ↦ ?_
  obtain ⟨openSubset, affine, member, inclusion⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 targetScheme.isBasis_affineOpens) member
  refine ⟨openSubset, member, inclusion, ?_⟩
  let : Algebra baseRing Γ(targetScheme, openSubset) :=
    ((targetScheme.presheaf.map (homOfLE (le_top : openSubset ≤ ⊤)).op).hom.comp
      (algebraMap baseRing Γ(targetScheme, ⊤))).toAlgebra
  let : Algebra Γ(baseScheme, ⊤) Γ(targetScheme, openSubset) :=
    ((targetScheme.presheaf.map (homOfLE (le_top : openSubset ≤ ⊤)).op).hom.comp
      (algebraMap Γ(baseScheme, ⊤) Γ(targetScheme, ⊤))).toAlgebra
  have : IsScalarTower Γ(baseScheme, ⊤) baseRing Γ(targetScheme, openSubset) := IsScalarTower.of_algebraMap_eq
    fun scalar ↦ by
      change (targetScheme.presheaf.map _).hom _ = (targetScheme.presheaf.map _).hom _
      rw [← IsScalarTower.algebraMap_apply]
  have open_compatible : algebraMap Γ(baseScheme, ⊤) Γ(targetScheme, openSubset) =
      (baseMap.appLE ⊤ openSubset (le_top.trans baseMap.preimage_top.ge)).hom := by
    rw [RingHom.algebraMap_toAlgebra, compatible, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
  have sections_square := mumfordFreeHom_sections square moduleSheaf cover compatible complex basis
    comparison openSubset open_compatible rfl
  have := isIso_mumfordSectionsHom (baseRing := baseRing) square moduleSheaf cover openSubset
    open_compatible affine affine_intersections
  have := universal_comparison Γ(targetScheme, openSubset)
  rw [← quasiIso_iff_comp_left
    (freeSectionsTensorHom complex basis (algebraMap baseRing Γ(targetScheme, ⊤)) openSubset rfl), sections_square]
  infer_instance

private def homologyIsoRestrictionNat {scheme : Scheme.{u}}
    (complex : CochainComplex scheme.Modules ℤ) [complex.IsStrictlyGE 0] (degree : ℕ) :
    complex.homology (degree : ℤ) ≅
      (complex.restriction ComplexShape.embeddingUpNat).homology degree := by
  cases degree with
  | zero =>
    have := complex.isIso_homologyπ (-1) 0 (by simp)
      ((complex.isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src _ _)
    have := (complex.restriction ComplexShape.embeddingUpNat).isIso_homologyπ 0 0 (by simp) (by simp)
    exact (asIso (complex.homologyπ 0)).symm ≪≫
      (complex.restrictionCyclesIso ComplexShape.embeddingUpNat 0 1 (by simp)
        (j' := 0) (k' := 1) rfl rfl (by simp)).symm ≪≫
      asIso ((complex.restriction ComplexShape.embeddingUpNat).homologyπ 0)
  | succ degree =>
    exact (complex.restrictionHomologyIso ComplexShape.embeddingUpNat
      degree (degree + 1) (degree + 1 + 1) (by simp) (by simp)
      (i' := (degree : ℤ)) (j' := ((degree + 1 : ℕ) : ℤ))
      (k' := ((degree + 1 + 1 : ℕ) : ℤ)) rfl rfl rfl (by simp) (by simp)).symm

include square compatible in
/-- The homology of the free sheaf complex is the actual higher direct image after base change. -/
theorem nonempty_homology_freeComplexOfBasis_iso [IsAffine baseScheme] [IsSeparated sourceMap]
    [moduleSheaf.IsQuasicoherent] [Finite coverIndex] [HasInjectiveResolutions pulledScheme.Modules]
    (affine_intersections : ∀ (degree : ℕ) (coverIndices : Fin (degree + 1) → coverIndex),
      IsAffineOpen (⨅ position, cover (coverIndices position))) (covering : ⨆ index, cover index = ⊤)
    (negative_empty : ∀ degree < 0, IsEmpty (indices degree))
    (universal_comparison : ∀ (extensionRing : Type u) [CommRing extensionRing]
      [Algebra baseRing extensionRing],
      QuasiIso (((ModuleCat.extendScalars (algebraMap baseRing extensionRing)).mapHomologicalComplex
        _).map comparison)) (degree : ℕ) :
    Nonempty ((freeComplexOfBasis complex basis (algebraMap baseRing Γ(targetScheme, ⊤))).homology degree ≅
      (higherDirectImage pulledMap degree).obj ((pullback pullbackMap).obj moduleSheaf)) := by
  have : IsSeparated pulledMap := MorphismProperty.of_isPullback square inferInstance
  let freeModel := freeComplexOfBasis (Y := targetScheme) complex basis (algebraMap baseRing Γ(targetScheme, ⊤))
  have : freeModel.IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro position negative
    have := negative_empty position negative
    exact isZero_free_of_isEmpty _
  have := quasiIso_mumfordFreeHom square moduleSheaf cover compatible complex basis comparison
    affine_intersections universal_comparison
  have affine_pullback (position : ℕ) (coverIndices : Fin (position + 1) → coverIndex) :
      IsAffineHom ((⨅ index, pullbackMap ⁻¹ᵁ cover (coverIndices index)).ι ≫ pulledMap) :=
    isAffineHom_ι_comp_of_isPullback square (affine_intersections position coverIndices)
      (by rw [Scheme.Hom.preimage_iInf])
  have pulled_covering : ⨆ index, pullbackMap ⁻¹ᵁ cover index = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, covering, Scheme.Hom.preimage_top]
  exact ⟨homologyIsoRestrictionNat freeModel degree ≪≫
    asIso (HomologicalComplex.homologyMap
      (mumfordFreeHom square moduleSheaf cover compatible complex basis comparison) degree) ≪≫
    (higherDirectImageIsoCechResolutionOfIsAffineHom pulledMap
      (fun index ↦ pullbackMap ⁻¹ᵁ cover index) affine_pullback pulled_covering
      ((pullback pullbackMap).obj moduleSheaf) degree).symm⟩

end Comparison

end AlgebraicGeometry.Scheme.Modules
