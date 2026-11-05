import Jacobian.Algebra.Category.ModuleCat.ChangeOfRings
import Jacobian.Algebra.Category.ModuleCat.Sheaf.Evaluation
import Jacobian.AlgebraicGeometry.Modules.MatrixComplex
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Sections of complexes defined by matrices

The sections of the free sheaf complex associated to a based algebraic complex
are its extension of scalars to the functions on the open set. This comparison
commutes with the differentials, hence is an isomorphism of complexes after
restriction to nonnegative degrees.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits TensorProduct Opposite SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {baseRing : Type u} [CommRing baseRing] {scheme : Scheme.{u}}
  {indices : ℤ → Type u} [∀ degree, Fintype (indices degree)]
  [∀ degree, DecidableEq (indices degree)]
  (complex : CochainComplex (ModuleCat.{u} baseRing) ℤ)
  (basis : ∀ degree, Module.Basis (indices degree) baseRing (complex.X degree))

/-- Sections of a free sheaf in the coordinates induced by an algebraic basis. -/
def freeSectionsTensorEquiv (openSubset : scheme.Opens)
    [Algebra baseRing Γ(scheme, openSubset)] (degree : ℤ) :
    Γ(scheme, openSubset) ⊗[baseRing] complex.X degree ≃ₗ[Γ(scheme, openSubset)]
      Γ(free (R := scheme.ringCatSheaf) (indices degree), openSubset) :=
  (Algebra.TensorProduct.basis Γ(scheme, openSubset) (basis degree)).equivFun.trans
    (freeSectionsLinearEquiv (R := scheme.ringCatSheaf) (indices degree) (op openSubset)).symm

/-- The coordinates of the sections comparison are the scalar-extended basis coordinates. -/
lemma freeSectionsLinearEquiv_freeSectionsTensorEquiv (openSubset : scheme.Opens)
    [Algebra baseRing Γ(scheme, openSubset)] (degree : ℤ)
    (element : Γ(scheme, openSubset) ⊗[baseRing] complex.X degree) :
    freeSectionsLinearEquiv (R := scheme.ringCatSheaf) (indices degree) (op openSubset)
        (freeSectionsTensorEquiv complex basis openSubset degree element) =
      (Algebra.TensorProduct.basis Γ(scheme, openSubset) (basis degree)).repr element := by
  exact (freeSectionsLinearEquiv (R := scheme.ringCatSheaf)
    (indices degree) (op openSubset)).apply_symm_apply _

/-- The tensor description of sections intertwines the algebraic and sheaf differentials. -/
lemma freeSectionsTensorEquiv_d (coefficients : baseRing →+* Γ(scheme, ⊤))
    (openSubset : scheme.Opens) [Algebra baseRing Γ(scheme, openSubset)]
    (compatible : algebraMap baseRing Γ(scheme, openSubset) =
      (scheme.presheaf.map (homOfLE le_top).op).hom.comp coefficients)
    {sourceDegree targetDegree : ℤ} (successor : sourceDegree + 1 = targetDegree)
    (element : Γ(scheme, openSubset) ⊗[baseRing] complex.X sourceDegree) :
    freeSectionsTensorEquiv complex basis openSubset targetDegree
        ((complex.d sourceDegree targetDegree).hom.baseChange Γ(scheme, openSubset) element) =
      Hom.app ((freeComplexOfBasis complex basis coefficients).d sourceDegree targetDegree)
        openSubset (freeSectionsTensorEquiv complex basis openSubset sourceDegree element) := by
  obtain rfl := successor
  apply (freeSectionsLinearEquiv (R := scheme.ringCatSheaf)
    (indices (sourceDegree + 1)) (op openSubset)).injective
  rw [freeComplex_d]
  erw [freeSectionsLinearEquiv_app_opens]
  rw [freeMatrix_freeHomOfMatrix,
    freeSectionsLinearEquiv_freeSectionsTensorEquiv,
    freeSectionsLinearEquiv_freeSectionsTensorEquiv,
    ← LinearMap.toMatrix_mulVec_repr
      (Algebra.TensorProduct.basis Γ(scheme, openSubset) (basis sourceDegree))
      (Algebra.TensorProduct.basis Γ(scheme, openSubset) (basis (sourceDegree + 1))),
    LinearMap.toMatrix_baseChange, Matrix.map_map, compatible]
  rfl

/-- The sections comparison as a chain map, using the native extension-of-scalars functor. -/
def freeSectionsTensorHom (coefficients : baseRing →+* Γ(scheme, ⊤))
    (openSubset : scheme.Opens) [Algebra baseRing Γ(scheme, openSubset)]
    (compatible : algebraMap baseRing Γ(scheme, openSubset) =
      (scheme.presheaf.map (homOfLE le_top).op).hom.comp coefficients) :
    ((forget₂ (ModuleCat.{u} Γ(scheme, openSubset)) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
        (((ModuleCat.extendScalars (algebraMap baseRing Γ(scheme, openSubset))).mapHomologicalComplex
          _).obj (complex.restriction ComplexShape.embeddingUpNat)) ⟶
      (((SheafOfModules.evaluation scheme.ringCatSheaf (op openSubset) ⋙
          forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex _).obj
        ((freeComplexOfBasis complex basis coefficients).restriction ComplexShape.embeddingUpNat))
    where
  f degree := AddCommGrpCat.ofHom
    (((ModuleCat.tensorEquivExtendScalars baseRing Γ(scheme, openSubset)
      (complex.X degree)).symm.trans
        (freeSectionsTensorEquiv complex basis openSubset degree)).toAddMonoidHom)
  comm' := by
    rintro degree _ rfl
    ext element
    change Hom.app ((freeComplexOfBasis complex basis coefficients).d (degree : ℤ)
        ((degree + 1 : ℕ) : ℤ)) openSubset
        (freeSectionsTensorEquiv complex basis openSubset degree
          ((ModuleCat.tensorEquivExtendScalars baseRing Γ(scheme, openSubset)
            (complex.X degree)).symm element)) =
      freeSectionsTensorEquiv complex basis openSubset ((degree + 1 : ℕ) : ℤ)
        ((ModuleCat.tensorEquivExtendScalars baseRing Γ(scheme, openSubset)
          (complex.X ((degree + 1 : ℕ) : ℤ))).symm
            ((ModuleCat.extendScalars (algebraMap baseRing Γ(scheme, openSubset))).map
              (complex.d (degree : ℤ) ((degree + 1 : ℕ) : ℤ)) element))
    rw [ModuleCat.tensorEquivExtendScalars_symm_naturality]
    exact (freeSectionsTensorEquiv_d complex basis coefficients openSubset compatible
      (sourceDegree := degree) (targetDegree := ((degree + 1 : ℕ) : ℤ))
      (by push_cast; rfl) _).symm

/-- The chain-level sections comparison is degreewise a linear equivalence. -/
instance (coefficients : baseRing →+* Γ(scheme, ⊤)) (openSubset : scheme.Opens)
    [Algebra baseRing Γ(scheme, openSubset)]
    (compatible : algebraMap baseRing Γ(scheme, openSubset) =
      (scheme.presheaf.map (homOfLE le_top).op).hom.comp coefficients) :
    IsIso (freeSectionsTensorHom complex basis coefficients openSubset compatible) := by
  have (degree : ℕ) :
      IsIso ((freeSectionsTensorHom complex basis coefficients openSubset compatible).f degree) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (((ModuleCat.tensorEquivExtendScalars baseRing Γ(scheme, openSubset)
        (complex.X degree)).symm.trans
          (freeSectionsTensorEquiv complex basis openSubset degree)).bijective)
  exact HomologicalComplex.Hom.isIso_of_components _

end AlgebraicGeometry.Scheme.Modules
