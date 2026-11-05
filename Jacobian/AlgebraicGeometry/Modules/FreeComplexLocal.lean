import Jacobian.Algebra.Category.ModuleCat.Sheaf.Colimits
import Jacobian.AlgebraicGeometry.Modules.FreeComplexLocus
import Jacobian.AlgebraicGeometry.Modules.HomSection
import Jacobian.AlgebraicGeometry.Modules.LocallySurjective
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Ranks of complexes over local schemes

On a scheme with a point whose only open neighbourhood is the whole scheme,
maps from free modules lift along epimorphisms. For a bounded complex of finite
free modules, free homology concentrated in one degree therefore determines
the ranks of the differential matrices at that point.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{u}} {point : scheme}

private lemma exists_lift_unit_of_epi
    (localPoint : ∀ openSubset : scheme.Opens, point ∈ openSubset → openSubset = ⊤)
    {source target : scheme.Modules} (projection : source ⟶ target) [Epi projection]
    (morphism : unit scheme ⟶ target) :
    ∃ lift : unit scheme ⟶ source, lift ≫ projection = morphism := by
  have epi : Epi ((SheafOfModules.toSheaf.{u} scheme.ringCatSheaf).map projection) :=
    inferInstance
  have locallySurjective := (Sheaf.isLocallySurjective_iff_epi'
    (φ := (SheafOfModules.toSheaf.{u} scheme.ringCatSheaf).map projection)).mpr epi
  have localLifts : TopCat.Presheaf.IsLocallySurjective
      ((toPresheaf scheme).map projection) := locallySurjective
  rw [TopCat.Presheaf.isLocallySurjective_iff] at localLifts
  obtain ⟨openSubset, inclusion, ⟨sectionValue, image⟩, membership⟩ :=
    localLifts ⊤ (morphism.app ⊤ (1 : Γ(scheme, ⊤))) point trivial
  obtain rfl := localPoint openSubset membership
  refine ⟨homOfGlobalSection source sectionValue, unit_hom_ext ?_⟩
  rw [Hom.comp_app, ConcreteCategory.comp_apply, homOfGlobalSection_app_one,
    presheaf_map_id_apply]
  exact image.trans (presheaf_map_id_apply _ _)

private lemma exists_lift_free_of_epi
    (localPoint : ∀ openSubset : scheme.Opens, point ∈ openSubset → openSubset = ⊤)
    {source target : scheme.Modules} (projection : source ⟶ target) [Epi projection]
    {indices : Type u} (morphism : free (R := scheme.ringCatSheaf) indices ⟶ target) :
    ∃ lift : free indices ⟶ source, lift ≫ projection = morphism := by
  choose lift lift_image using fun index : indices ↦
    exists_lift_unit_of_epi localPoint projection (ιFree index ≫ morphism)
  refine ⟨Sigma.desc lift, Sigma.hom_ext _ _ fun index ↦ ?_⟩
  rw [Sigma.ι_desc_assoc, lift_image]
  rfl

private lemma exists_lift_free_of_exact
    (localPoint : ∀ openSubset : scheme.Opens, point ∈ openSubset → openSubset = ⊤)
    {complex : ShortComplex scheme.Modules} (exactness : complex.Exact) {indices : Type u}
    (morphism : free (R := scheme.ringCatSheaf) indices ⟶ complex.X₂)
    (cycle : morphism ≫ complex.g = 0) :
    ∃ lift : free indices ⟶ complex.X₁, lift ≫ complex.f = morphism := by
  have := exactness.epi_toCycles
  obtain ⟨lift, lift_image⟩ := exists_lift_free_of_epi localPoint complex.toCycles
    (complex.liftCycles morphism cycle)
  refine ⟨lift, ?_⟩
  rw [← complex.toCycles_i, ← Category.assoc, lift_image, complex.liftCycles_i]

section Matrices

variable (complex : CochainComplex scheme.Modules ℤ) {indices : ℤ → Type u}
  [∀ degree, Fintype (indices degree)] [∀ degree, DecidableEq (indices degree)]
  (trivialization : ∀ degree, complex.X degree ≅ free (R := scheme.ringCatSheaf) (indices degree))

private lemma freeMatrix_comp_d {columns : Type u} {sourceDegree targetDegree : ℤ}
    (morphism : free (R := scheme.ringCatSheaf) columns ⟶ complex.X sourceDegree) :
    freeMatrix (morphism ≫ complex.d sourceDegree targetDegree ≫
        (trivialization targetDegree).hom) =
      freeMatrix ((trivialization sourceDegree).inv ≫ complex.d sourceDegree targetDegree ≫
        (trivialization targetDegree).hom) *
          freeMatrix (morphism ≫ (trivialization sourceDegree).hom) := by
  rw [← freeMatrix_comp]
  simp

omit [∀ degree, Fintype (indices degree)] in
private lemma eq_of_freeMatrix_comp_eq {columns : Type u} [Finite columns] {degree : ℤ}
    [Finite (indices degree)]
    {first second : free (R := scheme.ringCatSheaf) columns ⟶ complex.X degree}
    (matrix_eq : freeMatrix (first ≫ (trivialization degree).hom) =
      freeMatrix (second ≫ (trivialization degree).hom)) : first = second := by
  have morphism_eq := freeMatrix_injective matrix_eq
  simpa using congrArg (· ≫ (trivialization degree).inv) morphism_eq

variable {complex}

private lemma freeMatrix_freeHomOfMatrix_comp_d {columns : Type u} [Fintype columns]
    [DecidableEq columns] {sourceDegree targetDegree : ℤ}
    (matrix : Matrix (indices sourceDegree) columns Γ(scheme, ⊤)) :
    freeMatrix ((freeHomOfMatrix matrix ≫ (trivialization sourceDegree).inv) ≫
        complex.d sourceDegree targetDegree ≫ (trivialization targetDegree).hom) =
      freeMatrix ((trivialization sourceDegree).inv ≫ complex.d sourceDegree targetDegree ≫
        (trivialization targetDegree).hom) * matrix := by
  rw [freeMatrix_comp_d]
  simp

private lemma freeHomOfMatrix_comp_d_eq_zero {columns : Type u} [Fintype columns]
    [DecidableEq columns] {sourceDegree targetDegree : ℤ}
    (matrix : Matrix (indices sourceDegree) columns Γ(scheme, ⊤))
    (matrix_cycle : freeMatrix ((trivialization sourceDegree).inv ≫
      complex.d sourceDegree targetDegree ≫ (trivialization targetDegree).hom) * matrix = 0) :
    (freeHomOfMatrix matrix ≫ (trivialization sourceDegree).inv) ≫
      complex.d sourceDegree targetDegree = 0 := by
  have matrix_eq := freeMatrix_freeHomOfMatrix_comp_d trivialization
    (targetDegree := targetDegree) matrix
  rw [matrix_cycle, ← freeMatrix_zero] at matrix_eq
  have morphism_eq := freeMatrix_injective matrix_eq
  simpa using congrArg (· ≫ (trivialization targetDegree).inv) morphism_eq

variable (localPoint : ∀ openSubset : scheme.Opens, point ∈ openSubset → openSubset = ⊤)

include localPoint in
private lemma exists_freeMatrix_mul_eq_of_isZero_homology (degree : ℤ)
    (vanishing : IsZero (complex.homology degree)) (columns : Type u) [Finite columns]
    (matrix : Matrix (indices degree) columns Γ(scheme, ⊤))
    (matrix_cycle : freeMatrix ((trivialization degree).inv ≫ complex.d degree (degree + 1) ≫
      (trivialization (degree + 1)).hom) * matrix = 0) :
    ∃ preimage : Matrix (indices (degree - 1)) columns Γ(scheme, ⊤),
      freeMatrix ((trivialization (degree - 1)).inv ≫ complex.d (degree - 1) degree ≫
        (trivialization degree).hom) * preimage = matrix := by
  classical
  have := Fintype.ofFinite columns
  have exactness : (complex.sc' (degree - 1) degree (degree + 1)).Exact := by
    rw [← HomologicalComplex.exactAt_iff' complex (degree - 1) degree (degree + 1)
      (by simp) (by simp), HomologicalComplex.exactAt_iff_isZero_homology]
    exact vanishing
  obtain ⟨lift, lift_image⟩ := exists_lift_free_of_exact localPoint exactness _
    (freeHomOfMatrix_comp_d_eq_zero trivialization matrix matrix_cycle)
  refine ⟨freeMatrix (lift ≫ (trivialization (degree - 1)).hom), ?_⟩
  rw [← freeMatrix_comp_d]
  change freeMatrix (lift ≫ (complex.sc' (degree - 1) degree (degree + 1)).f ≫
    (trivialization degree).hom) = matrix
  rw [← Category.assoc, lift_image, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    freeMatrix_freeHomOfMatrix]

include localPoint in
private lemma exists_freeMatrix_of_homology_iso (degree : ℤ) {homologyIndices : Type u}
    [Fintype homologyIndices]
    (homologyIso : complex.homology degree ≅ free (R := scheme.ringCatSheaf) homologyIndices) :
    ∃ cycles : Matrix (indices degree) homologyIndices Γ(scheme, ⊤),
      freeMatrix ((trivialization degree).inv ≫ complex.d degree (degree + 1) ≫
        (trivialization (degree + 1)).hom) * cycles = 0 ∧
      (∀ matrix : Matrix (indices degree) (indices degree) Γ(scheme, ⊤),
        freeMatrix ((trivialization degree).inv ≫ complex.d degree (degree + 1) ≫
          (trivialization (degree + 1)).hom) * matrix = 0 →
        ∃ (boundaries : Matrix (indices (degree - 1)) (indices degree) Γ(scheme, ⊤))
          (coefficients : Matrix homologyIndices (indices degree) Γ(scheme, ⊤)),
          freeMatrix ((trivialization (degree - 1)).inv ≫ complex.d (degree - 1) degree ≫
            (trivialization degree).hom) * boundaries + cycles * coefficients = matrix) ∧
      (∀ (columns : Type u) [Finite columns]
        (boundaries : Matrix (indices (degree - 1)) columns Γ(scheme, ⊤))
        (coefficients : Matrix homologyIndices columns Γ(scheme, ⊤)),
        freeMatrix ((trivialization (degree - 1)).inv ≫ complex.d (degree - 1) degree ≫
          (trivialization degree).hom) * boundaries + cycles * coefficients = 0 →
        coefficients = 0) := by
  classical
  obtain ⟨representatives, representatives_image⟩ := exists_lift_free_of_epi localPoint
    (complex.homologyπ degree) homologyIso.inv
  have exactness : (ShortComplex.mk (complex.toCycles (degree - 1) degree)
      (complex.homologyπ degree) (complex.toCycles_comp_homologyπ (degree - 1) degree)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (complex.homologyIsCokernel (degree - 1) degree (by simp))
  refine ⟨freeMatrix (representatives ≫ complex.iCycles degree ≫ (trivialization degree).hom),
    ?_, fun matrix matrix_cycle ↦ ?_, fun columns _ boundaries coefficients relation ↦ ?_⟩
  · rw [← freeMatrix_comp]
    simp
  · set morphism := freeHomOfMatrix matrix ≫ (trivialization degree).inv
    have morphism_cycle : morphism ≫ complex.d degree (degree + 1) = 0 :=
      freeHomOfMatrix_comp_d_eq_zero trivialization matrix matrix_cycle
    set cycleLift := complex.liftCycles morphism (degree + 1) (by simp) morphism_cycle
    set classMap := cycleLift ≫ complex.homologyπ degree ≫ homologyIso.hom
    have class_eq : (cycleLift - classMap ≫ representatives) ≫ complex.homologyπ degree = 0 := by
      simp [classMap, representatives_image]
    obtain ⟨boundaryLift, boundary_image⟩ := exists_lift_free_of_exact localPoint exactness _ class_eq
    refine ⟨freeMatrix (boundaryLift ≫ (trivialization (degree - 1)).hom), freeMatrix classMap, ?_⟩
    have decomposition : morphism = boundaryLift ≫ complex.d (degree - 1) degree +
        classMap ≫ representatives ≫ complex.iCycles degree := by
      have cycle_eq : cycleLift = boundaryLift ≫ complex.toCycles (degree - 1) degree +
          classMap ≫ representatives := by
        rw [← sub_eq_iff_eq_add]
        exact boundary_image.symm
      rw [← complex.liftCycles_i morphism (degree + 1) (by simp) morphism_cycle,
        ← complex.toCycles_i (degree - 1) degree]
      change cycleLift ≫ _ = _
      rw [cycle_eq, Preadditive.add_comp, Category.assoc, Category.assoc]
    rw [← freeMatrix_comp_d, ← freeMatrix_comp, ← freeMatrix_add]
    conv_rhs => rw [← freeMatrix_freeHomOfMatrix matrix]
    congr 1
    rw [show freeHomOfMatrix matrix = morphism ≫ (trivialization degree).hom by simp [morphism],
      decomposition]
    simp
  · have := Fintype.ofFinite columns
    set boundaryMap := freeHomOfMatrix boundaries
    set coefficientMap := freeHomOfMatrix coefficients
    have cycle_eq : (boundaryMap ≫ (trivialization (degree - 1)).inv ≫
        complex.toCycles (degree - 1) degree + coefficientMap ≫ representatives) ≫
          complex.iCycles degree = 0 := by
      refine eq_of_freeMatrix_comp_eq complex trivialization ?_
      rw [zero_comp, freeMatrix_zero, ← relation, Preadditive.add_comp, Preadditive.add_comp,
        freeMatrix_add]
      congr 1
      · have differential_eq : ((boundaryMap ≫ (trivialization (degree - 1)).inv ≫
            complex.toCycles (degree - 1) degree) ≫ complex.iCycles degree) ≫
            (trivialization degree).hom = (boundaryMap ≫ (trivialization (degree - 1)).inv) ≫
              complex.d (degree - 1) degree ≫ (trivialization degree).hom := by simp
        rw [differential_eq, freeMatrix_freeHomOfMatrix_comp_d]
      · have associativity : ((coefficientMap ≫ representatives) ≫ complex.iCycles degree) ≫
            (trivialization degree).hom = coefficientMap ≫ representatives ≫ complex.iCycles degree ≫
              (trivialization degree).hom := by simp
        rw [associativity, freeMatrix_comp, freeMatrix_freeHomOfMatrix]
    have zero_cycles := (cancel_mono (complex.iCycles degree)).mp (cycle_eq.trans zero_comp.symm)
    have zero_class : coefficientMap ≫ homologyIso.inv = 0 := by
      have class_eq := congrArg (· ≫ complex.homologyπ degree) zero_cycles
      simpa [representatives_image] using class_eq
    have zero_coefficients : coefficientMap = 0 := by
      simpa using congrArg (· ≫ homologyIso.hom) zero_class
    rw [← freeMatrix_freeHomOfMatrix coefficients]
    change freeMatrix coefficientMap = 0
    rw [zero_coefficients, freeMatrix_zero]

end Matrices

/-- On a local scheme, free homology in one degree forces the corresponding
rank equations for a bounded complex of finite free modules. -/
theorem rankCondition_of_homology
    (localPoint : ∀ openSubset : scheme.Opens, point ∈ openSubset → openSubset = ⊤)
    (complex : CochainComplex scheme.Modules ℤ) {indices : ℤ → Type u}
    [∀ degree, Fintype (indices degree)] [∀ degree, DecidableEq (indices degree)]
    (trivialization : ∀ degree, complex.X degree ≅ free (R := scheme.ringCatSheaf) (indices degree))
    (bound : ℤ) (bounded : ∀ degree, bound < degree → IsEmpty (indices degree))
    (degree : ℤ) {homologyIndices : Type u} [Fintype homologyIndices]
    (vanishing : ∀ otherDegree, otherDegree ≠ degree → Nonempty (indices otherDegree) →
      IsZero (complex.homology otherDegree))
    (homologyIso : complex.homology degree ≅ free (R := scheme.ringCatSheaf) homologyIndices) :
    Scheme.RankCondition (fun sourceDegree targetDegree ↦
      freeMatrix ((trivialization sourceDegree).inv ≫ complex.d sourceDegree targetDegree ≫
        (trivialization targetDegree).hom)) degree (Fintype.card homologyIndices) point := by
  classical
  intro homologyDegree
  obtain ⟨residuePoint⟩ : Nonempty (Spec (scheme.residueField point)) := inferInstance
  let := (isField_Γ_Spec_residueField point).toField
  have localUnits (scalar : Γ(scheme, ⊤))
      (nonzero : (scheme.fromSpecResidueField point).appTop.hom scalar ≠ 0) : IsUnit scalar := by
    have membership := (Hom.appTop_ne_zero_iff_mem_basicOpen (isField_Γ_Spec_residueField point)
      (scheme.fromSpecResidueField point) scalar residuePoint).mp nonzero
    rw [fromSpecResidueField_base_apply] at membership
    exact isUnit_of_le_basicOpen (localPoint _ membership).ge
  obtain ⟨cycles, cycles_closed, decomposition, uniqueness⟩ :=
    exists_freeMatrix_of_homology_iso trivialization localPoint degree homologyIso
  exact Matrix.rank_map_add_rank_map_add_eq_of_exact (scheme.fromSpecResidueField point).appTop.hom
    (fun sourceDegree targetDegree ↦ freeMatrix ((trivialization sourceDegree).inv ≫
      complex.d sourceDegree targetDegree ≫ (trivialization targetDegree).hom)) localUnits
    (fun sourceDegree middleDegree targetDegree ↦ by rw [← freeMatrix_comp]; simp) bound bounded degree
    (fun otherDegree unequal columns _ matrix matrix_cycle ↦ by
      by_cases nonempty : Nonempty (indices otherDegree)
      · exact exists_freeMatrix_mul_eq_of_isZero_homology trivialization localPoint otherDegree
          (vanishing otherDegree unequal nonempty) columns matrix matrix_cycle
      · have : IsEmpty (indices otherDegree) := not_nonempty_iff.mp nonempty
        exact ⟨0, Subsingleton.elim _ _⟩)
    cycles cycles_closed decomposition (fun boundaries coefficients relation ↦
      uniqueness _ boundaries coefficients relation) homologyDegree

end AlgebraicGeometry.Scheme.Modules
