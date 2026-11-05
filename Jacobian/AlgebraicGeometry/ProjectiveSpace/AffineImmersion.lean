import Jacobian.AlgebraicGeometry.ProjectiveSpace.Charts
import Jacobian.AlgebraicGeometry.Morphisms.Immersion
import Jacobian.RingTheory.Localization.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Projective embeddings of affine schemes

An affine scheme locally of finite type over an arbitrary base admits an
immersion into projective space over that base, with finitely many
homogeneous coordinates.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {sourceScheme baseScheme : Scheme.{u}}

section Auxiliary

lemma exists_finite_subring_closure_divBasicOpen_eq_top (structureMap : sourceScheme ⟶ baseScheme) [IsAffine sourceScheme]
    [LocallyOfFiniteType structureMap] (denominator : Γ(sourceScheme, ⊤)) (affineOpen : baseScheme.Opens) (hW : IsAffineOpen affineOpen)
    (hle : sourceScheme.basicOpen denominator ≤ structureMap ⁻¹ᵁ affineOpen) :
    ∃ (generatorIndex : Type u) (_ : Finite generatorIndex) (numerators : generatorIndex → Γ(sourceScheme, ⊤)),
      Subring.closure (Set.range (structureMap.resLE affineOpen (sourceScheme.basicOpen denominator) hle).appTop ∪
        Set.range fun generator ↦ sourceScheme.divBasicOpen (numerators generator) denominator) = ⊤ := by
  have : IsAffine affineOpen.toScheme := hW
  have : IsAffine (sourceScheme.basicOpen denominator : Scheme.{u}) := (isAffineOpen_top sourceScheme).basicOpen denominator
  have : LocallyOfFiniteType (structureMap.resLE affineOpen (sourceScheme.basicOpen denominator) hle) := by
    delta Scheme.Hom.resLE; infer_instance
  let : Algebra Γ(affineOpen.toScheme, ⊤) Γ((sourceScheme.basicOpen denominator : Scheme.{u}), ⊤) :=
    (structureMap.resLE affineOpen (sourceScheme.basicOpen denominator) hle).appTop.hom.toAlgebra
  have : Algebra.FiniteType Γ(affineOpen.toScheme, ⊤) Γ((sourceScheme.basicOpen denominator : Scheme.{u}), ⊤) :=
    HasRingHomProperty.iff_of_isAffine.mp ‹LocallyOfFiniteType (structureMap.resLE affineOpen (sourceScheme.basicOpen denominator) hle)›
  obtain ⟨exponent, finiteGenerators, hM, numerators, hc⟩ := Algebra.FiniteType.exists_surjective_aeval_mk'
    (baseRing := Γ(affineOpen.toScheme, ⊤)) denominator Γ((sourceScheme.basicOpen denominator : Scheme.{u}), ⊤)
  refine ⟨ULift.{u} (Option finiteGenerators), inferInstance, fun generator ↦ generator.down.elim 1 fun generator ↦ numerators generator * denominator,
    (Subring.eq_top_iff' _).mpr fun element ↦ ?_⟩
  obtain ⟨polynomial, rfl⟩ := hc element
  have hone : sourceScheme.divBasicOpen 1 denominator ∈
      Subring.closure (Set.range ⇑(structureMap.resLE affineOpen (sourceScheme.basicOpen denominator) hle).appTop ∪
        Set.range fun generator : ULift.{u} (Option finiteGenerators) ↦
          sourceScheme.divBasicOpen (generator.down.elim 1 fun generator ↦ numerators generator * denominator) denominator) :=
    Subring.subset_closure (Or.inr ⟨⟨none⟩, rfl⟩)
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient =>
    refine Subring.subset_closure (Or.inl ⟨coefficient, ?_⟩)
    rw [MvPolynomial.aeval_C]
    rfl
  | add polynomial otherPolynomial hp hq => simpa only [map_add] using Subring.add_mem _ hp hq
  | mul_X polynomial generator hp =>
    rw [map_mul, MvPolynomial.aeval_X,
      mk'_eq_divBasicOpen_pow sourceScheme denominator (numerators generator) exponent ⟨exponent, rfl⟩]
    exact Subring.mul_mem _ hp (Subring.mul_mem _ (Subring.pow_mem _ hone exponent)
      (Subring.subset_closure (Or.inr ⟨⟨some generator⟩, rfl⟩)))

lemma isImmersion_homOfVector_divBasicOpen (structureMap : sourceScheme ⟶ baseScheme) [IsAffine sourceScheme] {coordinates : Type u}
    (sections : coordinates → Γ(sourceScheme, ⊤)) (coordinate : coordinates) (affineOpen : baseScheme.Opens) (hW : IsAffineOpen affineOpen)
    (hle : sourceScheme.basicOpen (sections coordinate) ≤ structureMap ⁻¹ᵁ affineOpen)
    (hgen : Subring.closure (Set.range (structureMap.resLE affineOpen (sourceScheme.basicOpen (sections coordinate)) hle).appTop ∪
      Set.range fun embedding : {embedding : coordinates // embedding ≠ coordinate} ↦ sourceScheme.divBasicOpen (sections embedding.1) (sections coordinate)) = ⊤) :
    IsImmersion (AffineSpace.homOfVector ((sourceScheme.basicOpen (sections coordinate)).ι ≫ structureMap)
      fun embedding : {embedding : coordinates // embedding ≠ coordinate} ↦ sourceScheme.divBasicOpen (sections embedding.1) (sections coordinate)) := by
  have : IsAffine affineOpen.toScheme := hW
  have : IsAffine (sourceScheme.basicOpen (sections coordinate) : Scheme.{u}) := (isAffineOpen_top sourceScheme).basicOpen (sections coordinate)
  have := AffineSpace.isClosedImmersion_homOfVector
    (coordinates := {otherCoordinate : coordinates // otherCoordinate ≠ coordinate})
    (structureMap.resLE affineOpen (sourceScheme.basicOpen (sections coordinate)) hle) _ hgen
  rw [show (sourceScheme.basicOpen (sections coordinate)).ι ≫ structureMap = structureMap.resLE affineOpen (sourceScheme.basicOpen (sections coordinate)) hle ≫ affineOpen.ι from
    (Scheme.Hom.resLE_comp_ι structureMap hle).symm, ← AffineSpace.homOfVector_comp_map]
  infer_instance

end Auxiliary

theorem exists_isImmersion_projectiveSpace [IsAffine sourceScheme] (structureMap : sourceScheme ⟶ baseScheme) [LocallyOfFiniteType structureMap] :
    ∃ (coordinates : Type u) (_ : Finite coordinates) (embedding : sourceScheme ⟶ ℙ(coordinates; baseScheme)),
      IsImmersion embedding ∧ embedding ≫ ℙ(coordinates; baseScheme) ↘ baseScheme = structureMap := by
  obtain ⟨coverIndex, hΛ, denominator, affineOpen, hW, hWle, hcov⟩ :=
    exists_finite_basicOpen_cover_le_preimage_isAffineOpen structureMap
  have := hΛ
  choose generatorIndex hm numerators ht using fun coverMember : coverIndex ↦
    exists_finite_subring_closure_divBasicOpen_eq_top structureMap (denominator coverMember) (affineOpen coverMember) (hW coverMember) (hWle coverMember)
  have : ∀ coverMember, Finite (generatorIndex coverMember) := hm
  set coordinates : Type u := coverIndex ⊕ (Σ coverMember : coverIndex, generatorIndex coverMember)
  set sections : coordinates → Γ(sourceScheme, ⊤) := Sum.elim denominator fun polynomial ↦ numerators polynomial.1 polynomial.2
  have hs : Ideal.span (Set.range sections) = ⊤ := by
    rw [← (isAffineOpen_top sourceScheme).iSup_basicOpen_eq_self_iff, iSup_range']
    exact top_le_iff.mp
      (hcov.ge.trans (iSup_le fun coverMember ↦ le_iSup (fun coordinate ↦ sourceScheme.basicOpen (sections coordinate)) (Sum.inl coverMember)))
  have hpre : ∀ coverMember : coverIndex, ProjectiveSpace.homOfSections structureMap sections hs ⁻¹ᵁ
      ProjectiveSpace.standardOpen coordinates baseScheme (Sum.inl coverMember) = sourceScheme.basicOpen (sections (Sum.inl coverMember)) :=
    fun coverMember ↦ ProjectiveSpace.homOfSections_preimage_standardOpen structureMap sections hs (Sum.inl coverMember)
  refine ⟨coordinates, inferInstance, ProjectiveSpace.homOfSections structureMap sections hs, ?_,
    ProjectiveSpace.homOfSections_over structureMap sections hs⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup
    (fun coverMember : coverIndex ↦ ProjectiveSpace.standardOpen coordinates baseScheme (Sum.inl coverMember)) ?_ fun coverMember ↦ ?_
  · rintro _ ⟨element, rfl⟩
    have hx : element ∈ ⨆ coverMember : coverIndex, sourceScheme.basicOpen (denominator coverMember) := by rw [hcov]; trivial
    obtain ⟨coverMember, hxl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine SetLike.mem_coe.mpr (TopologicalSpace.Opens.mem_iSup.mpr ⟨coverMember, ?_⟩)
    change element ∈ ProjectiveSpace.homOfSections structureMap sections hs ⁻¹ᵁ
      ProjectiveSpace.standardOpen coordinates baseScheme (Sum.inl coverMember)
    rw [hpre coverMember]
    exact hxl
  · rw [← Scheme.Hom.resLE_eq_morphismRestrict,
      Scheme.Hom.resLE_congr (ProjectiveSpace.homOfSections structureMap sections hs)
        (U := ProjectiveSpace.standardOpen coordinates baseScheme (Sum.inl coverMember)) le_rfl rfl (hpre coverMember) @IsImmersion,
      ← MorphismProperty.cancel_right_of_respectsIso @IsImmersion _
        (ProjectiveSpace.standardOpenIso coordinates baseScheme (Sum.inl coverMember)).hom,
      ProjectiveSpace.homOfSections_resLE_standardOpenIso_hom structureMap sections hs (Sum.inl coverMember)]
    refine isImmersion_homOfVector_divBasicOpen structureMap sections (Sum.inl coverMember) (affineOpen coverMember) (hW coverMember) (hWle coverMember)
      (eq_top_iff.mpr ((ht coverMember).ge.trans
        (Subring.closure_mono (Set.union_subset_union_right _ ?_))))
    rintro _ ⟨generator, rfl⟩
    exact ⟨⟨Sum.inr ⟨coverMember, generator⟩, Sum.inr_ne_inl⟩, rfl⟩

end AlgebraicGeometry
