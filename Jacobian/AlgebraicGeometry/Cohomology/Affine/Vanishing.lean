import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Jacobian.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
import Jacobian.AlgebraicGeometry.Cohomology.Basic
import Jacobian.Topology.Sheaves.MayerVietoris

/-!
# Vanishing on affine opens and above the size of a finite affine cover.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe coefficientUniverse

open CategoryTheory Limits Abelian TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{coefficientUniverse}}

/-- **Higher cohomology on an affine open vanishes.** For an abelian sheaf `F` on `X` which is
Čech-acyclic on the affine opens (for instance a quasi-coherent module), `H^q(U, F) = 0` for
every affine open `U` and every `q > 0`. -/
theorem subsingleton_H'_succ_of_isAffineOpen
    (sheaf : Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse}) (hF : cechAcyclicOnAffines scheme sheaf)
    {cover : scheme.Opens} (hU : IsAffineOpen cover) (cohomologyDegree : ℕ) :
    Subsingleton (sheaf.H' (cohomologyDegree + 1) cover : AddCommGrpCat.{coefficientUniverse}) := by
  induction cohomologyDegree generalizing sheaf with
  | zero =>
    let sequence := ShortComplex.mk (Injective.ι sheaf) (cokernel.π (Injective.ι sheaf)) (cokernel.condition _)
    have hS : sequence.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    change Subsingleton (Ext (TopCat.Sheaf.freeSheaf cover) sheaf 1)
    refine subsingleton_of_forall_eq 0 fun element ↦ ?_
    obtain ⟨otherElement, rfl⟩ :=
      Ext.covariant_sequence_exact₁ _ hS element (Ext.eq_zero_of_injective _) (zero_add 1)
    obtain ⟨thirdElement, rfl⟩ := TopCat.Sheaf.surjective_comp_mk₀_of_surjective sequence.g cover
      (surjective_app_of_cechAcyclicOnAffines hS hF hU) otherElement
    dsimp only
    rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  | succ cohomologyDegree ih =>
    let sequence := ShortComplex.mk (Injective.ι sheaf) (cokernel.π (Injective.ι sheaf)) (cokernel.condition _)
    have hS : sequence.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have hQ : Subsingleton (Ext (TopCat.Sheaf.freeSheaf cover) sequence.X₃ (cohomologyDegree + 1)) :=
      ih sequence.X₃ (cechAcyclicOnAffines_under_cokernel hF).2
    change Subsingleton (Ext (TopCat.Sheaf.freeSheaf cover) sheaf (cohomologyDegree + 2))
    refine subsingleton_of_forall_eq 0 fun element ↦ ?_
    obtain ⟨otherElement, rfl⟩ :=
      Ext.covariant_sequence_exact₁ _ hS element (Ext.eq_zero_of_injective _) rfl
    rw [Subsingleton.elim otherElement 0, Ext.zero_comp]

/-- **Quasi-coherent cohomology vanishes above the number of affine opens.** Let `X` be a
separated scheme which is the union of a nonempty finite family `U i`, `i ∈ s`, of affine
opens. If an abelian sheaf `F` on `X` is Čech-acyclic on the affine opens (for instance a
quasi-coherent module), then `H^q(X, F) = 0` for `q ≥ #s`. -/
theorem subsingleton_H_of_card_le [IsSeparated (terminal.from scheme)] {indexType : Type*} (sectionValue : Finset indexType)
    (hs : sectionValue.Nonempty) (cover : indexType → scheme.Opens) (hU : ∀ index ∈ sectionValue, IsAffineOpen (cover index)) (hcov : sectionValue.sup cover = ⊤)
    (sheaf : Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse}) (hF : cechAcyclicOnAffines scheme sheaf)
    {cohomologyDegree : ℕ} (hq : sectionValue.card ≤ cohomologyDegree) : Subsingleton (CategoryTheory.Sheaf.H sheaf cohomologyDegree) := by
  refine TopCat.Sheaf.subsingleton_H_of_subsingleton_H' sheaf ?_
  rw [← hcov]
  exact TopCat.Sheaf.subsingleton_H'_finsetSup sheaf IsAffineOpen (fun _ _ hU hV ↦ hU.inf hV)
    (fun _ hU cohomologyDegree ↦ subsingleton_H'_succ_of_isAffineOpen sheaf hF hU cohomologyDegree) sectionValue hs cover hU cohomologyDegree hq

/-- A quasi-compact scheme is the union of a nonempty finite family of affine opens. -/
lemma exists_finset_isAffineOpen_sup_eq_top [CompactSpace scheme] :
    ∃ sectionValue : Finset scheme.affineOpens, sectionValue.Nonempty ∧ sectionValue.sup (fun cover ↦ (cover : scheme.Opens)) = ⊤ := by
  classical
  obtain ⟨liftedSection, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun cover : scheme.affineOpens ↦ ((cover : scheme.Opens) : Set scheme)) (fun cover ↦ (cover : scheme.Opens).isOpen)
    (fun element _ ↦ Set.mem_iUnion.2 (by
      obtain ⟨cover, hU, hxU, -⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.1 scheme.isBasis_affineOpens)
          (show element ∈ (⊤ : scheme.Opens) from trivial)
      exact ⟨⟨cover, hU⟩, hxU⟩))
  let sectionValue := insert (⟨⊥, isAffineOpen_bot scheme⟩ : scheme.affineOpens) liftedSection
  refine ⟨sectionValue, Finset.insert_nonempty _ _, eq_top_iff.2 fun element _ ↦ ?_⟩
  obtain ⟨cover, hU, hxU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ element))
  exact (Finset.le_sup (f := fun cover : scheme.affineOpens ↦ (cover : scheme.Opens))
    (Finset.mem_insert_of_mem hU)) hxU

/-- **Quasi-coherent cohomology vanishes in high degrees.** On a quasi-compact separated
scheme there is a degree above which the cohomology of every quasi-coherent module vanishes:
the number of affine opens in a finite affine open covering. -/
theorem exists_forall_subsingleton_H_of_isQuasicoherent [CompactSpace scheme]
    [IsSeparated (terminal.from scheme)] :
    ∃ targetCategory : ℕ, ∀ (moduleSheaf : scheme.Modules) [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) moduleSheaf]
      (cohomologyDegree : ℕ), targetCategory < cohomologyDegree → Subsingleton (moduleSheaf.H cohomologyDegree) := by
  obtain ⟨sectionValue, hs, hcov⟩ := exists_finset_isAffineOpen_sup_eq_top (scheme := scheme)
  exact ⟨sectionValue.card, fun moduleSheaf _ cohomologyDegree hq ↦ subsingleton_H_of_card_le sectionValue hs (fun cover ↦ (cover : scheme.Opens))
    (fun cover _ ↦ cover.2) hcov _ (cechAcyclicOnAffines_of_isQuasicoherent moduleSheaf) hq.le⟩

/-- Higher cohomology of a quasi-coherent module on an affine scheme vanishes. -/
theorem subsingleton_H_succ_of_isAffine [IsAffine scheme] (moduleSheaf : scheme.Modules)
    [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) moduleSheaf] (degree : ℕ) :
    Subsingleton (moduleSheaf.H (degree + 1)) :=
  TopCat.Sheaf.subsingleton_H_of_subsingleton_H'
    ((SheafOfModules.toSheaf scheme.ringCatSheaf).obj moduleSheaf)
    (subsingleton_H'_succ_of_isAffineOpen _
      (cechAcyclicOnAffines_of_isQuasicoherent moduleSheaf) (isAffineOpen_top scheme) degree)

end AlgebraicGeometry.Scheme.Modules
