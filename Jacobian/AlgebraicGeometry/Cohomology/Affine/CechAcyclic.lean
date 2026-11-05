import Jacobian.AlgebraicGeometry.Cohomology.Affine.Cech
import Jacobian.CategoryTheory.Abelian.DimensionShifting

/-!
# Abelian sheaves acyclic on standard affine covers and exactness on affine sections.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe coefficientUniverse
open CategoryTheory Limits TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
variable {scheme : Scheme.{coefficientUniverse}}

section CechAcyclic

open TopCat.Presheaf Opposite

/-- Every open covering of an affine open `V` is refined by a standard covering
`D(f₁), …, D(fₙ)` of `V` by finitely many basic opens. -/
lemma exists_basicOpen_cover_of_isAffineOpen {openSubset : scheme.Opens} (hV : IsAffineOpen openSubset)
    (smallerOpen : openSubset → scheme.Opens) (hW : ∀ element, element.1 ∈ smallerOpen element) :
    ∃ (size : ℕ) (morphism : Fin size → Γ(scheme, openSubset)), ⨆ index, scheme.basicOpen (morphism index) = openSubset ∧
      ∀ index, ∃ element, scheme.basicOpen (morphism index) ≤ smallerOpen element := by
  choose sectionFamily hgW hxg using fun element : openSubset ↦ hV.exists_basicOpen_le (V := smallerOpen element) ⟨element.1, hW element⟩ element.2
  obtain ⟨liftedSection, ht⟩ := hV.isCompact.elim_finite_subcover (fun element : openSubset ↦ (scheme.basicOpen (sectionFamily element) : Set scheme))
    (fun element ↦ (scheme.basicOpen (sectionFamily element)).isOpen) (fun element hx ↦ Set.mem_iUnion.2 ⟨⟨element, hx⟩, hxg _⟩)
  have hsup : ⨆ index, scheme.basicOpen (sectionFamily (liftedSection.equivFin.symm index).1) = openSubset := by
    refine le_antisymm (iSup_le fun index ↦ scheme.basicOpen_le _) fun element hx ↦ ?_
    obtain ⟨otherElement, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact Opens.mem_iSup.2 ⟨liftedSection.equivFin ⟨otherElement, hy⟩, by simpa using hxy⟩
  exact ⟨liftedSection.card, fun index ↦ sectionFamily (liftedSection.equivFin.symm index).1, hsup, fun index ↦ ⟨(liftedSection.equivFin.symm index).1, hgW _⟩⟩

variable (scheme) in
/-- The abelian sheaves on `X` whose Čech complexes on the standard coverings
`D(f₁), …, D(fₙ)` of the affine opens `V` of `X` are exact in positive degrees. Quasi-coherent
modules (`exactAt_cechComplex_basicOpen`) and injective abelian sheaves have this property. -/
def cechAcyclicOnAffines :
    ObjectProperty (Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse}) :=
  fun sheaf ↦ ∀ ⦃openSubset : scheme.Opens⦄, IsAffineOpen openSubset → ∀ {size : ℕ} (morphism : Fin size → Γ(scheme, openSubset)),
    ⨆ index, scheme.basicOpen (morphism index) = openSubset → ∀ cohomologyDegree : ℕ,
      ((cechComplex fun index ↦ scheme.basicOpen (morphism index)).obj sheaf.obj).ExactAt (cohomologyDegree + 1)

/-- The underlying abelian sheaf of a quasi-coherent module is Čech-acyclic on affine opens. -/
lemma cechAcyclicOnAffines_of_isQuasicoherent (moduleSheaf : scheme.Modules)
    [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) moduleSheaf] :
    cechAcyclicOnAffines scheme ((SheafOfModules.toSheaf scheme.ringCatSheaf).obj moduleSheaf) :=
  fun _ hV _ morphism hf cohomologyDegree ↦ exactAt_cechComplex_basicOpen moduleSheaf hV morphism hf cohomologyDegree

/-- An injective abelian sheaf is Čech-acyclic on affine opens. -/
lemma cechAcyclicOnAffines_of_injective (injectiveSheaf : Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse})
    [Injective injectiveSheaf] : cechAcyclicOnAffines scheme injectiveSheaf :=
  fun _ _ _ _ _ cohomologyDegree ↦ exactAt_cechComplex_of_injective _ injectiveSheaf cohomologyDegree

/-- A short exact sequence `0 → F → G → H → 0` of abelian sheaves with `F` Čech-acyclic on
affine opens is surjective on the sections over every affine open. -/
lemma surjective_app_of_cechAcyclicOnAffines
    {sequence : ShortComplex (Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse})}
    (hS : sequence.ShortExact) (compatibility : cechAcyclicOnAffines scheme sequence.X₁) {openSubset : scheme.Opens} (hV : IsAffineOpen openSubset) :
    Function.Surjective (sequence.g.hom.app (op openSubset)) :=
  TopCat.Sheaf.surjective_app_of_exactAt_cechComplex hS IsAffineOpen
    (fun {size} cover ↦ ∃ (openSubset : scheme.Opens) (_ : IsAffineOpen openSubset) (morphism : Fin size → Γ(scheme, openSubset)),
      cover = (fun index ↦ scheme.basicOpen (morphism index)) ∧ ⨆ index, scheme.basicOpen (morphism index) = openSubset)
    (fun openSubset hV smallerOpen hW ↦ by
      obtain ⟨size, morphism, hf, hfW⟩ := exists_basicOpen_cover_of_isAffineOpen hV smallerOpen hW
      exact ⟨size, _, ⟨openSubset, hV, morphism, rfl, hf⟩, hf, hfW⟩)
    (by
      rintro size _ ⟨openSubset, hV, morphism, rfl, hf⟩
      exact compatibility hV morphism hf 0) openSubset hV

/-- In a short exact sequence `0 → F → G → H → 0` of abelian sheaves with `F` and `G`
Čech-acyclic on affine opens, `H` is Čech-acyclic on affine opens. -/
lemma cechAcyclicOnAffines_X₃
    {sequence : ShortComplex (Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse})}
    (hS : sequence.ShortExact) (h₁ : cechAcyclicOnAffines scheme sequence.X₁) (h₂ : cechAcyclicOnAffines scheme sequence.X₂) :
    cechAcyclicOnAffines scheme sequence.X₃ := by
  intro openSubset hV size morphism hf cohomologyDegree
  refine exactAt_cechComplex_of_sectionwise _ sequence.f.hom sequence.g.hom TopCat.Sheaf.app_g_app_f
    (TopCat.Sheaf.injective_app_f hS) (TopCat.Sheaf.exists_app_f_eq hS) (fun degree otherElement ↦ ?_) cohomologyDegree
    (h₁ hV morphism hf (cohomologyDegree + 1)) (h₂ hV morphism hf cohomologyDegree)
  refine surjective_app_of_cechAcyclicOnAffines hS h₁ ?_
  rw [Scheme.iInf_basicOpen_eq_basicOpen_prod]
  exact hV.basicOpen _

/-- Being Čech-acyclic on affine opens passes from `F` to the chosen injective sheaf under `F`
and to the cokernel of `F ⟶ I`. -/
lemma cechAcyclicOnAffines_under_cokernel
    {sheaf : Sheaf (Opens.grothendieckTopology scheme) AddCommGrpCat.{coefficientUniverse}} (compatibility : cechAcyclicOnAffines scheme sheaf) :
    cechAcyclicOnAffines scheme (Injective.under sheaf) ∧
      cechAcyclicOnAffines scheme (cokernel (Injective.ι sheaf)) := by
  have h₂ : cechAcyclicOnAffines scheme (Injective.under sheaf) :=
    cechAcyclicOnAffines_of_injective (Injective.under sheaf)
  have hS := ObjectProperty.shortExact_injectiveShortComplex sheaf
  have h₃ := cechAcyclicOnAffines_X₃ hS compatibility h₂
  exact ⟨h₂, h₃⟩

end CechAcyclic
end AlgebraicGeometry.Scheme.Modules
