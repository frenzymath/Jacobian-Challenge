import Jacobian.AlgebraicGeometry.Modules.FreeGenerator

/-!
# Local criteria for a free generator

A section freely generates a module sheaf when scalar multiplication is injective
on every open subset and is locally surjective.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

open TopologicalSpace

variable {scheme : Scheme.{u}} {moduleSheaf otherSheaf : scheme.Modules}

/-- A section which freely generates on a covering sieve freely generates globally. -/
lemma isFreeGenerator_of_mem {openSubset : scheme.Opens} (generator : Γ(moduleSheaf, openSubset)) {coveringSieve : Sieve openSubset}
    (hS : coveringSieve ∈ _root_.Opens.grothendieckTopology scheme openSubset)
    (compatibility : ∀ ⦃smallerOpen : scheme.Opens⦄ (index : smallerOpen ⟶ openSubset), coveringSieve index → IsFreeGenerator (moduleSheaf.presheaf.map index.op generator)) :
    IsFreeGenerator generator := by
  intro smallestOpen hW
  have hS' := (_root_.Opens.grothendieckTopology scheme).pullback_stable (homOfLE hW) hS
  have hO := ((isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget _ scheme.presheaf
      (CategoryTheory.forget CommRingCat)).mp scheme.sheaf.property)) _ hS'
  have hM := ((isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget _ moduleSheaf.presheaf
      (CategoryTheory.forget AddCommGrpCat)).mp moduleSheaf.isSheaf)) _ hS'
  refine ⟨fun firstElement secondElement hab ↦ ?_, fun exponent ↦ ?_⟩
  · refine hO.isSeparatedFor.ext fun smallerOpen morphism hf ↦ (compatibility _ hf).smul_left_injective ?_
    have := congr_arg (moduleSheaf.presheaf.map morphism.op) hab
    simp only [map_smul, presheaf_map_map_apply] at this
    exact this
  · let element : Presieve.FamilyOfElements (scheme.presheaf ⋙ CategoryTheory.forget CommRingCat)
        (coveringSieve.pullback (homOfLE hW)).arrows := fun smallerOpen morphism hf ↦
      ((compatibility _ hf).coeff (moduleSheaf.presheaf.map morphism.op exponent) : Γ(scheme, smallerOpen))
    have hx : element.Compatible := by
      intro Z₁ Z₂ smallerOpen g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
      change scheme.presheaf.map g₁.op (element f₁ hf₁) = scheme.presheaf.map g₂.op (element f₂ hf₂)
      simp only [element]
      rw [← homOfLE_leOfHom g₁, ← homOfLE_leOfHom g₂, ← IsFreeGenerator.coeff_map,
        ← IsFreeGenerator.coeff_map]
      simp only [homOfLE_leOfHom, presheaf_map_map_apply]
      congr 2
    refine ⟨hO.amalgamate element hx, hM.isSeparatedFor.ext fun smallerOpen morphism hf ↦ ?_⟩
    change moduleSheaf.presheaf.map morphism.op (_ • _) = _
    rw [map_smul, presheaf_map_map_apply]
    have := hO.valid_glue hx morphism hf
    change scheme.presheaf.map morphism.op _ = _ at this
    rw [this]
    exact (compatibility _ hf).coeff_smul _

/-- Restricting a section of `M` twice along inclusions of opens. -/
lemma presheaf_map_homOfLE_map_homOfLE {openSubset smallerOpen smallestOpen : scheme.Opens} (compatibility : smallerOpen ≤ openSubset) (otherCompatibility : smallestOpen ≤ smallerOpen)
    (generator : Γ(moduleSheaf, openSubset)) :
    moduleSheaf.presheaf.map (homOfLE otherCompatibility).op (moduleSheaf.presheaf.map (homOfLE compatibility).op generator) =
      moduleSheaf.presheaf.map (homOfLE (otherCompatibility.trans compatibility)).op generator :=
  presheaf_map_map_apply _ _ _

/-- A relation `m = ρ • m'` over `V` restricts to the relation `m = ρ|_W • m'` over `W ⊆ V`. -/
lemma presheaf_map_homOfLE_eq_smul {openSubset smallerOpen smallestOpen : scheme.Opens} (compatibility : smallerOpen ≤ openSubset) (hW : smallestOpen ≤ smallerOpen)
    {exponent otherExponent : Γ(moduleSheaf, openSubset)} {ρ : Γ(scheme, smallerOpen)}
    (H : moduleSheaf.presheaf.map (homOfLE compatibility).op exponent = ρ • moduleSheaf.presheaf.map (homOfLE compatibility).op otherExponent) :
    moduleSheaf.presheaf.map (homOfLE (hW.trans compatibility)).op exponent =
      scheme.presheaf.map (homOfLE hW).op ρ • moduleSheaf.presheaf.map (homOfLE (hW.trans compatibility)).op otherExponent := by
  rw [← presheaf_map_homOfLE_map_homOfLE compatibility hW, H, map_smul, presheaf_map_homOfLE_map_homOfLE]

/-- **A criterion for a free generator.** A section `σ` of `Q` over `U` such that multiplication
`r ↦ r • σ` is injective over every open of `U`, and every section over an open of `U` is
locally a multiple of `σ`, is a free generator. -/
lemma isFreeGenerator_of_locally {testSheaf : scheme.Modules} {openSubset : scheme.Opens} (localSection : Γ(testSheaf, openSubset))
    (hinj : ∀ (smallerOpen : scheme.Opens) (compatibility : smallerOpen ≤ openSubset),
      Function.Injective fun scalar : Γ(scheme, smallerOpen) ↦ scalar • testSheaf.presheaf.map (homOfLE compatibility).op localSection)
    (hsurj : ∀ (smallerOpen : scheme.Opens) (compatibility : smallerOpen ≤ openSubset) (otherDegree : Γ(testSheaf, smallerOpen)), ∃ coveringSieve : Sieve smallerOpen,
      coveringSieve ∈ Opens.grothendieckTopology scheme smallerOpen ∧ ∀ ⦃smallestOpen : scheme.Opens⦄ (index : smallestOpen ⟶ smallerOpen), coveringSieve index →
        ∃ firstElement : Γ(scheme, smallestOpen), testSheaf.presheaf.map index.op otherDegree =
          firstElement • testSheaf.presheaf.map (homOfLE ((leOfHom index).trans compatibility)).op localSection) :
    IsFreeGenerator localSection := by
  intro smallerOpen compatibility
  refine ⟨hinj smallerOpen compatibility, fun otherDegree ↦ ?_⟩
  obtain ⟨coveringSieve, hS, hq⟩ := hsurj smallerOpen compatibility otherDegree
  have hO := ((isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget _ scheme.presheaf
      (CategoryTheory.forget CommRingCat)).mp
      scheme.sheaf.property)) coveringSieve hS
  have hQ := ((isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget _ testSheaf.presheaf
      (CategoryTheory.forget AddCommGrpCat)).mp
      testSheaf.isSheaf)) coveringSieve hS
  choose firstElement ha using hq
  let element : Presieve.FamilyOfElements (scheme.presheaf ⋙ CategoryTheory.forget CommRingCat)
      coveringSieve.arrows := fun smallestOpen index hi ↦ (firstElement index hi : Γ(scheme, smallestOpen))
  have hσ (smallestOpen : scheme.Opens) (power otherPower : smallestOpen ⟶ openSubset) : testSheaf.presheaf.map power.op localSection = testSheaf.presheaf.map otherPower.op localSection := by
    rw [Subsingleton.elim power otherPower]
  have hx : element.Compatible := by
    intro Z₁ Z₂ smallestOpen g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
    change scheme.presheaf.map g₁.op (firstElement f₁ hf₁) = scheme.presheaf.map g₂.op (firstElement f₂ hf₂)
    refine hinj smallestOpen ((leOfHom (g₁ ≫ f₁)).trans compatibility) ?_
    have e₁ := congrArg (testSheaf.presheaf.map g₁.op) (ha f₁ hf₁)
    have e₂ := congrArg (testSheaf.presheaf.map g₂.op) (ha f₂ hf₂)
    rw [map_smul, presheaf_map_map_apply, presheaf_map_map_apply] at e₁ e₂
    rw [hcomm] at e₁
    dsimp only
    rw [hσ smallestOpen (g₂ ≫ homOfLE ((leOfHom f₂).trans compatibility)) (g₁ ≫ homOfLE ((leOfHom f₁).trans compatibility))]
      at e₂
    rw [hσ smallestOpen (homOfLE _) (g₁ ≫ homOfLE ((leOfHom f₁).trans compatibility))]
    exact e₁.symm.trans e₂
  refine ⟨hO.amalgamate element hx, hQ.isSeparatedFor.ext fun smallestOpen index hi ↦ ?_⟩
  refine Eq.trans ?_ (ha index hi).symm
  change testSheaf.presheaf.map index.op (_ • _) = _
  rw [map_smul, presheaf_map_map_apply,
    hσ smallestOpen (index ≫ homOfLE compatibility) (homOfLE ((leOfHom index).trans compatibility))]
  congr 1
  exact hO.valid_glue hx index hi

end AlgebraicGeometry.Scheme.Modules
