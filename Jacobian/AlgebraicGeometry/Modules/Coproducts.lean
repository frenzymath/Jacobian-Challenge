import Jacobian.Algebra.Category.ModuleCat.Sheaf.Coproducts
import Jacobian.AlgebraicGeometry.Modules.FinitePresentation
import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Local
import Jacobian.AlgebraicGeometry.Modules.LocallySurjective
import Jacobian.AlgebraicGeometry.Modules.Sections
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# Coproducts and epimorphisms of quasi-coherent sheaves

Quasi-coherence is preserved by coproducts, and finite presentation is preserved
by finite coproducts. Surjectivity on sections over an affine cover detects
epimorphisms of module sheaves with quasi-coherent target.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.Modules
variable {scheme : Scheme.{u}}
/-- **A coproduct of quasi-coherent modules is quasi-coherent.** -/
theorem isQuasicoherent_sigma {indexType : Type u} (family : indexType → scheme.Modules)
    [∀ index, SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) (family index)] :
    SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) (∐ family) :=
  isQuasicoherent_of_iSup_opensRange_eq_top (∐ family) (fun openSubset : scheme.affineOpens ↦
    openSubset.2.fromSpec) (by simpa only [IsAffineOpen.opensRange_fromSpec] using iSup_affineOpens_eq_top scheme) fun openSubset ↦
      (SheafOfModules.Presentation.sigma _ fun index ↦ presentationOfIsIsoFromTildeΓ
        ((family index).restrict openSubset.2.fromSpec)).ofIsIso
        (PreservesCoproduct.iso (restrictFunctor openSubset.2.fromSpec) family).inv

/-- **A finite coproduct of modules of finite presentation is of finite presentation.** Every point
has an affine neighbourhood over which all the summands have finite presentations. -/
theorem isFinitePresentation_sigma {indexType : Type u} [Finite indexType] (family : indexType → scheme.Modules)
    [∀ index, SheafOfModules.IsFinitePresentation (R := scheme.ringCatSheaf) (family index)] :
    SheafOfModules.IsFinitePresentation (R := scheme.ringCatSheaf) (∐ family) := by
  choose presentations hq using fun index ↦ SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (R := scheme.ringCatSheaf) (family index)
  choose chartIndex hj using fun (point : scheme) (index : indexType) ↦
    ((Opens.coversTop_iff _ (presentations index).X).mp (presentations index).coversTop).exists_mem point
  have hV (point : scheme) : ∃ smallerOpen : scheme.Opens, IsAffineOpen smallerOpen ∧ point ∈ smallerOpen ∧ ∀ index, smallerOpen ≤ (presentations index).X (chartIndex point index) := by
    obtain ⟨_, ⟨smallerOpen, hV, rfl⟩, hxV, hVle⟩ := scheme.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_iInter.mpr fun index ↦ hj point index) (isOpen_iInter_of_finite fun index ↦ ((presentations index).X (chartIndex point index)).2)
    exact ⟨smallerOpen, hV, hxV, fun index ↦ (hVle.trans (Set.iInter_subset _ index) :)⟩
  choose smallerOpen hV hxV hVle using hV
  let presentation (point : scheme) : ((∐ family).restrict (hV point).fromSpec).Presentation :=
    (SheafOfModules.Presentation.sigma _ fun index ↦ presentationRestrictOfOver
      ((presentations index).presentation (chartIndex point index)) (hV point).fromSpec
      (by rw [(hV point).opensRange_fromSpec]; exact hVle point index)).ofIsIso
      (PreservesCoproduct.iso (restrictFunctor (hV point).fromSpec) family).inv
  refine isFinitePresentation_of_iSup_opensRange_eq_top (∐ family) (fun point ↦ (hV point).fromSpec) ?_ presentation
  refine eq_top_iff.mpr fun point _ ↦ Opens.mem_iSup.mpr ⟨point, ?_⟩
  rw [(hV point).opensRange_fromSpec]
  exact hxV point

section Epi

variable {scheme : Scheme.{u}}

/-- **Surjectivity on an affine cover gives an epimorphism.** Let `𝒩` be quasi-coherent and let
`(Uᵢ)` be affine opens covering `X`. If `φ : ℳ ⟶ 𝒩` is surjective on sections over every `Uᵢ`,
then `φ` is an epimorphism: a section of `𝒩` near `x ∈ Uᵢ` is, on a basic open `D(g) ∋ x` of
`Uᵢ`, `g⁻ᵏ` times the restriction of a section over `Uᵢ`. -/
lemma epi_of_surjective_app {family targetSheaf : scheme.Modules}
    [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) targetSheaf] (morphism : family ⟶ targetSheaf) {indexType : Type*}
    (openSubset : indexType → scheme.Opens) (hU : ∀ index, IsAffineOpen (openSubset index)) (hcov : ⨆ index, openSubset index = ⊤)
    (surjectiveSections : ∀ index, Function.Surjective (morphism.app (openSubset index))) : Epi morphism := by
  refine epi_of_forall_exists_app_eq morphism fun smallestOpen sectionValue point hx ↦ ?_
  obtain ⟨index, hi⟩ := Opens.mem_iSup.mp (show point ∈ ⨆ index, openSubset index by rw [hcov]; trivial)
  obtain ⟨denominator, hgU, hxg⟩ := (hU index).exists_basicOpen_le ⟨point, hx⟩ hi
  obtain ⟨exponent, extendedSection, ht⟩ := exists_map_eq_pow_smul_of_isAffineOpen targetSheaf (hU index) denominator
    (targetSheaf.presheaf.map (homOfLE hgU).op sectionValue)
  obtain ⟨preimageSection, rfl⟩ := surjectiveSections index extendedSection
  have hu : IsUnit ((scheme.presheaf.map (homOfLE (scheme.basicOpen_le denominator)).op denominator) ^ exponent) :=
    (scheme.toRingedSpace.isUnit_res_basicOpen denominator).pow exponent
  refine ⟨_, hgU, hxg, hu.unit⁻¹.1 • family.presheaf.map (homOfLE (scheme.basicOpen_le denominator)).op preimageSection, ?_⟩
  rw [Hom.app_smul, Hom.app_presheaf_map, ht, smul_smul, IsUnit.val_inv_mul, one_smul]

/-- Maps from a family of module sheaves give an epimorphism from their coproduct if their
images span the target sections on an affine cover. -/
lemma epi_sigma_desc_of_span_eq_top {indexType : Type u}
    (family : indexType → scheme.Modules) {targetSheaf : scheme.Modules}
    [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) targetSheaf]
    (componentMap : ∀ index, family index ⟶ targetSheaf) {coverIndex : Type*}
    (openSubset : coverIndex → scheme.Opens)
    (affine : ∀ index, IsAffineOpen (openSubset index))
    (cover : ⨆ index, openSubset index = ⊤)
    (spans : ∀ index, Submodule.span Γ(scheme, openSubset index)
      (⋃ generatorIndex, Set.range ((componentMap generatorIndex).app (openSubset index))) = ⊤) :
    Epi (Sigma.desc componentMap) := by
  refine epi_of_surjective_app (Sigma.desc componentMap) openSubset affine cover ?_
  intro coverMember
  change Function.Surjective (Hom.appₗ (Sigma.desc componentMap) (openSubset coverMember))
  apply LinearMap.range_eq_top.mp
  refine top_le_iff.mp ?_
  rw [← spans coverMember]
  refine Submodule.span_le.mpr ?_
  intro sectionValue membership
  obtain ⟨generatorIndex, localSection, rfl⟩ := Set.mem_iUnion.mp membership
  refine ⟨(Sigma.ι family generatorIndex).app (openSubset coverMember) localSection, ?_⟩
  change (Sigma.desc componentMap).app (openSubset coverMember)
    ((Sigma.ι family generatorIndex).app (openSubset coverMember) localSection) = _
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Sigma.ι_desc]

end Epi
end AlgebraicGeometry.Scheme.Modules
