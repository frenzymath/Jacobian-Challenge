import Jacobian.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Invertible
import Jacobian.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
import Jacobian.AlgebraicGeometry.Modules.ClearDenominators

/-!
# Immersions defined by an ample family of sections

For a scheme separated and locally of finite type over an affine base, a finite
family of sections of one invertible module with affine nonvanishing loci
covering the scheme gives an immersion into projective space. Clearing
denominators produces the additional coordinates needed on each affine chart.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme.Modules

section Auxiliary

variable {sourceScheme : Scheme.{u}}

/-- Every section of a module over the empty open is a free generator. -/
lemma Scheme.Modules.isFreeGenerator_bot {moduleSheaf : sourceScheme.Modules} (generator :
  Γ(moduleSheaf, ⊥)) : IsFreeGenerator generator :=
  isFreeGenerator_of_mem generator (coveringSieve := ⊥) (fun _ hx ↦ hx.elim) fun _ _ equality ↦
    equality.elim

/-- If a nonzero tensor power of a section of an invertible module freely generates on an open,
that open lies in the nonvanishing locus of the section. -/
lemma Scheme.Modules.le_compl_support_zeroLocus_of_isFreeGenerator {lineBundle :
  sourceScheme.Modules}
    [SheafOfModules.IsInvertible.{u, u, u} lineBundle]
      (lineSection : 𝟙_ sourceScheme.Modules ⟶ lineBundle) {generatorIndices : ℕ} (hm :
      generatorIndices ≠ 0)
    {openSubset : sourceScheme.Opens} (hW : IsFreeGenerator (tensorPowSectionOne lineSection
      generatorIndices openSubset)) :
    openSubset ≤ (Hom.zeroLocus lineSection).support.compl := by
  intro point hx
  obtain ⟨chartScheme, hxV, hVW, generator, he⟩ := exists_isFreeGenerator lineBundle hx
  obtain ⟨powerGenerator, hE, hσE⟩ := exists_tensorPowSectionOne_eq_pow_smul lineSection he
    (he.coeff_smul (lineSection.app chartScheme.1 (unitSectionsEquiv _ 1))).symm generatorIndices
  have hG := hW.map hVW
  rw [presheaf_map_tensorPowSectionOne, hσE] at hG
  obtain ⟨extendedSections, hw⟩ := hE.exists_unit_smul_eq hG
  have hc : IsUnit (he.coeff (lineSection.app chartScheme.1 (unitSectionsEquiv _ 1))) := by
    rw [← isUnit_pow_iff hm, hE.smul_left_injective hw]
    exact extendedSections.isUnit
  have equality := basicOpen_coeff_eq lineSection chartScheme he
  rw [sourceScheme.basicOpen_of_isUnit hc] at equality
  exact (equality.le hxV).2

/-- An extension after multiplication by a tensor power can be extended to any larger exponent by
multiplying by further copies of the section. -/
lemma Scheme.Modules.exists_restrict_eq_smul_tensorPowSectionOne_of_le {lineBundle :
  sourceScheme.Modules}
    (lineSection : 𝟙_ sourceScheme.Modules ⟶ lineBundle) {opens : sourceScheme.Opens} {localFunction
      : Γ(sourceScheme, opens)} {exponent : ℕ} (extendedSection : Γ(lineBundle.tensorPow exponent,
      ⊤))
    (hv : (lineBundle.tensorPow exponent).presheaf.map (homOfLE le_top).op extendedSection =
      localFunction • tensorPowSectionOne lineSection exponent opens)
    {largerExponent : ℕ} (hkl : exponent ≤ largerExponent) :
    ∃ nextSection : Γ(lineBundle.tensorPow largerExponent, ⊤),
      (lineBundle.tensorPow largerExponent).presheaf.map (homOfLE le_top).op nextSection =
        localFunction • tensorPowSectionOne lineSection largerExponent opens := by
  induction largerExponent, hkl using Nat.le_induction with
  | base => exact ⟨extendedSection, hv⟩
  | succ largerExponent _ ih =>
    obtain ⟨nextSection, hv'⟩ := ih
    refine ⟨tmulSection (lineSection.app ⊤ (unitSectionsEquiv ⊤ 1)) nextSection, (tmulSection_map
      le_top _ _).trans ?_⟩
    rw [hv', ← Hom.app_presheaf_map, presheaf_map_unitSectionsEquiv, map_one, tmulSection_smul,
      tensorPowSectionOne_succ]

/-- On a quasi-compact scheme separated over an affine base, a function on the nonvanishing locus
of an invertible-module section extends globally after multiplication by a suitable tensor
power. -/
lemma Scheme.Modules.exists_restrict_eq_smul_tensorPowSectionOne {baseScheme : Scheme.{u}}
  (structureMap : sourceScheme ⟶ baseScheme)
    [IsSeparated structureMap] [IsAffine baseScheme] [CompactSpace sourceScheme] (lineBundle :
      sourceScheme.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} lineBundle]
      (lineSection : 𝟙_ sourceScheme.Modules ⟶ lineBundle)
    (localFunction : Γ(sourceScheme, (Hom.zeroLocus lineSection).support.compl)) :
    ∃ (exponent : ℕ) (extendedSection : Γ(lineBundle.tensorPow exponent, ⊤)),
      (lineBundle.tensorPow exponent).presheaf.map (homOfLE (le_top : (Hom.zeroLocus
        lineSection).support.compl ≤ ⊤)).op
        extendedSection = localFunction • tensorPowSectionOne lineSection exponent (Hom.zeroLocus
          lineSection).support.compl := by
  have : SheafOfModules.IsQuasicoherent (R := sourceScheme.ringCatSheaf) (𝟙_ sourceScheme.Modules)
    :=
    SheafOfModules.isQuasicoherent_unit (ringSheaf := sourceScheme.ringCatSheaf)
  obtain ⟨exponent, tensorSection, hu⟩ :=
    exists_tensorPowSection_eq_restrict structureMap lineBundle lineSection (𝟙_
      sourceScheme.Modules) (unitSectionsEquiv _ localFunction)
  refine ⟨exponent, (λ_ (lineBundle.tensorPow exponent)).hom.app ⊤ tensorSection, ?_⟩
  rw [← Hom.app_presheaf_map, hu, rightUnitor_inv_comp_whiskerLeft_app,
    leftUnitor_hom_app_tmulSection]

/-- Generation by quotients with denominator one transports to any denominator equal to one. -/
private lemma subring_closure_divBasicOpen_eq_top_of_eq_one {chartScheme baseScheme : Scheme.{u}}
  (chartMap : chartScheme ⟶ baseScheme)
    (openSubset : baseScheme.Opens) {denominator : Γ(chartScheme, ⊤)} (hb : denominator = 1)
      {generatorIndices : Type*} (functions : generatorIndices → Γ(chartScheme, ⊤))
    (hle : chartScheme.basicOpen denominator ≤ chartMap ⁻¹ᵁ openSubset) (hle₁ :
      chartScheme.basicOpen (1 : Γ(chartScheme, ⊤)) ≤ chartMap ⁻¹ᵁ openSubset)
    (equality : Subring.closure (Set.range (chartMap.resLE openSubset (chartScheme.basicOpen 1)
      hle₁).appTop ∪
      Set.range fun functionIndex ↦ chartScheme.divBasicOpen (functions functionIndex) 1) = ⊤) :
    Subring.closure (Set.range (chartMap.resLE openSubset (chartScheme.basicOpen denominator)
      hle).appTop ∪
      Set.range fun functionIndex ↦ chartScheme.divBasicOpen (functions functionIndex) denominator)
        = ⊤ := by
  subst hb
  exact equality

end Auxiliary

/-- A finite family of sections of one invertible module, whose nonvanishing loci are affine and
cover a scheme separated and locally of finite type over an affine base, gives an immersion
into finite-coordinate projective space over that base. -/
theorem exists_isImmersion_projectiveSpace_of_isAffineOpen {sourceScheme baseScheme : Scheme.{u}}
  (structureMap : sourceScheme ⟶ baseScheme)
    [IsAffine baseScheme] [IsSeparated structureMap] [LocallyOfFiniteType structureMap] (lineBundle
      : sourceScheme.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} lineBundle] {indices
      : Type u} [Finite indices]
    (sections : indices → (𝟙_ sourceScheme.Modules ⟶ lineBundle))
    (hs : ∀ chartIndex, IsAffineOpen (Hom.zeroLocus (sections chartIndex)).support.compl)
    (hcov : ⨆ chartIndex, (Hom.zeroLocus (sections chartIndex)).support.compl = ⊤) :
    ∃ (coordinates : Type u) (_ : Finite coordinates) (coordinate : sourceScheme ⟶ ℙ(coordinates;
      baseScheme)), IsImmersion coordinate ∧ coordinate ≫ ℙ(coordinates; baseScheme) ↘ baseScheme =
      structureMap := by
  classical
  set opens : indices → sourceScheme.Opens := fun chartIndex ↦ (Hom.zeroLocus (sections
    chartIndex)).support.compl
  have hUa (chartIndex : indices) : IsAffine (opens chartIndex).toScheme := hs chartIndex
  have : CompactSpace sourceScheme := by
    refine ⟨?_⟩
    have equality := isCompact_iUnion fun chartIndex ↦ (hs chartIndex).isCompact
    rwa [← TopologicalSpace.Opens.coe_iSup, hcov, TopologicalSpace.Opens.coe_top] at equality
  choose generatorIndices hm functions ht using fun chartIndex ↦
    exists_finite_subring_closure_divBasicOpen_eq_top
    ((opens chartIndex).ι ≫ structureMap) 1 ⊤ (isAffineOpen_top baseScheme) fun _ _ ↦ trivial
  have : ∀ chartIndex, Finite (generatorIndices chartIndex) := hm
  choose exponent extendedSection hv using fun generatorIndex : Σ chartIndex, generatorIndices
    chartIndex ↦
    exists_restrict_eq_smul_tensorPowSectionOne structureMap lineBundle (sections generatorIndex.1)
      ((opens generatorIndex.1).topIso.hom (functions generatorIndex.1 generatorIndex.2))
  obtain ⟨commonExponent, hN⟩ := Finite.exists_le exponent
  choose extendedSections hw using fun generatorIndex : Σ chartIndex, generatorIndices chartIndex ↦
    exists_restrict_eq_smul_tensorPowSectionOne_of_le (sections generatorIndex.1) (extendedSection
      generatorIndex) (hv generatorIndex)
      ((hN generatorIndex).trans commonExponent.le_succ)
  set coordinates : Type u := indices ⊕ Σ chartIndex, generatorIndices chartIndex
  set globalSections : coordinates → Γ(lineBundle.tensorPow (commonExponent + 1), ⊤) :=
    Sum.elim (fun chartIndex ↦ tensorPowSectionOne (sections chartIndex) (commonExponent + 1) ⊤)
      extendedSections
  set coordinateOpens : coordinates → sourceScheme.Opens := Sum.elim opens fun _ ↦ ⊥
  have coordinateGenerators (coordinate : coordinates) : IsFreeGenerator
      ((lineBundle.tensorPow (commonExponent + 1)).presheaf.map (homOfLE (le_top : coordinateOpens
        coordinate ≤ ⊤)).op (globalSections coordinate)) := by
    rcases coordinate with chartIndex | generatorIndex
    · simp only [globalSections, coordinateOpens, Sum.elim_inl]
      rw [presheaf_map_tensorPowSectionOne]
      exact isFreeGenerator_tensorPowSectionOne _ (isFreeGenerator_app_one_of_le _ le_rfl) _
    · exact isFreeGenerator_bot _
  have coordinateCover : ⨆ coordinate, coordinateOpens coordinate = ⊤ :=
    eq_top_iff.mpr (hcov.ge.trans (iSup_le fun chartIndex ↦ le_iSup coordinateOpens (Sum.inl
      chartIndex)))
  set projectiveMap := ProjectiveSpace.homOfIsFreeGenerator globalSections coordinateOpens
    coordinateGenerators structureMap coordinateCover
  have hpre (chartIndex : indices) : projectiveMap ⁻¹ᵁ ProjectiveSpace.standardOpen coordinates
    baseScheme (Sum.inl chartIndex) = opens chartIndex := by
    refine le_antisymm (le_compl_support_zeroLocus_of_isFreeGenerator (sections chartIndex)
      commonExponent.succ_ne_zero ?_)
      (ProjectiveSpace.le_preimage_standardOpen globalSections coordinateOpens coordinateGenerators
        structureMap coordinateCover (Sum.inl chartIndex))
    have equality := ProjectiveSpace.isFreeGenerator_of_twistRestrict_iso
      (ProjectiveSpace.twistRestrictHom globalSections coordinateOpens coordinateGenerators
        structureMap coordinateCover)
      (ProjectiveSpace.twistRestrictHom_app_pullbackSection globalSections coordinateOpens
        coordinateGenerators structureMap coordinateCover) (Sum.inl chartIndex)
    simp only [globalSections, Sum.elim_inl] at equality
    rwa [presheaf_map_tensorPowSectionOne] at equality
  refine ⟨coordinates, inferInstance, projectiveMap, ?_, ProjectiveSpace.homOfIsFreeGenerator_over
    globalSections coordinateOpens coordinateGenerators structureMap coordinateCover⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup
    (fun chartIndex : indices ↦ ProjectiveSpace.standardOpen coordinates baseScheme (Sum.inl
      chartIndex)) ?_ fun chartIndex ↦ ?_
  · rintro _ ⟨point, rfl⟩
    have hx : point ∈ ⨆ chartIndex, opens chartIndex := by rw [hcov]; trivial
    obtain ⟨chartIndex, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact SetLike.mem_coe.mpr (TopologicalSpace.Opens.mem_iSup.mpr ⟨chartIndex, (hpre chartIndex).ge
      hxi⟩)
  set chartSections := ProjectiveSpace.localSections globalSections coordinateOpens
    coordinateGenerators (Sum.inl chartIndex)
  have h₁ : chartSections (Sum.inl chartIndex) = 1 := by
    simp [chartSections, ProjectiveSpace.localSections]
  have ht' (functionIndex : generatorIndices chartIndex) : chartSections (Sum.inr ⟨chartIndex,
    functionIndex⟩) = functions chartIndex functionIndex := by
    have equality : ProjectiveSpace.sectionRatio globalSections coordinateOpens coordinateGenerators
      (Sum.inl chartIndex) (Sum.inr ⟨chartIndex, functionIndex⟩) =
        (opens chartIndex).topIso.hom (functions chartIndex functionIndex) := by
      refine ((coordinateGenerators (Sum.inl chartIndex)).coeff_eq_iff _ _).mpr ?_
      simp only [globalSections, coordinateOpens, Sum.elim_inl, Sum.elim_inr]
      rw [presheaf_map_tensorPowSectionOne]
      exact (hw ⟨chartIndex, functionIndex⟩).symm
    simp only [chartSections, ProjectiveSpace.localSections, equality]
    exact Iso.hom_inv_id_apply _ _
  set chartBasicOpen := (opens chartIndex).toScheme.basicOpen (chartSections (Sum.inl chartIndex))
  have : IsIso chartBasicOpen.ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by
      rw [Scheme.Opens.opensRange_ι]
      simp [chartBasicOpen, h₁])
  have key : chartBasicOpen.ι ≫ projectiveMap.resLE (ProjectiveSpace.standardOpen coordinates
    baseScheme (Sum.inl chartIndex)) (opens chartIndex) (hpre chartIndex).ge =
      (ProjectiveSpace.homOfSections ((opens chartIndex).ι ≫ structureMap) chartSections
        (ProjectiveSpace.span_range_localSections globalSections coordinateOpens
          coordinateGenerators (Sum.inl chartIndex))).resLE
        (ProjectiveSpace.standardOpen coordinates baseScheme (Sum.inl chartIndex)) chartBasicOpen
        (ProjectiveSpace.homOfSections_preimage_standardOpen _ _ _ _).ge := by
    rw [← cancel_mono (ProjectiveSpace.standardOpen coordinates baseScheme (Sum.inl chartIndex)).ι,
      Category.assoc,
      Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι]
    exact congrArg (chartBasicOpen.ι ≫ ·) (ProjectiveSpace.ι_homOfIsFreeGenerator globalSections
      coordinateOpens coordinateGenerators structureMap coordinateCover (Sum.inl chartIndex))
  rw [← Scheme.Hom.resLE_eq_morphismRestrict,
    Scheme.Hom.resLE_congr projectiveMap (U := ProjectiveSpace.standardOpen coordinates baseScheme
      (Sum.inl chartIndex)) le_rfl rfl
      (hpre chartIndex) @IsImmersion,
    ← MorphismProperty.cancel_left_of_respectsIso @IsImmersion chartBasicOpen.ι, key,
    ← MorphismProperty.cancel_right_of_respectsIso @IsImmersion _
      (ProjectiveSpace.standardOpenIso coordinates baseScheme (Sum.inl chartIndex)).hom,
    ProjectiveSpace.homOfSections_resLE_standardOpenIso_hom]
  refine isImmersion_homOfVector_divBasicOpen ((opens chartIndex).ι ≫ structureMap) chartSections
    (Sum.inl chartIndex) ⊤
    (isAffineOpen_top baseScheme) (fun _ _ ↦ trivial) (eq_top_iff.mpr
      ((subring_closure_divBasicOpen_eq_top_of_eq_one _ _ h₁ (functions chartIndex) _ _ (ht
        chartIndex)).ge.trans
        (Subring.closure_mono (Set.union_subset_union_right _ ?_))))
  rintro _ ⟨functionIndex, rfl⟩
  exact ⟨⟨Sum.inr ⟨chartIndex, functionIndex⟩, Sum.inr_ne_inl⟩,
    congrArg (fun point ↦ (opens chartIndex).toScheme.divBasicOpen point (chartSections (Sum.inl
      chartIndex))) (ht' functionIndex)⟩


end AlgebraicGeometry
