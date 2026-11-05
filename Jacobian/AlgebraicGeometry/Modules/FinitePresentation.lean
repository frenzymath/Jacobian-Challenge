import Jacobian.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
import Jacobian.AlgebraicGeometry.Modules.Quasicoherent
import Jacobian.AlgebraicGeometry.Modules.Localization
import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-!
# Finite presentation and affine sections

The sections of a finitely presented module sheaf on an affine open form a
finitely presented module. The proof descends finite presentation from basic
opens carrying finite presentations, using localization of quasi-coherent
sections.

For a quasi-coherent module on `Spec R`, finite presentation is equivalent both
to finite presentation of its global sections over `R` and to existence of a
finite global presentation. On a general scheme, finite presentation of a
quasi-coherent module can be checked on all affine opens. No Noetherian
hypothesis is needed for these criteria.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme source : Scheme.{schemeUniverse}}

/-- A presentation on an over-site restricts along an open immersion with image in that open. -/
def presentationRestrictOfOver {moduleSheaf : scheme.Modules} {openSubset : scheme.Opens}
    (presentation : (moduleSheaf.over openSubset).Presentation) (morphism : source ⟶ scheme)
    [IsOpenImmersion morphism] (imageLe : morphism.opensRange ≤ openSubset) :
    (moduleSheaf.restrict morphism).Presentation :=
  let lift : source ⟶ openSubset.toScheme := IsOpenImmersion.lift openSubset.ι morphism (by
    rw [Scheme.Opens.range_ι]
    exact imageLe)
  haveI : IsOpenImmersion (lift ≫ openSubset.ι) := by
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  haveI : IsOpenImmersion lift := IsOpenImmersion.of_comp lift openSubset.ι
  haveI : PreservesColimitsOfSize.{schemeUniverse, schemeUniverse} (restrictFunctor lift) :=
    inferInstance
  let functor := (overEquiv openSubset).functor ⋙ restrictFunctor lift
  let restrictionIso : SheafOfModules.overFunctor scheme.ringCatSheaf openSubset ⋙ functor ≅
      restrictFunctor morphism :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (overFunctorEquiv openSubset) _ ≪≫
      (restrictFunctorComp lift openSubset.ι).symm ≪≫
      restrictFunctorCongr (IsOpenImmersion.lift_fac _ _ _)
  SheafOfModules.Presentation.ofIsIso.{schemeUniverse, schemeUniverse, schemeUniverse}
    (restrictionIso.app moduleSheaf).hom (presentation.map functor (restrictUnitIso _).symm)

instance isFinite_presentationRestrictOfOver {moduleSheaf : scheme.Modules}
    {openSubset : scheme.Opens} (presentation : (moduleSheaf.over openSubset).Presentation)
    [presentation.IsFinite] (morphism : source ⟶ scheme) [IsOpenImmersion morphism]
    (imageLe : morphism.opensRange ≤ openSubset) :
    (presentationRestrictOfOver presentation morphism imageLe).IsFinite := by
  dsimp [presentationRestrictOfOver]
  infer_instance

/-- Sections on an affine open agree with the global sections of its affine chart. -/
def sectionsRestrictFromSpecLinearEquiv (moduleSheaf : scheme.Modules)
    {openSubset : scheme.Opens} (affine : IsAffineOpen openSubset) :
    moduleSpecΓFunctor.obj (moduleSheaf.restrict affine.fromSpec) ≃ₗ[Γ(scheme, openSubset)]
      Γ(moduleSheaf, openSubset) := by
  have openLeImage : openSubset ≤ affine.fromSpec ''ᵁ ⊤ :=
    (affine.opensRange_fromSpec.symm.trans (Scheme.Hom.image_top_eq_opensRange _).symm).le
  have imageLeOpen : affine.fromSpec ''ᵁ ⊤ ≤ openSubset := affine.fromSpec_image_le ⊤
  have restrictRestrict (sectionValue : Γ(moduleSheaf, openSubset)) :
      moduleSheaf.presheaf.map (homOfLE openLeImage).op
        (moduleSheaf.presheaf.map (homOfLE imageLeOpen).op sectionValue) = sectionValue := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      show (homOfLE imageLeOpen).op ≫ (homOfLE openLeImage).op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id]
    rfl
  have restrictRestrictImage (sectionValue : Γ(moduleSheaf, affine.fromSpec ''ᵁ ⊤)) :
      moduleSheaf.presheaf.map (homOfLE imageLeOpen).op
        (moduleSheaf.presheaf.map (homOfLE openLeImage).op sectionValue) = sectionValue := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      show (homOfLE openLeImage).op ≫ (homOfLE imageLeOpen).op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id]
    rfl
  have restrictScalar (scalar : Γ(scheme, openSubset)) :
      scheme.presheaf.map (homOfLE openLeImage).op
        (scheme.presheaf.map (homOfLE imageLeOpen).op scalar) = scalar := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      show (homOfLE imageLeOpen).op ≫ (homOfLE openLeImage).op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id]
    rfl
  exact
    { toFun sectionValue := moduleSheaf.presheaf.map (homOfLE openLeImage).op
        ((moduleSheaf.restrictAppIso affine.fromSpec ⊤).hom sectionValue)
      invFun sectionValue := (moduleSheaf.restrictAppIso affine.fromSpec ⊤).inv
        (moduleSheaf.presheaf.map (homOfLE imageLeOpen).op sectionValue)
      map_add' first second := by simp only [map_add]
      map_smul' scalar sectionValue := by
        change moduleSheaf.presheaf.map (homOfLE openLeImage).op
          ((moduleSheaf.restrictAppIso affine.fromSpec ⊤).hom
            (scalar • (sectionValue : Γ(moduleSheaf.restrict affine.fromSpec, ⊤)))) = _
        rw [restrictAppIso_fromSpec_smul, Scheme.Modules.map_smul, restrictScalar]
        rfl
      left_inv sectionValue := by
        dsimp only
        rw [restrictRestrictImage]
        exact (moduleSheaf.restrictAppIso affine.fromSpec ⊤).hom_inv_id_apply sectionValue
      right_inv sectionValue := by
        dsimp only
        rw [Iso.inv_hom_id_apply, restrictRestrict] }

/-- A finite global presentation on an affine scheme gives finitely presented global sections. -/
theorem finitePresentation_sections_top_of_presentation {ring : CommRingCat.{schemeUniverse}}
    (moduleSheaf : (Spec ring).Modules) [IsIso moduleSheaf.fromTildeΓ]
    (presentation : moduleSheaf.Presentation) [presentation.IsFinite] :
    Module.FinitePresentation ring Γ(moduleSheaf, ⊤) := by
  let tildeFunctor := tilde.functor ring
  let relationsMap := (SheafOfModules.freeHomEquiv _).symm presentation.relations.s ≫
    kernel.ι presentation.generators.π
  let moduleRelationsMap : ModuleCat.of ring (presentation.relations.I →₀ ring) ⟶
      ModuleCat.of ring (presentation.generators.I →₀ ring) :=
    tildeFunctor.preimage
      ((tildeFinsupp _).hom ≫ relationsMap ≫ (tildeFinsupp _).inv)
  let cokernelIso : tildeFunctor.obj (cokernel moduleRelationsMap) ≅
      cokernel (tildeFunctor.map moduleRelationsMap) :=
    PreservesCokernel.iso tildeFunctor moduleRelationsMap
  let relationsIso : cokernel (tildeFunctor.map moduleRelationsMap) ≅ cokernel relationsMap :=
    cokernel.mapIso _ _ (tildeFinsupp _) (tildeFinsupp _) (by
      refine (tildeFunctor.map_preimage _ =≫ _).trans ?_
      simp)
  let presentationIso : cokernel relationsMap ≅ moduleSheaf :=
    (colimit.isColimit _).coconePointUniqueUpToIso presentation.isColimit
  let sectionsIso : moduleSheaf ≅ tildeFunctor.obj (moduleSpecΓFunctor.obj moduleSheaf) :=
    (asIso moduleSheaf.fromTildeΓ).symm
  let moduleIso : cokernel moduleRelationsMap ≅ moduleSpecΓFunctor.obj moduleSheaf :=
    tildeFunctor.preimageIso (cokernelIso ≪≫ relationsIso ≪≫ presentationIso ≪≫ sectionsIso)
  have : Module.FinitePresentation ring (cokernel (C := ModuleCat ring) moduleRelationsMap) := by
    have : Module.FinitePresentation ring (_ ⧸ LinearMap.range moduleRelationsMap.hom) :=
      Module.finitePresentation_of_surjective (LinearMap.range moduleRelationsMap.hom).mkQ
        (Submodule.mkQ_surjective _) (by
          rw [Submodule.ker_mkQ]
          exact Module.Finite.iff_fg.mp inferInstance)
    exact .of_equiv (ModuleCat.cokernelIsoRangeQuotient moduleRelationsMap).toLinearEquiv.symm
  exact .of_equiv moduleIso.toLinearEquiv

/-- A finitely presented module sheaf has finitely presented sections on every affine open. -/
theorem finitePresentation_sections_of_isFinitePresentation (moduleSheaf : scheme.Modules)
    [moduleSheaf.IsFinitePresentation] {openSubset : scheme.Opens}
    (affine : IsAffineOpen openSubset) :
    Module.FinitePresentation Γ(scheme, openSubset) Γ(moduleSheaf, openSubset) := by
  obtain ⟨localData, finiteData⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (R := scheme.ringCatSheaf) moduleSheaf
  have cover : IsOpenCover localData.X := (Opens.coversTop_iff _ localData.X).mp localData.coversTop
  let goodSections : Set Γ(scheme, openSubset) :=
    {scalar | Module.FinitePresentation Γ(scheme, scheme.basicOpen scalar)
      Γ(moduleSheaf, scheme.basicOpen scalar)}
  have spanGood : Ideal.span goodSections = ⊤ := by
    rw [← affine.self_le_iSup_basicOpen_iff]
    intro point membership
    obtain ⟨index, coverMembership⟩ := cover.exists_mem point
    obtain ⟨scalar, basicLe, basicMembership⟩ :=
      affine.exists_basicOpen_le ⟨point, coverMembership⟩ membership
    have basicAffine := affine.basicOpen scalar
    let presentation := presentationRestrictOfOver (localData.presentation index)
      basicAffine.fromSpec (basicAffine.opensRange_fromSpec.le.trans basicLe)
    have : (moduleSheaf.restrict basicAffine.fromSpec).IsQuasicoherent :=
      isQuasicoherent_restrictFunctor basicAffine.fromSpec moduleSheaf
    have : IsIso (moduleSheaf.restrict basicAffine.fromSpec).fromTildeΓ :=
      isIso_fromTildeΓ_of_isQuasicoherent _
    have : Module.FinitePresentation Γ(scheme, scheme.basicOpen scalar)
        (moduleSpecΓFunctor.obj (moduleSheaf.restrict basicAffine.fromSpec)) :=
      finitePresentation_sections_top_of_presentation _ presentation
    exact Opens.mem_iSup.mpr
      ⟨⟨scalar, .of_equiv (sectionsRestrictFromSpecLinearEquiv moduleSheaf basicAffine)⟩,
        basicMembership⟩
  let _ (scalar : goodSections) :
      Module Γ(scheme, openSubset) Γ(moduleSheaf, scheme.basicOpen scalar.1) :=
    Module.compHom _ (algebraMap Γ(scheme, openSubset) Γ(scheme, scheme.basicOpen scalar.1))
  have _ (scalar : goodSections) := isLocalizedModule_basicOpen moduleSheaf affine scalar.1
  have _ (scalar : goodSections) := affine.isLocalization_basicOpen scalar.1
  have _ (scalar : goodSections) :
      IsScalarTower Γ(scheme, openSubset) Γ(scheme, scheme.basicOpen scalar.1)
        Γ(moduleSheaf, scheme.basicOpen scalar.1) :=
    ⟨fun first second sectionValue ↦ mul_smul
      (algebraMap Γ(scheme, openSubset) Γ(scheme, scheme.basicOpen scalar.1) first)
      second sectionValue⟩
  exact Module.FinitePresentation.of_localizationSpan' goodSections spanGood
    (Rₚ := fun scalar : goodSections ↦ Γ(scheme, scheme.basicOpen scalar.1))
    (fun scalar ↦
      { toFun := moduleSheaf.presheaf.map (homOfLE (scheme.basicOpen_le scalar.1)).op
        map_add' := map_add _
        map_smul' := map_smul moduleSheaf _ }) fun scalar ↦ scalar.2

instance isFinite_presentationOverOfRestrict {moduleSheaf : scheme.Modules}
    (openSubset : scheme.Opens) (presentation : (moduleSheaf.restrict openSubset.ι).Presentation)
    [presentation.IsFinite] : (presentationOverOfRestrict openSubset presentation).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite presentation.generators.I)⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite presentation.relations.I)⟩

/-- Finite global presentations on an open cover give the native finite-presentation property. -/
theorem isFinitePresentation_of_isOpenCover (moduleSheaf : scheme.Modules)
    {indices : Type schemeUniverse} {openSubsets : indices → scheme.Opens}
    (cover : IsOpenCover openSubsets)
    (presentations : ∀ index, (moduleSheaf.restrict (openSubsets index).ι).Presentation)
    [∀ index, (presentations index).IsFinite] : moduleSheaf.IsFinitePresentation := by
  let localData : SheafOfModules.QuasicoherentData.{schemeUniverse, schemeUniverse,
      schemeUniverse, schemeUniverse} moduleSheaf :=
    { I := indices
      X := openSubsets
      coversTop := (Opens.coversTop_iff _ openSubsets).mpr cover
      presentation index := presentationOverOfRestrict (openSubsets index) (presentations index) }
  have : localData.IsFinitePresentation :=
    { isFinite_presentation index := inferInstanceAs
        (presentationOverOfRestrict (openSubsets index) (presentations index)).IsFinite }
  exact localData.isFinitePresentation

instance isFinite_presentationRestrictOpensRange {moduleSheaf : scheme.Modules}
    (morphism : source ⟶ scheme) [IsOpenImmersion morphism]
    (presentation : (moduleSheaf.restrict morphism).Presentation) [presentation.IsFinite] :
    (presentationRestrictOpensRange morphism presentation).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite presentation.generators.I)⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite presentation.relations.I)⟩

/-- Finite presentations along open immersions covering the scheme give finite presentation. -/
theorem isFinitePresentation_of_iSup_opensRange_eq_top (moduleSheaf : scheme.Modules)
    {indices : Type schemeUniverse} {sources : indices → Scheme.{schemeUniverse}}
    (morphisms : ∀ index, sources index ⟶ scheme) [∀ index, IsOpenImmersion (morphisms index)]
    (cover : ⨆ index, (morphisms index).opensRange = ⊤)
    (presentations : ∀ index, (moduleSheaf.restrict (morphisms index)).Presentation)
    [∀ index, (presentations index).IsFinite] : moduleSheaf.IsFinitePresentation :=
  isFinitePresentation_of_isOpenCover moduleSheaf
    (openSubsets := fun index ↦ (morphisms index).opensRange) cover
    (fun index ↦ presentationRestrictOpensRange (morphisms index) (presentations index))

/-- A quasi-coherent module with finitely presented affine sections has a finite presentation. -/
theorem exists_presentation_isFinite_of_finitePresentation_sections
    {ring : CommRingCat.{schemeUniverse}} (moduleSheaf : (Spec ring).Modules)
    [moduleSheaf.IsQuasicoherent] [Module.FinitePresentation ring Γ(moduleSheaf, ⊤)] :
    ∃ presentation : moduleSheaf.Presentation, presentation.IsFinite := by
  let sections := (modulesSpecToSheaf.obj moduleSheaf).presheaf.obj (.op ⊤)
  have : Module.FinitePresentation ring sections := ‹Module.FinitePresentation ring Γ(moduleSheaf, ⊤)›
  obtain ⟨generators, spanGenerators, relations, spanRelations⟩ :=
    Module.FinitePresentation.out (R := ring) (M := sections)
  have : IsIso (C := SheafOfModules.{schemeUniverse} (Spec ring).ringCatSheaf)
      moduleSheaf.fromTildeΓ :=
    isIso_fromTildeΓ_of_isQuasicoherent moduleSheaf
  exact ⟨(presentationTilde sections (generators : Set sections) spanGenerators
      (relations : Set _) spanRelations).ofIsIso moduleSheaf.fromTildeΓ,
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (generators : Set sections))⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite (relations : Set (generators →₀ ring)))⟩ }⟩

/-- Finitely presented affine sections are equivalent to a finite global presentation. -/
theorem finitePresentation_sections_iff_exists_presentation_isFinite
    {ring : CommRingCat.{schemeUniverse}} (moduleSheaf : (Spec ring).Modules)
    [moduleSheaf.IsQuasicoherent] :
    Module.FinitePresentation ring Γ(moduleSheaf, ⊤) ↔
      ∃ presentation : moduleSheaf.Presentation, presentation.IsFinite := by
  constructor
  · intro finiteSections
    letI : Module.FinitePresentation ring Γ(moduleSheaf, ⊤) := finiteSections
    exact exists_presentation_isFinite_of_finitePresentation_sections moduleSheaf
  · rintro ⟨presentation, finitePresentation⟩
    exact finitePresentation_sections_top_of_presentation moduleSheaf presentation

/-- Finite presentation of a module sheaf on `Spec R` gives finite presentation over `R`. -/
theorem finitePresentation_sections_top_of_isFinitePresentation
    {ring : CommRingCat.{schemeUniverse}} (moduleSheaf : (Spec ring).Modules)
    [moduleSheaf.IsFinitePresentation] : Module.FinitePresentation ring Γ(moduleSheaf, ⊤) := by
  letI : Module.FinitePresentation Γ(Spec ring, ⊤) Γ(moduleSheaf, ⊤) :=
    finitePresentation_sections_of_isFinitePresentation moduleSheaf (isAffineOpen_top _)
  have algebraMapBijective : Function.Bijective (Algebra.linearMap ring Γ(Spec ring, ⊤)) := by
    constructor
    · intro first second equality
      have := congrArg (Scheme.ΓSpecIso ring).hom equality
      simpa using this
    · intro sectionValue
      exact ⟨(Scheme.ΓSpecIso ring).hom sectionValue, by simp⟩
  letI : Module.FinitePresentation ring Γ(Spec ring, ⊤) :=
    .of_equiv (LinearEquiv.ofBijective (Algebra.linearMap ring Γ(Spec ring, ⊤)) algebraMapBijective)
  exact Module.FinitePresentation.trans ring Γ(moduleSheaf, ⊤) Γ(Spec ring, ⊤)

/-- On `Spec R`, the native finite-presentation property is equivalent to that of sections. -/
theorem isFinitePresentation_iff_finitePresentation_sections_top
    {ring : CommRingCat.{schemeUniverse}} (moduleSheaf : (Spec ring).Modules)
    [moduleSheaf.IsQuasicoherent] :
    moduleSheaf.IsFinitePresentation ↔ Module.FinitePresentation ring Γ(moduleSheaf, ⊤) := by
  constructor
  · intro finitePresentation
    letI : moduleSheaf.IsFinitePresentation := finitePresentation
    exact finitePresentation_sections_top_of_isFinitePresentation moduleSheaf
  · intro finiteSections
    letI : Module.FinitePresentation ring Γ(moduleSheaf, ⊤) := finiteSections
    obtain ⟨presentation, finitePresentation⟩ :=
      exists_presentation_isFinite_of_finitePresentation_sections moduleSheaf
    exact presentation.isFinitePresentation

/-- Finite presentation of a quasi-coherent module can be tested on all affine opens. -/
theorem isFinitePresentation_iff_forall_isAffineOpen (moduleSheaf : scheme.Modules)
    [moduleSheaf.IsQuasicoherent] :
    moduleSheaf.IsFinitePresentation ↔ ∀ (openSubset : scheme.Opens), IsAffineOpen openSubset →
      Module.FinitePresentation Γ(scheme, openSubset) Γ(moduleSheaf, openSubset) := by
  constructor
  · intro finitePresentation openSubset affine
    letI : moduleSheaf.IsFinitePresentation := finitePresentation
    exact finitePresentation_sections_of_isFinitePresentation moduleSheaf affine
  · intro finiteSections
    have (openSubset : scheme.affineOpens) :
        Module.FinitePresentation Γ(scheme, openSubset.1)
          Γ(moduleSheaf.restrict openSubset.2.fromSpec, ⊤) := by
      letI := finiteSections openSubset.1 openSubset.2
      exact .of_equiv (sectionsRestrictFromSpecLinearEquiv moduleSheaf openSubset.2).symm
    choose presentations finitePresentations using fun openSubset : scheme.affineOpens ↦
      exists_presentation_isFinite_of_finitePresentation_sections
        (moduleSheaf.restrict openSubset.2.fromSpec)
    letI : ∀ openSubset, (presentations openSubset).IsFinite := finitePresentations
    exact isFinitePresentation_of_iSup_opensRange_eq_top moduleSheaf
      (fun openSubset : scheme.affineOpens ↦ openSubset.2.fromSpec)
      (by simpa only [IsAffineOpen.opensRange_fromSpec] using iSup_affineOpens_eq_top scheme)
      presentations

/-- Over a Noetherian affine scheme, finite quasi-coherent sections give finite presentation. -/
theorem isFinitePresentation_of_finite {ring : CommRingCat.{schemeUniverse}}
    [IsNoetherianRing ring] (moduleSheaf : (Spec ring).Modules) [moduleSheaf.IsQuasicoherent]
    [Module.Finite ring Γ(moduleSheaf, ⊤)] : moduleSheaf.IsFinitePresentation := by
  letI := Module.finitePresentation_of_finite ring Γ(moduleSheaf, ⊤)
  exact (isFinitePresentation_iff_finitePresentation_sections_top moduleSheaf).mpr inferInstance

variable {X Y : Scheme.{schemeUniverse}}

/-- A finite presentation admits finite presentations on an open cover. -/
theorem exists_isOpenCover_presentation_isFinite (M : X.Modules) [M.IsFinitePresentation] :
    ∃ (ι : Type schemeUniverse) (U : ι → X.Opens)
      (P : ∀ i, (M.restrict (U i).ι).Presentation),
      IsOpenCover U ∧ ∀ i, (P i).IsFinite := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (R := X.ringCatSheaf) M
  exact ⟨q.I, q.X, fun i ↦ presentationRestrictOfOver (q.presentation i)
    (Scheme.Opens.ι (q.X i)) (by simp), (Opens.coversTop_iff _ q.X).mp q.coversTop,
    fun i ↦ inferInstance⟩

/-- Pullback preserves finite presentation of quasi-coherent module sheaves. -/
instance isFinitePresentation_pullback (g : X ⟶ Y) (M : Y.Modules)
    [M.IsFinitePresentation] : ((pullback g).obj M).IsFinitePresentation := by
  obtain ⟨ι, U, pres, hU, hfin⟩ := exists_isOpenCover_presentation_isFinite M
  have (i : ι) : PreservesColimitsOfSize.{schemeUniverse, schemeUniverse}
      (pullback (g ∣_ U i)) := inferInstance
  let P (i : ι) : (((pullback g).obj M).restrict (g ⁻¹ᵁ U i).ι).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{schemeUniverse, schemeUniverse, schemeUniverse}
      ((restrictFunctorIsoPullback _).app _ ≪≫
        (pullbackComp (g ⁻¹ᵁ U i).ι g).app M ≪≫
        (pullbackCongr (morphismRestrict_ι g (U i)).symm).app M ≪≫
        (pullbackComp (g ∣_ U i) (U i).ι).symm.app M ≪≫
        (pullback (g ∣_ U i)).mapIso ((restrictFunctorIsoPullback _).app M).symm).inv
      ((pres i).map (pullback (g ∣_ U i)) (pullbackObjUnitIso _).symm)
  have (i : ι) : (P i).IsFinite := by
    dsimp only [P]
    infer_instance
  refine isFinitePresentation_of_isOpenCover _ (openSubsets := fun i ↦ g ⁻¹ᵁ U i) ?_ P
  refine IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ ?_)
  obtain ⟨i, hi⟩ := hU.exists_mem (g.base x)
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

end AlgebraicGeometry.Scheme.Modules
