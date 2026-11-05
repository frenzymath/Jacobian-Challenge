import Jacobian.AlgebraicGeometry.Cohomology.FlatBaseChange
import Jacobian.AlgebraicGeometry.Cohomology.SectionsBaseChange
import Jacobian.AlgebraicGeometry.Modules.Sections
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Canonical base change of the sections of a pencil

The flat base-change theorem is compared with actual pullback of sections in
degree zero. In particular it proves injectivity of the canonical cohomology
map, not just existence of an unspecified equivalence of vector spaces.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory Limits Abelian TopologicalSpace Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

namespace AlgebraicGeometry.SectionPencil

private theorem sectionsBaseChange_injective
    {source pulledSource base extension : Scheme.{u}}
    {structureMap : source ⟶ base} {pulledStructureMap : pulledSource ⟶ extension}
    {baseMap : extension ⟶ base} {projection : pulledSource ⟶ source}
    (cartesian : IsPullback projection pulledStructureMap structureMap baseMap)
    (moduleSheaf : source.Modules) [moduleSheaf.IsQuasicoherent]
    [IsAffine base] [IsAffine extension] [Flat baseMap]
    [QuasiSeparated structureMap] [QuasiCompact structureMap]
    [Algebra Γ(base, ⊤) Γ(extension, ⊤)]
    (scalarEquation : algebraMap Γ(base, ⊤) Γ(extension, ⊤) = baseMap.appTop.hom) :
    Function.Injective (sectionsModuleBaseChange cartesian moduleSheaf scalarEquation ⊤) := by
  have compactSource : CompactSpace source :=
    QuasiCompact.compactSpace_of_compactSpace structureMap
  letI := compactSource
  have square :
      ⇑(pushforwardSectionsAddEquiv pulledStructureMap projection moduleSheaf ⊤) ∘
          ⇑(cohomologyBaseChange cartesian moduleSheaf scalarEquation
            (TopCat.Sheaf.freeSheaf ⊤) 0) =
        ⇑(sectionsModuleBaseChange cartesian moduleSheaf scalarEquation ⊤) ∘
          ⇑((sectionsLinearEquiv moduleSheaf ⊤).lTensor Γ(extension, ⊤)) := by
    funext tensorElement
    induction tensorElement using TensorProduct.induction_on with
    | zero => simp only [Function.comp_apply, map_zero]
    | add firstElement secondElement firstEquation secondEquation =>
      simp only [Function.comp_apply, map_add] at firstEquation secondEquation ⊢
      rw [firstEquation, secondEquation]
    | tmul scalar element =>
      change TopCat.Sheaf.extFreeSheafZeroAddEquiv ⊤ _
          ((Ext.WithAction.toExt _ element).comp
            (Ext.mk₀ (toSheafUnit projection moduleSheaf ≫
              pushforwardPullbackAction pulledStructureMap projection moduleSheaf scalar))
            (add_zero 0)) =
        sectionsModuleBaseChange cartesian moduleSheaf scalarEquation ⊤
          (scalar ⊗ₜ sectionsLinearEquiv moduleSheaf ⊤ element)
      rw [TopCat.Sheaf.extFreeSheafZeroAddEquiv_comp_mk₀,
        sectionsModuleBaseChange_tmul]
      rfl
  have bijectiveComparison := bijective_cohomologyBaseChange_of_isCompact
    cartesian moduleSheaf scalarEquation
    (openSubset := ⊤) (by rw [Opens.coe_top]; exact isCompact_univ) 0
  have injectiveComposite : Function.Injective
      (⇑(sectionsModuleBaseChange cartesian moduleSheaf scalarEquation ⊤) ∘
        ⇑((sectionsLinearEquiv moduleSheaf ⊤).lTensor Γ(extension, ⊤))) := by
    rw [← square]
    exact (pushforwardSectionsAddEquiv pulledStructureMap projection moduleSheaf ⊤).injective.comp
      bijectiveComparison.injective
  intro firstElement secondElement equality
  obtain ⟨firstPreimage, rfl⟩ :=
    ((sectionsLinearEquiv moduleSheaf ⊤).lTensor Γ(extension, ⊤)).surjective firstElement
  obtain ⟨secondPreimage, rfl⟩ :=
    ((sectionsLinearEquiv moduleSheaf ⊤).lTensor Γ(extension, ⊤)).surjective secondElement
  exact congrArg ((sectionsLinearEquiv moduleSheaf ⊤).lTensor Γ(extension, ⊤))
    (injectiveComposite equality)

/-- The actual canonical field-extension map is injective in degree zero. -/
theorem canonicalH0BaseChange_injective {baseField extensionField : Type u}
    [Field baseField] [Field extensionField] [Algebra baseField extensionField]
    {source : Scheme.{u}} [source.Over (Spec (.of baseField))]
    [QuasiCompact (source ↘ Spec (.of baseField))]
    [QuasiSeparated (source ↘ Spec (.of baseField))]
    (moduleSheaf : source.Modules) [moduleSheaf.IsQuasicoherent] :
    Function.Injective (H.baseChange (baseField := baseField) extensionField moduleSheaf 0) := by
  let structureMap := source ↘ Spec (.of baseField)
  let baseMap := Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))
  let projection := Limits.pullback.fst structureMap baseMap
  let pulledStructureMap := Limits.pullback.snd structureMap baseMap
  let pulledModule := (Scheme.Modules.pullback projection).obj moduleSheaf
  let baseRing := Γ(Spec (.of baseField), ⊤)
  let extensionRing := Γ(Spec (.of extensionField), ⊤)
  letI : Algebra baseRing extensionRing := baseMap.appTop.hom.toAlgebra
  let baseEquiv : baseField ≃+* baseRing :=
    (Scheme.ΓSpecIso (.of baseField)).symm.commRingCatIsoToRingEquiv
  let extensionEquiv : extensionField ≃+* extensionRing :=
    (Scheme.ΓSpecIso (.of extensionField)).symm.commRingCatIsoToRingEquiv
  letI : RingHomInvPair baseEquiv.toRingHom baseEquiv.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv baseEquiv
  letI : RingHomInvPair baseEquiv.symm.toRingHom baseEquiv.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm baseEquiv
  let coefficientEquiv : LinearEquiv baseEquiv.toRingHom
      (σ' := baseEquiv.symm.toRingHom) extensionField extensionRing :=
    { extensionEquiv.toAddEquiv with
      map_smul' := fun scalar coefficient ↦ by
        rw [Algebra.smul_def, Algebra.smul_def]
        change extensionEquiv (algebraMap baseField extensionField scalar * coefficient) =
          baseMap.appTop (baseEquiv scalar) * extensionEquiv coefficient
        rw [map_mul]
        congr 1
        exact ConcreteCategory.congr_hom
          (Scheme.ΓSpecIso_inv_naturality
            (CommRingCat.ofHom (algebraMap baseField extensionField))) scalar }
  let sectionEquiv : LinearEquiv baseEquiv.toRingHom
      (σ' := baseEquiv.symm.toRingHom) (moduleSheaf.H 0)
      (sectionsModule structureMap moduleSheaf ⊤) :=
    { (H.zeroLinearEquiv moduleSheaf).toAddEquiv with
      map_smul' := fun scalar element ↦ by
        change H.zeroLinearEquiv moduleSheaf
            (globalSectionsRingHom baseField (X := source) scalar • element) =
          source.presheaf.map (homOfLE (le_refl (⊤ : source.Opens))).op
            (structureMap.appTop (baseEquiv scalar)) • H.zeroLinearEquiv moduleSheaf element
        rw [(H.zeroLinearEquiv moduleSheaf).map_smul]
        simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
          ConcreteCategory.id_apply]
        rfl }
  let tensorEquiv := TensorProduct.congr (σ₂₁ := baseEquiv.symm.toRingHom)
    coefficientEquiv sectionEquiv
  let sectionComparison := sectionsModuleBaseChange
    (IsPullback.of_hasPullback structureMap baseMap) moduleSheaf rfl ⊤
  let evaluation : pulledModule.H 0 →+ sectionsModule pulledStructureMap pulledModule
      (projection ⁻¹ᵁ ⊤) :=
    ((pulledModule.presheaf.map
      (homOfLE (le_top : projection ⁻¹ᵁ ⊤ ≤ ⊤)).op).hom).comp
        (H.zeroLinearEquiv pulledModule).toAddMonoidHom
  have evaluation_apply (element : pulledModule.H 0) :
      evaluation element = pulledModule.presheaf.map
        (homOfLE (le_top : projection ⁻¹ᵁ ⊤ ≤ ⊤)).op
        (H.zeroLinearEquiv pulledModule element) := rfl
  have square (tensorElement : extensionField ⊗[baseField] moduleSheaf.H 0) :
      sectionComparison (tensorEquiv tensorElement) =
        evaluation (H.baseChange (baseField := baseField) extensionField moduleSheaf 0
          tensorElement) := by
    induction tensorElement using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add firstElement secondElement firstEquation secondEquation =>
      simp only [map_add, firstEquation, secondEquation]
    | tmul scalar element =>
      letI : Module baseRing Γ(moduleSheaf, ⊤) :=
        (sectionsModule structureMap moduleSheaf ⊤).isModule
      have tensorFormula : tensorEquiv (scalar ⊗ₜ[baseField] element) =
          extensionEquiv scalar ⊗ₜ[baseRing] H.zeroLinearEquiv moduleSheaf element :=
        TensorProduct.congr_tmul coefficientEquiv sectionEquiv scalar element
      rw [tensorFormula, evaluation_apply, H.baseChange_tmul_zeroLinearEquiv,
        sectionsModuleBaseChange_tmul]
      change _ = pulledModule.presheaf.map _
        (globalSectionsRingHom extensionField
            (X := Limits.pullback structureMap baseMap) scalar •
          pulledModule.presheaf.map _
            (pullbackSection projection (H.zeroLinearEquiv moduleSheaf element)))
      rw [Scheme.Modules.map_smul, Scheme.Modules.presheaf_map_map_apply]
      simp only [homOfLE_refl, Category.id_comp, op_id,
        Scheme.Modules.pullbackSectionAddHom_apply]
      rw [Scheme.Modules.presheaf_map_id_apply (M := pulledModule)]
      have scalarEquation : pulledStructureMap.appTop (extensionEquiv scalar) =
          globalSectionsRingHom extensionField
            (X := Limits.pullback structureMap baseMap) scalar := rfl
      letI : Module Γ(Limits.pullback structureMap baseMap, projection ⁻¹ᵁ ⊤)
          (sectionsModule pulledStructureMap pulledModule (projection ⁻¹ᵁ ⊤)) :=
        inferInstanceAs
          (Module Γ(Limits.pullback structureMap baseMap, projection ⁻¹ᵁ ⊤)
            Γ(pulledModule, projection ⁻¹ᵁ ⊤))
      have scalarAction (coefficient : extensionRing)
          (sectionValue : sectionsModule pulledStructureMap pulledModule (projection ⁻¹ᵁ ⊤)) :
          coefficient • sectionValue =
            (Limits.pullback structureMap baseMap).presheaf.map
                ((projection ⁻¹ᵁ ⊤).leTop).op
                (pulledStructureMap.appTop coefficient) •
              (sectionValue : Γ(pulledModule, projection ⁻¹ᵁ ⊤)) := rfl
      simp only [scalarAction, scalarEquation, Scheme.Hom.preimage_top,
        TopologicalSpace.Opens.leTop, homOfLE_refl, op_id,
        CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
      dsimp only [projection] <;> rfl
  have injectiveSections := sectionsBaseChange_injective
    (IsPullback.of_hasPullback structureMap baseMap) moduleSheaf rfl
  intro firstElement secondElement equality
  apply tensorEquiv.injective
  apply injectiveSections
  exact (square firstElement).trans
    ((congrArg evaluation equality).trans (square secondElement).symm)

/-- Independent cohomology classes remain independent under actual field pullback. -/
theorem linearIndependent_baseChange {baseField extensionField : Type u}
    [Field baseField] [Field extensionField] [Algebra baseField extensionField]
    {source : Scheme.{u}} [source.Over (Spec (.of baseField))]
    [QuasiCompact (source ↘ Spec (.of baseField))]
    [QuasiSeparated (source ↘ Spec (.of baseField))]
    (moduleSheaf : source.Modules) [moduleSheaf.IsQuasicoherent]
    {indices : Type v} (classes : indices → moduleSheaf.H 0)
    (independent : LinearIndependent baseField classes) :
    LinearIndependent extensionField
      (fun index ↦ H.baseChange (baseField := baseField) extensionField moduleSheaf 0
        (1 ⊗ₜ[baseField] classes index)) := by
  have tensorIndependent :=
    Module.Flat.linearIndependent_one_tmul (S := extensionField) independent
  exact tensorIndependent.map'
    (H.baseChange (baseField := baseField) extensionField moduleSheaf 0)
    (LinearMap.ker_eq_bot.mpr (canonicalH0BaseChange_injective
      (baseField := baseField) (extensionField := extensionField) moduleSheaf))

/-- A nontrivial combination of two independent sections stays nonzero after extension. -/
theorem pulled_pencil_ne_zero {baseField extensionField : Type u}
    [Field baseField] [Field extensionField] [Algebra baseField extensionField]
    {source : Scheme.{u}} [source.Over (Spec (.of baseField))]
    [QuasiCompact (source ↘ Spec (.of baseField))]
    [QuasiSeparated (source ↘ Spec (.of baseField))]
    (moduleSheaf : source.Modules) [moduleSheaf.IsQuasicoherent]
    (firstClass secondClass : moduleSheaf.H 0)
    (independent : LinearIndependent baseField ![firstClass, secondClass])
    (firstScalar secondScalar : extensionField)
    (nonzero : firstScalar ≠ 0 ∨ secondScalar ≠ 0) :
    let projection := Limits.pullback.fst (source ↘ Spec (.of baseField))
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))
    let pulledModule := (Scheme.Modules.pullback projection).obj moduleSheaf
    globalSectionsRingHom extensionField
        (X := Limits.pullback (source ↘ Spec (.of baseField))
          (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))) firstScalar •
        pulledModule.presheaf.map (homOfLE (by simp : ⊤ ≤ projection ⁻¹ᵁ ⊤)).op
          (pullbackSection projection (H.zeroLinearEquiv moduleSheaf firstClass)) +
      globalSectionsRingHom extensionField
          (X := Limits.pullback (source ↘ Spec (.of baseField))
            (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))) secondScalar •
        pulledModule.presheaf.map (homOfLE (by simp : ⊤ ≤ projection ⁻¹ᵁ ⊤)).op
          (pullbackSection projection (H.zeroLinearEquiv moduleSheaf secondClass)) ≠ 0 := by
  let pulledSource := Limits.pullback (source ↘ Spec (.of baseField))
    (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))
  let projection : pulledSource ⟶ source := Limits.pullback.fst
    (source ↘ Spec (.of baseField))
    (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))
  let pulledModule := (Scheme.Modules.pullback projection).obj moduleSheaf
  let firstImage := H.baseChange (baseField := baseField) extensionField moduleSheaf 0
    (1 ⊗ₜ[baseField] firstClass)
  let secondImage := H.baseChange (baseField := baseField) extensionField moduleSheaf 0
    (1 ⊗ₜ[baseField] secondClass)
  have imageIndependent : LinearIndependent extensionField ![firstImage, secondImage] := by
    convert linearIndependent_baseChange (baseField := baseField)
      (extensionField := extensionField) moduleSheaf ![firstClass, secondClass] independent using 1
    ext index
    fin_cases index <;> rfl
  dsimp only
  intro zeroSections
  have scalarFormula (scalar : extensionField) (element : pulledModule.H 0) :
      H.zeroLinearEquiv pulledModule (scalar • element) =
        globalSectionsRingHom extensionField (X := pulledSource) scalar •
          H.zeroLinearEquiv pulledModule element := by
    change H.zeroLinearEquiv pulledModule
        (globalSectionsRingHom extensionField (X := pulledSource) scalar • element) = _
    exact (H.zeroLinearEquiv pulledModule).map_smul _ _
  have imageFormula (element : moduleSheaf.H 0) :
      H.zeroLinearEquiv pulledModule
          (H.baseChange (baseField := baseField) extensionField moduleSheaf 0
            (1 ⊗ₜ[baseField] element)) =
        pulledModule.presheaf.map (homOfLE (by simp : ⊤ ≤ projection ⁻¹ᵁ ⊤)).op
          (pullbackSection projection (H.zeroLinearEquiv moduleSheaf element)) := by
    simpa only [map_one, one_smul] using H.baseChange_tmul_zeroLinearEquiv
      (baseField := baseField) (extensionField := extensionField)
      moduleSheaf (1 : extensionField) element
  have zeroClasses : firstScalar • firstImage + secondScalar • secondImage = 0 := by
    apply (H.zeroLinearEquiv pulledModule).injective
    rw [map_add, scalarFormula firstScalar firstImage,
      scalarFormula secondScalar secondImage, map_zero]
    dsimp only [firstImage, secondImage]
    rw [imageFormula firstClass, imageFormula secondClass]
    exact zeroSections
  obtain ⟨firstZero, secondZero⟩ := imageIndependent.eq_zero_of_pair zeroClasses
  rcases nonzero with firstNonzero | secondNonzero
  · exact firstNonzero firstZero
  · exact secondNonzero secondZero

end AlgebraicGeometry.SectionPencil
