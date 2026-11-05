import Jacobian.AlgebraicGeometry.Modules.PullbackTilde

/-!
# Sections of a quasi-coherent pullback on affine opens
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe schemeUniverse
open CategoryTheory Opposite TensorProduct Limits TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
variable {scheme source thirdScheme : Scheme.{schemeUniverse}}

/-- The units of the pullback along two equal morphisms agree, up to `pullbackCongr`. -/
lemma pullbackCongr_hom_app_pullbackSection {morphism secondMorphism : scheme ⟶ source} (compatibility : morphism = secondMorphism) {moduleSheaf : source.Modules}
    {openSubset : source.Opens} (sectionValue : Γ(moduleSheaf, openSubset)) :
    ((pullbackCongr compatibility).hom.app moduleSheaf).app (morphism ⁻¹ᵁ openSubset) (pullbackSection morphism sectionValue) =
      ((pullback secondMorphism).obj moduleSheaf).presheaf.map (eqToHom (by rw [compatibility])).op (pullbackSection secondMorphism sectionValue) := by
  subst compatibility
  simp [pullbackCongr]

/-- The pullback along a composite `g ≫ f` of a section is the pullback along `g` of its pullback
along `f`, up to `pullbackComp`. -/
lemma pullbackComp_inv_app_pullbackSection (secondMorphism : thirdScheme ⟶ source) (morphism : source ⟶ scheme) {moduleSheaf : scheme.Modules}
    {openSubset : scheme.Opens} (sectionValue : Γ(moduleSheaf, openSubset)) :
    ((pullbackComp secondMorphism morphism).inv.app moduleSheaf).app ((secondMorphism ≫ morphism) ⁻¹ᵁ openSubset) (pullbackSection (secondMorphism ≫ morphism) sectionValue) =
      pullbackSection secondMorphism (pullbackSection morphism sectionValue) :=
  pullbackUnit_comp_app_apply secondMorphism morphism moduleSheaf openSubset sectionValue

/-- The pullback along an affine open immersion `Spec Γ(X, U) ⟶ X` of sections over `U`,
followed by the identification `fromSpec ⁻¹ᵁ U = ⊤`, is bijective. -/
lemma bijective_pullbackSection_fromSpec (moduleSheaf : scheme.Modules) {openSubset : scheme.Opens} (hU : IsAffineOpen openSubset) :
    Function.Bijective (fun sectionValue : Γ(moduleSheaf, openSubset) ↦ ((pullback hU.fromSpec).obj moduleSheaf).presheaf.map
      (eqToHom hU.fromSpec_preimage_self.symm).op (pullbackSection hU.fromSpec sectionValue)) :=
  (ConcreteCategory.bijective_of_isIso (((pullback hU.fromSpec).obj moduleSheaf).presheaf.map
    (eqToHom hU.fromSpec_preimage_self.symm).op)).comp
    (bijective_pullbackUnit_app_of_isOpenImmersion hU.fromSpec moduleSheaf hU.opensRange_fromSpec.ge)

/-- The pullback along `fromSpec` of sections over `U`, as a linear equivalence
`Γ(M, U) ≃ Γ(fromSpec^* M, ⊤)` over `Γ(X, U)`. -/
noncomputable def pullbackSectionFromSpecEquiv (moduleSheaf : scheme.Modules) {openSubset : scheme.Opens}
    (hU : IsAffineOpen openSubset) : Γ(moduleSheaf, openSubset) ≃ₗ[Γ(scheme, openSubset)] Γ((pullback hU.fromSpec).obj moduleSheaf, ⊤) :=
  LinearEquiv.ofBijective
    { toFun sectionValue := ((pullback hU.fromSpec).obj moduleSheaf).presheaf.map
        (eqToHom hU.fromSpec_preimage_self.symm).op (pullbackSection hU.fromSpec sectionValue)
      map_add' sectionValue sectionValue' := by simp [pullbackSection_add]
      map_smul' scalar sectionValue := by
        rw [pullbackSection_smul, map_smul, RingHom.id_apply, hU.fromSpec_app_self,
          smul_Spec_def]
        rfl }
    (bijective_pullbackSection_fromSpec moduleSheaf hU)

lemma pullbackSectionFromSpecEquiv_apply (moduleSheaf : scheme.Modules) {openSubset : scheme.Opens} (hU : IsAffineOpen openSubset)
    (sectionValue : Γ(moduleSheaf, openSubset)) :
    pullbackSectionFromSpecEquiv moduleSheaf hU sectionValue = ((pullback hU.fromSpec).obj moduleSheaf).presheaf.map
        (eqToHom hU.fromSpec_preimage_self.symm).op (pullbackSection hU.fromSpec sectionValue) :=
  rfl

/-- Pullback of sections commutes with restriction along any inclusion of opens. -/
lemma pullbackSection_presheaf_map (secondMorphism : scheme ⟶ source) {moduleSheaf : source.Modules} {openSubset smallerOpen : source.Opens} (inclusion : smallerOpen ⟶ openSubset)
    (sectionValue : Γ(moduleSheaf, openSubset)) :
    pullbackSection secondMorphism (moduleSheaf.presheaf.map inclusion.op sectionValue) =
      ((pullback secondMorphism).obj moduleSheaf).presheaf.map (homOfLE (secondMorphism.preimage_mono inclusion.le)).op
        (pullbackSection secondMorphism sectionValue) := by
  rw [show inclusion = homOfLE inclusion.le from Subsingleton.elim _ _]
  exact pullbackSection_map secondMorphism inclusion.le sectionValue

/-- Two restrictions of the same section to the same open agree. -/
lemma presheaf_map_apply_congr (moduleSheaf : scheme.Modules) {openSubset smallerOpen : scheme.Opens} (inclusion openImmersion : smallerOpen ⟶ openSubset) (sectionValue : Γ(moduleSheaf, openSubset)) :
    moduleSheaf.presheaf.map inclusion.op sectionValue = moduleSheaf.presheaf.map openImmersion.op sectionValue := by
  rw [Subsingleton.elim inclusion openImmersion]

/-- Restricting twice is restricting once. -/
lemma presheaf_map_presheaf_map_apply (moduleSheaf : scheme.Modules) {openSubset smallerOpen largerOpen : scheme.Opens} (inclusion : smallerOpen ⟶ openSubset)
    (openImmersion : largerOpen ⟶ smallerOpen) (compositeInclusion : largerOpen ⟶ openSubset) (sectionValue : Γ(moduleSheaf, openSubset)) :
    moduleSheaf.presheaf.map openImmersion.op (moduleSheaf.presheaf.map inclusion.op sectionValue) = moduleSheaf.presheaf.map compositeInclusion.op sectionValue := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim (inclusion.op ≫ openImmersion.op) compositeInclusion.op]

lemma iso_hom_app_inv_app {moduleSheaf targetSheaf : scheme.Modules} (comparison : moduleSheaf ≅ targetSheaf) (openSubset : scheme.Opens) (element : Γ(targetSheaf, openSubset)) :
    Hom.app comparison.hom openSubset (Hom.app comparison.inv openSubset element) = element := by
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, comparison.inv_hom_id, Hom.id_app,
    ConcreteCategory.id_apply]

lemma natIso_hom_app_inv_app {category : Type*} [Category category] {abelianSheaf targetAbelianSheaf : category ⥤ scheme.Modules} (comparison : abelianSheaf ≅ targetAbelianSheaf) (moduleSheaf : category)
    (openSubset : scheme.Opens) (element : Γ(targetAbelianSheaf.obj moduleSheaf, openSubset)) :
    Hom.app (comparison.hom.app moduleSheaf) openSubset (Hom.app (comparison.inv.app moduleSheaf) openSubset element) = element :=
  iso_hom_app_inv_app (comparison.app moduleSheaf) openSubset element

/-- For a commutative square `g ≫ f = g' ≫ f'`, the comparison `g^* f^* M ≅ g'^* f'^* M` sends
the iterated pullback of a section to the iterated pullback. -/
lemma pullbackComp_congr_hom_app_pullbackSection {source' : Scheme.{schemeUniverse}} {secondMorphism : thirdScheme ⟶ source} {morphism : source ⟶ scheme}
    {secondMorphism' : thirdScheme ⟶ source'} {morphism' : source' ⟶ scheme} (compatibility : secondMorphism ≫ morphism = secondMorphism' ≫ morphism') (moduleSheaf : scheme.Modules) {openSubset : scheme.Opens}
    (sectionValue : Γ(moduleSheaf, openSubset)) :
    ((pullbackComp secondMorphism morphism).app moduleSheaf ≪≫ (pullbackCongr compatibility).app moduleSheaf ≪≫
        ((pullbackComp secondMorphism' morphism').app moduleSheaf).symm).hom.app ((secondMorphism ≫ morphism) ⁻¹ᵁ openSubset)
        (pullbackSection secondMorphism (pullbackSection morphism sectionValue)) =
      ((pullback secondMorphism').obj ((pullback morphism').obj moduleSheaf)).presheaf.map (eqToHom (by
        change (secondMorphism ≫ morphism) ⁻¹ᵁ openSubset = (secondMorphism' ≫ morphism') ⁻¹ᵁ openSubset; rw [compatibility])).op
        (pullbackSection secondMorphism' (pullbackSection morphism' sectionValue)) := by
  rw [← pullbackComp_inv_app_pullbackSection, ← pullbackComp_inv_app_pullbackSection]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Hom.comp_app,
    ConcreteCategory.comp_apply]
  rw [natIso_hom_app_inv_app (pullbackComp secondMorphism morphism) moduleSheaf _ (pullbackSection (secondMorphism ≫ morphism) sectionValue),
    pullbackCongr_hom_app_pullbackSection]
  exact Hom.app_presheaf_map _ _ _

/-- A variant of `pullbackComp_congr_hom_app_pullbackSection` stated over `g ⁻¹ᵁ f ⁻¹ᵁ U`. -/
lemma pullbackComp_congr_hom_app_pullbackSection' {source' : Scheme.{schemeUniverse}} {secondMorphism : thirdScheme ⟶ source} {morphism : source ⟶ scheme}
    {secondMorphism' : thirdScheme ⟶ source'} {morphism' : source' ⟶ scheme} (compatibility : secondMorphism ≫ morphism = secondMorphism' ≫ morphism') (moduleSheaf : scheme.Modules) {openSubset : scheme.Opens}
    (sectionValue : Γ(moduleSheaf, openSubset)) :
    ((pullbackComp secondMorphism morphism).app moduleSheaf ≪≫ (pullbackCongr compatibility).app moduleSheaf ≪≫
        ((pullbackComp secondMorphism' morphism').app moduleSheaf).symm).hom.app (secondMorphism ⁻¹ᵁ morphism ⁻¹ᵁ openSubset)
        (pullbackSection secondMorphism (pullbackSection morphism sectionValue)) =
      ((pullback secondMorphism').obj ((pullback morphism').obj moduleSheaf)).presheaf.map (eqToHom (by
        change (secondMorphism ≫ morphism) ⁻¹ᵁ openSubset = (secondMorphism' ≫ morphism') ⁻¹ᵁ openSubset; rw [compatibility])).op
        (pullbackSection secondMorphism' (pullbackSection morphism' sectionValue)) :=
  pullbackComp_congr_hom_app_pullbackSection compatibility moduleSheaf sectionValue

/-- `pullbackΓ` is the pullback of sections followed by the identification `g ⁻¹ᵁ ⊤ = ⊤`. -/
lemma pullbackΓ_eq (secondMorphism : source ⟶ scheme) (moduleSheaf : scheme.Modules) (element : Γ(moduleSheaf, ⊤)) :
    pullbackΓ secondMorphism moduleSheaf element = ((pullback secondMorphism).obj moduleSheaf).presheaf.map (eqToHom secondMorphism.preimage_top.symm).op
      (pullbackSection secondMorphism element) := by
  rw [pullbackΓ_apply, show (eqToHom secondMorphism.preimage_top.symm).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id]
  rfl

/-- A morphism of `𝒪_{Spec R}`-modules, on global sections, as an `R`-linear map. -/
noncomputable def Hom.appTopLinear {baseRing : CommRingCat.{schemeUniverse}} {moduleSheaf targetSheaf : (Spec baseRing).Modules} (ringMap : moduleSheaf ⟶ targetSheaf) :
    Γ(moduleSheaf, ⊤) →ₗ[baseRing] Γ(targetSheaf, ⊤) where
  toFun := ringMap.app ⊤
  map_add' := (ringMap.app ⊤).hom.map_add
  map_smul' scalar element := by rw [smul_Spec_def, smul_Spec_def, Hom.app_smul]; rfl

/-- **Sections of a pullback over an affine open.** Let `f : X ⟶ Y`, `ℱ` a quasi-coherent
`𝒪_Y`-module, `V ⊆ Y` and `U ⊆ X` affine opens with `U ⊆ f⁻¹ V`. Then
`Γ(f^* ℱ, U) ≅ Γ(X, U) ⊗[Γ(Y, V)] Γ(ℱ, V)`, with `1 ⊗ m` corresponding to the restriction of the
pullback of `m`. -/
theorem exists_linearEquiv_pullback_sections (morphism : scheme ⟶ source) (coherentSheaf : source.Modules) [coherentSheaf.IsQuasicoherent]
    {smallerOpen : source.Opens} (hV : IsAffineOpen smallerOpen) {openSubset : scheme.Opens} (hU : IsAffineOpen openSubset)
    (hUV : openSubset ≤ morphism ⁻¹ᵁ smallerOpen) :
    letI := (morphism.appLE smallerOpen openSubset hUV).hom.toAlgebra
    ∃ comparison : Γ(scheme, openSubset) ⊗[Γ(source, smallerOpen)] Γ(coherentSheaf, smallerOpen) ≃ₗ[Γ(scheme, openSubset)] Γ((pullback morphism).obj coherentSheaf, openSubset),
      ∀ sectionValue : Γ(coherentSheaf, smallerOpen), comparison (1 ⊗ₜ sectionValue) =
        ((pullback morphism).obj coherentSheaf).presheaf.map (homOfLE hUV).op (pullbackSection morphism sectionValue) := by
  let := (morphism.appLE smallerOpen openSubset hUV).hom.toAlgebra
  have hsq : Spec.map (morphism.appLE smallerOpen openSubset hUV) ≫ hV.fromSpec = hU.fromSpec ≫ morphism :=
    IsAffineOpen.SpecMap_appLE_fromSpec morphism hV hU hUV
  let pulledSheaf := (pullback hV.fromSpec).obj coherentSheaf
  obtain ⟨e₁, he₁⟩ := exists_linearEquiv_pullback_Spec (baseAlgebra := Γ(source, smallerOpen)) (extensionAlgebra := Γ(scheme, openSubset)) pulledSheaf
  replace he₁ (sectionValue) : e₁ (1 ⊗ₜ sectionValue) = pullbackΓ (Spec.map (morphism.appLE smallerOpen openSubset hUV)) pulledSheaf sectionValue := he₁ sectionValue
  let moduleIso : (pullback (Spec.map (morphism.appLE smallerOpen openSubset hUV))).obj pulledSheaf ≅
      (pullback hU.fromSpec).obj ((pullback morphism).obj coherentSheaf) :=
    (pullbackComp _ _).app coherentSheaf ≪≫ (pullbackCongr hsq).app coherentSheaf ≪≫ ((pullbackComp _ _).app coherentSheaf).symm
  let eE : Γ((pullback (Spec.map (morphism.appLE smallerOpen openSubset hUV))).obj pulledSheaf, ⊤) ≃ₗ[Γ(scheme, openSubset)]
      Γ((pullback hU.fromSpec).obj ((pullback morphism).obj coherentSheaf), ⊤) :=
    { Hom.appTopLinear moduleIso.hom with
      invFun := moduleIso.inv.app ⊤
      left_inv element := congr($(moduleIso.hom_inv_id).app ⊤ element)
      right_inv element := congr($(moduleIso.inv_hom_id).app ⊤ element) }
  refine ⟨((pullbackSectionFromSpecEquiv coherentSheaf hV).baseChange Γ(source, smallerOpen) Γ(scheme, openSubset) _ _).trans
    (e₁.trans (eE.trans (pullbackSectionFromSpecEquiv _ hU).symm)), fun sectionValue ↦ ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, LinearEquiv.trans_apply, he₁,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq, pullbackSectionFromSpecEquiv_apply,
    pullbackSectionFromSpecEquiv_apply, pullbackΓ_eq]
  have hE (element) : eE element = moduleIso.hom.app ⊤ element := rfl
  refine (hE _).trans ?_
  rw [Hom.app_presheaf_map, pullbackSection_presheaf_map, Hom.app_presheaf_map,
    show moduleIso.hom.app _ (pullbackSection _ (pullbackSection _ sectionValue)) = _ from
      pullbackComp_congr_hom_app_pullbackSection' hsq coherentSheaf sectionValue, pullbackSection_presheaf_map]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

end AlgebraicGeometry.Scheme.Modules
