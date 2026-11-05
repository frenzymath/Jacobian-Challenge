import Jacobian.AlgebraicGeometry.Modules.BaseChange
import Jacobian.AlgebraicGeometry.Scheme.Opens
import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Pullback
import Jacobian.Topology.Sheaves.CechCriterion
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Čech base change over an affine open

For a cartesian square whose base map factors through an affine open, finite Čech
cochains commute with scalar extension when the intersections are affine and the
coefficient sheaf is trivial on them. The comparison uses the canonical pullback
of sections. We also identify sections on the union with Čech zero-cocycles.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe schemeUniverse

open CategoryTheory Limits TensorProduct Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {sourceScheme pulledScheme baseScheme extensionScheme : Scheme.{schemeUniverse}} {pullbackMap : pulledScheme ⟶ sourceScheme} {pulledProjection : pulledScheme ⟶ extensionScheme} {projection : sourceScheme ⟶ baseScheme} {baseMap : extensionScheme ⟶ baseScheme}


/-- In a cartesian square, an affine open lying over an affine open of the base
has affine preimage under an affine base change. -/
lemma isAffineOpen_preimage_of_isPullback (square : IsPullback pullbackMap pulledProjection projection baseMap) {baseOpen : baseScheme.Opens}
    (hV : IsAffineOpen baseOpen) [IsAffine extensionScheme] (hfV : ⊤ ≤ baseMap ⁻¹ᵁ baseOpen) {sourceOpen : sourceScheme.Opens} (hWV : sourceOpen ≤ projection ⁻¹ᵁ baseOpen)
    (hW : IsAffineOpen sourceOpen) : IsAffineOpen (pullbackMap ⁻¹ᵁ sourceOpen) := by
  have hUY : pullbackMap ⁻¹ᵁ sourceOpen = pullbackMap ⁻¹ᵁ sourceOpen ⊓ pulledProjection ⁻¹ᵁ ⊤ := by simp
  have : IsAffine baseOpen.toScheme := hV
  have : IsAffine (⊤ : extensionScheme.Opens).toScheme := isAffineOpen_top extensionScheme
  have : IsAffine sourceOpen.toScheme := hW
  exact .of_isIso (Scheme.Hom.isPullback_resLE square hfV hWV hUY).isoPullback.hom

section Sections

variable (commutativity : pullbackMap ≫ projection = pulledProjection ≫ baseMap) {baseOpen : baseScheme.Opens} (hfV : ⊤ ≤ baseMap ⁻¹ᵁ baseOpen) (moduleSheaf : sourceScheme.Modules)
  {sourceOpen : sourceScheme.Opens} (hWV : sourceOpen ≤ projection ⁻¹ᵁ baseOpen)
  [Algebra Γ(baseScheme, baseOpen) Γ(extensionScheme, ⊤)] (hf : algebraMap Γ(baseScheme, baseOpen) Γ(extensionScheme, ⊤) = (baseMap.appLE baseOpen ⊤ hfV).hom)
  [Module Γ(baseScheme, baseOpen) Γ(moduleSheaf, sourceOpen)] (hW : ∀ (scalar : Γ(baseScheme, baseOpen)) (sectionValue : Γ(moduleSheaf, sourceOpen)), scalar • sectionValue = projection.appLE baseOpen sourceOpen hWV scalar • sectionValue)

omit [Algebra Γ(baseScheme, baseOpen) Γ(extensionScheme, ⊤)] in
include commutativity in
lemma appLE_comp_eq_app_appLE (scalar : Γ(baseScheme, baseOpen)) :
    pulledProjection.appLE ⊤ (pullbackMap ⁻¹ᵁ sourceOpen) (le_top.trans pulledProjection.preimage_top.ge) (baseMap.appLE baseOpen ⊤ hfV scalar) =
      pullbackMap.app sourceOpen (projection.appLE baseOpen sourceOpen hWV scalar) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  congr 1
  simp only [commutativity]

include commutativity hf hW in
/-- **Base change of sections.** The map `B ⊗[A] Γ(moduleSheaf, sourceOpen) ⟶ Γ(pullbackMap^* moduleSheaf, pullbackMap⁻¹ sourceOpen)`,
`extensionScalar ⊗ sectionValue ↦ pulledProjection^♯ extensionScalar • pullbackMap^* sectionValue`, for `A = Γ(baseScheme, baseOpen)` and `B = Γ(extensionScheme, ⊤)`. -/
noncomputable def sectionsBaseChange :
    Γ(extensionScheme, ⊤) ⊗[Γ(baseScheme, baseOpen)] Γ(moduleSheaf, sourceOpen) →+ Γ((pullback pullbackMap).obj moduleSheaf, pullbackMap ⁻¹ᵁ sourceOpen) :=
  TensorProduct.liftAddHom
    { toFun extensionScalar :=
        { toFun sectionValue := pulledProjection.appLE ⊤ (pullbackMap ⁻¹ᵁ sourceOpen) (le_top.trans pulledProjection.preimage_top.ge) extensionScalar • pullbackSection pullbackMap sectionValue
          map_zero' := by simp only [pullbackSection, map_zero, smul_zero]
          map_add' sectionValue otherSectionValue := by rw [pullbackSection_add, smul_add] }
      map_zero' := by ext sectionValue; simp
      map_add' extensionScalar otherScalar := by ext sectionValue; simp [add_smul] }
    (fun scalar extensionScalar sectionValue ↦ by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [hW, pullbackSection_smul, smul_smul, Algebra.smul_def, hf, map_mul,
        appLE_comp_eq_app_appLE commutativity hfV hWV, mul_comm])

lemma sectionsBaseChange_tmul (extensionScalar : Γ(extensionScheme, ⊤)) (sectionValue : Γ(moduleSheaf, sourceOpen)) :
    sectionsBaseChange commutativity hfV moduleSheaf hWV hf hW (extensionScalar ⊗ₜ sectionValue) =
      pulledProjection.appLE ⊤ (pullbackMap ⁻¹ᵁ sourceOpen) (le_top.trans pulledProjection.preimage_top.ge) extensionScalar • pullbackSection pullbackMap sectionValue :=
  rfl


/-- **Base change of sections over an affine open with scalar free generator.** If `extensionScheme` and `baseOpen` are
affine and `moduleSheaf` has scalar free generator `generator` on the affine open `sourceOpen ⊆ projection⁻¹ baseOpen`, the map
`B ⊗[A] Γ(moduleSheaf, sourceOpen) ⟶ Γ(pullbackMap^* moduleSheaf, pullbackMap⁻¹ sourceOpen)` is bijective: through `generator` and its pullback `pullbackMap^* generator`, which is scalar
free generator of `pullbackMap^* moduleSheaf` on `pullbackMap⁻¹ sourceOpen`, it is the identification of `B ⊗[A] Γ(sourceScheme, sourceOpen)` with the ring
of functions `Γ(pulledScheme, pullbackMap⁻¹ sourceOpen)` of the affine `pullbackMap⁻¹ sourceOpen = sourceOpen ×_S extensionScheme`. -/
theorem sectionsBaseChange_bijective (square : IsPullback pullbackMap pulledProjection projection baseMap) (hV : IsAffineOpen baseOpen)
    [IsAffine extensionScheme] (hWa : IsAffineOpen sourceOpen) {generator : Γ(moduleSheaf, sourceOpen)} (he : IsFreeGenerator generator) :
    Function.Bijective (sectionsBaseChange square.w hfV moduleSheaf hWV hf hW) := by
  let : Algebra Γ(baseScheme, baseOpen) Γ(sourceScheme, sourceOpen) := (projection.appLE baseOpen sourceOpen hWV).hom.toAlgebra
  let trivialization : Γ(sourceScheme, sourceOpen) →ₗ[Γ(baseScheme, baseOpen)] Γ(moduleSheaf, sourceOpen) :=
    { toFun functionValue := functionValue • generator
      map_add' functionValue otherFunction := add_smul functionValue otherFunction generator
      map_smul' scalar functionValue := by
        rw [RingHom.id_apply, hW, Algebra.smul_def, mul_smul]
        rfl }
  have hψ : Function.Bijective trivialization := he.bijective
  have hUY : pullbackMap ⁻¹ᵁ sourceOpen = pullbackMap ⁻¹ᵁ sourceOpen ⊓ pulledProjection ⁻¹ᵁ ⊤ := by simp
  have hpush := (isIso_pushoutSection_iff square hfV hWV hUY).mp
    (isIso_pushoutSection_of_isAffineOpen square hfV hWV hUY hV (isAffineOpen_top extensionScheme) hWa)
  have hα : CommRingCat.ofHom (algebraMap Γ(baseScheme, baseOpen) Γ(extensionScheme, ⊤)) = baseMap.appLE baseOpen ⊤ hfV := by
    rw [hf]
    rfl
  let ringComparison := hpush.tensorEquiv hα rfl
  have he' : IsFreeGenerator (pullbackSection pullbackMap generator) := IsFreeGenerator.pullbackSection pullbackMap he
  have key : ⇑(sectionsBaseChange square.w hfV moduleSheaf hWV hf hW) ∘ ⇑(trivialization.lTensor Γ(extensionScheme, ⊤)) =
      (fun sectionValue : Γ(pulledScheme, pullbackMap ⁻¹ᵁ sourceOpen) ↦ sectionValue • pullbackSection pullbackMap generator) ∘ ⇑ringComparison := by
    funext element
    induction element using TensorProduct.induction_on with
    | zero => simp
    | tmul extensionScalar functionValue =>
      simp only [Function.comp_apply, LinearMap.lTensor_tmul, sectionsBaseChange_tmul]
      rw [CategoryTheory.IsPushout.tensorEquiv_tmul]
      change _ • pullbackSection pullbackMap (functionValue • generator) = _
      rw [pullbackSection_smul, smul_smul, Scheme.Hom.app_eq_appLE]
    | add element otherElement hz hz' =>
      simp only [Function.comp_apply, map_add, add_smul] at hz hz' ⊢
      rw [hz, hz']
  have hlt : Function.Bijective (trivialization.lTensor Γ(extensionScheme, ⊤)) :=
    (LinearEquiv.lTensor Γ(extensionScheme, ⊤) (LinearEquiv.ofBijective trivialization hψ)).bijective
  refine (Function.Bijective.of_comp_iff _ hlt).mp ?_
  rw [key]
  exact he'.bijective.comp ringComparison.bijective

end Sections

section Cech

open TopCat.Presheaf

variable {baseOpen : baseScheme.Opens} (hfV : ⊤ ≤ baseMap ⁻¹ᵁ baseOpen) (moduleSheaf : sourceScheme.Modules) {coverIndex : Type schemeUniverse} (cover : coverIndex → sourceScheme.Opens)
  (hUV : ∀ faceIndex, cover faceIndex ≤ projection ⁻¹ᵁ baseOpen)

include hUV in
lemma iInf_le_preimage_of_forall_le {degree : ℕ} (simplex : Fin (degree + 1) → coverIndex) :
    ⨅ position, cover (simplex position) ≤ projection ⁻¹ᵁ baseOpen :=
  (iInf_le _ 0).trans (hUV _)

variable (pullbackMap) in
lemma iInf_preimage_eq_preimage_iInf {degree : ℕ} (simplex : Fin (degree + 1) → coverIndex) :
    ⨅ position, pullbackMap ⁻¹ᵁ cover (simplex position) = pullbackMap ⁻¹ᵁ ⨅ position, cover (simplex position) :=
  (pullbackMap.preimage_iInf _).symm

variable [Algebra Γ(baseScheme, baseOpen) Γ(extensionScheme, ⊤)] (hf : algebraMap Γ(baseScheme, baseOpen) Γ(extensionScheme, ⊤) = (baseMap.appLE baseOpen ⊤ hfV).hom)
  [∀ (degree : ℕ) (simplex : Fin (degree + 1) → coverIndex), Module Γ(baseScheme, baseOpen) Γ(moduleSheaf, ⨅ position, cover (simplex position))]
  (hU : ∀ (degree : ℕ) (simplex : Fin (degree + 1) → coverIndex) (scalar : Γ(baseScheme, baseOpen)) (sectionValue : Γ(moduleSheaf, ⨅ position, cover (simplex position))),
    scalar • sectionValue = projection.appLE baseOpen _ (iInf_le_preimage_of_forall_le cover hUV simplex) scalar • sectionValue)

include hU in
/-- The Čech differential `Č^degree(cover, moduleSheaf) ⟶ Č^{degree+1}(cover, moduleSheaf)` is `Γ(baseScheme, baseOpen)`-linear. -/
lemma cechComplex_d_smul (degree : ℕ) (scalar : Γ(baseScheme, baseOpen)) (cochain : CechCochain cover moduleSheaf.presheaf degree) :
    ((cechComplex cover).obj moduleSheaf.presheaf).d degree (degree + 1) (scalar • cochain : CechCochain cover moduleSheaf.presheaf degree) =
      scalar • (show CechCochain cover moduleSheaf.presheaf (degree + 1) from
        ((cechComplex cover).obj moduleSheaf.presheaf).d degree (degree + 1) cochain) := by
  funext simplex
  rw [cechComplex_d_apply, Pi.smul_apply, cechComplex_d_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun faceIndex _ ↦ ?_
  rw [smul_comm, Pi.smul_apply, hU, hU, Scheme.Modules.map_smul]
  congr 2
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-- The Čech differential `Č^degree(cover, moduleSheaf) ⟶ Č^{degree+1}(cover, moduleSheaf)` as scalar `Γ(baseScheme, baseOpen)`-linear map. -/
noncomputable def cechDifferential (degree : ℕ) :
    CechCochain cover moduleSheaf.presheaf degree →ₗ[Γ(baseScheme, baseOpen)] CechCochain cover moduleSheaf.presheaf (degree + 1) where
  toFun := ((cechComplex cover).obj moduleSheaf.presheaf).d degree (degree + 1)
  map_add' := map_add _
  map_smul' scalar cochain := cechComplex_d_smul moduleSheaf cover hUV hU degree scalar cochain

lemma cechDifferential_apply (degree : ℕ) (cochain : CechCochain cover moduleSheaf.presheaf degree) :
    cechDifferential moduleSheaf cover hUV hU degree cochain = ((cechComplex cover).obj moduleSheaf.presheaf).d degree (degree + 1) cochain :=
  rfl

lemma cechDifferential_comp (degree : ℕ) :
    cechDifferential moduleSheaf cover hUV hU (degree + 1) ∘ₗ cechDifferential moduleSheaf cover hUV hU degree = 0 := by
  refine LinearMap.ext fun cochain ↦ ?_
  exact congr($(((cechComplex cover).obj moduleSheaf.presheaf).d_comp_d degree (degree + 1) (degree + 2)) cochain)

variable (commutativity : pullbackMap ≫ projection = pulledProjection ≫ baseMap) [Fintype coverIndex] [DecidableEq coverIndex]

include commutativity hf hU in
/-- **Base change of Čech cochains.** The map `B ⊗[A] Č^degree(cover, moduleSheaf) ⟶ Č^degree(pullbackMap⁻¹ cover, pullbackMap^* moduleSheaf)`,
`extensionScalar ⊗ cochain ↦ (simplex ↦ pulledProjection^♯ extensionScalar • pullbackMap^* (cochain simplex))`. -/
noncomputable def cechBaseChange (degree : ℕ) :
    Γ(extensionScheme, ⊤) ⊗[Γ(baseScheme, baseOpen)] CechCochain cover moduleSheaf.presheaf degree →+
      CechCochain (fun faceIndex ↦ pullbackMap ⁻¹ᵁ cover faceIndex) ((pullback pullbackMap).obj moduleSheaf).presheaf degree :=
  AddMonoidHom.pi fun simplex ↦
    (((pullback pullbackMap).obj moduleSheaf).presheaf.map
      (eqToHom (iInf_preimage_eq_preimage_iInf pullbackMap cover simplex)).op).hom.comp
      ((sectionsBaseChange commutativity hfV moduleSheaf (iInf_le_preimage_of_forall_le cover hUV simplex) hf (hU degree simplex)).comp
        ((Pi.evalAddMonoidHom _ simplex).comp (TensorProduct.piRight Γ(baseScheme, baseOpen) Γ(baseScheme, baseOpen) Γ(extensionScheme, ⊤)
          (fun simplex : Fin (degree + 1) → coverIndex ↦ Γ(moduleSheaf, ⨅ position, cover (simplex position)))).toLinearMap.toAddMonoidHom))

lemma cechBaseChange_tmul (degree : ℕ) (extensionScalar : Γ(extensionScheme, ⊤)) (cochain : CechCochain cover moduleSheaf.presheaf degree)
    (simplex : Fin (degree + 1) → coverIndex) :
    cechBaseChange hfV moduleSheaf cover hUV hf hU commutativity degree (extensionScalar ⊗ₜ cochain) simplex =
      ((pullback pullbackMap).obj moduleSheaf).presheaf.map (eqToHom (iInf_preimage_eq_preimage_iInf pullbackMap cover simplex)).op
        (pulledProjection.appLE ⊤ (pullbackMap ⁻¹ᵁ ⨅ position, cover (simplex position)) (le_top.trans pulledProjection.preimage_top.ge) extensionScalar •
          pullbackSection pullbackMap (cochain simplex)) := by
  simp [cechBaseChange, TensorProduct.piRight_apply, sectionsBaseChange_tmul]


omit [Fintype coverIndex] [DecidableEq coverIndex] in
/-- Restriction commutes with multiplication by the image of scalar function on `extensionScheme`. -/
lemma presheaf_map_appLE_smul (otherModule : pulledScheme.Modules) {firstOpen secondOpen : pulledScheme.Opens} (inclusion : secondOpen ≤ firstOpen) (extensionScalar : Γ(extensionScheme, ⊤))
    (otherDegree : Γ(otherModule, firstOpen)) :
    otherModule.presheaf.map (homOfLE inclusion).op (pulledProjection.appLE ⊤ firstOpen (le_top.trans pulledProjection.preimage_top.ge) extensionScalar • otherDegree) =
      pulledProjection.appLE ⊤ secondOpen (le_top.trans pulledProjection.preimage_top.ge) extensionScalar • otherModule.presheaf.map (homOfLE inclusion).op otherDegree := by
  rw [Scheme.Modules.map_smul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-- **Base change of Čech cochains is bijective** when all finite intersections of the cover are
affine opens on which `moduleSheaf` has scalar free generator, and `extensionScheme`, `baseOpen` are affine. -/
theorem cechBaseChange_bijective (square : IsPullback pullbackMap pulledProjection projection baseMap) (hV : IsAffineOpen baseOpen) [IsAffine extensionScheme]
    (hUa : ∀ (degree : ℕ) (simplex : Fin (degree + 1) → coverIndex), IsAffineOpen (⨅ position, cover (simplex position)))
    (he : ∀ (degree : ℕ) (simplex : Fin (degree + 1) → coverIndex), ∃ generator : Γ(moduleSheaf, ⨅ position, cover (simplex position)), IsFreeGenerator generator)
    (degree : ℕ) : Function.Bijective (cechBaseChange hfV moduleSheaf cover hUV hf hU square.w degree) := by
  let comparison : ∀ simplex : Fin (degree + 1) → coverIndex, Γ(extensionScheme, ⊤) ⊗[Γ(baseScheme, baseOpen)] Γ(moduleSheaf, ⨅ position, cover (simplex position)) →
      Γ((pullback pullbackMap).obj moduleSheaf, ⨅ position, pullbackMap ⁻¹ᵁ cover (simplex position)) := fun simplex ↦
    (((pullback pullbackMap).obj moduleSheaf).presheaf.map
      (eqToHom (iInf_preimage_eq_preimage_iInf pullbackMap cover simplex)).op).hom ∘
      sectionsBaseChange square.w hfV moduleSheaf (iInf_le_preimage_of_forall_le cover hUV simplex) hf (hU degree simplex)
  have hφ (simplex : Fin (degree + 1) → coverIndex) : Function.Bijective (comparison simplex) := by
    obtain ⟨generator, he⟩ := he degree simplex
    refine (ConcreteCategory.bijective_of_isIso _).comp ?_
    exact sectionsBaseChange_bijective hfV moduleSheaf _ hf (hU degree simplex) square hV (hUa degree simplex) he
  have key : ⇑(cechBaseChange hfV moduleSheaf cover hUV hf hU square.w degree) =
      (fun element simplex ↦ comparison simplex (element simplex)) ∘ ⇑(TensorProduct.piRight Γ(baseScheme, baseOpen) Γ(baseScheme, baseOpen) Γ(extensionScheme, ⊤)
        (fun simplex : Fin (degree + 1) → coverIndex ↦ Γ(moduleSheaf, ⨅ position, cover (simplex position)))) := rfl
  rw [key]
  refine Function.Bijective.comp ?_ (LinearEquiv.bijective _)
  refine ⟨fun element otherElement hzz' ↦ funext fun simplex ↦ (hφ simplex).1 (congr_fun hzz' simplex), fun cochain ↦ ?_⟩
  choose element hz using fun simplex ↦ (hφ simplex).2 (cochain simplex)
  exact ⟨element, funext hz⟩


omit [Fintype coverIndex] [DecidableEq coverIndex] in
lemma presheaf_map_eqToHom_eq_homOfLE (otherModule : pulledScheme.Modules) {firstOpen secondOpen : pulledScheme.Opens} (inclusion : secondOpen = firstOpen)
    (otherDegree : Γ(otherModule, firstOpen)) : otherModule.presheaf.map (eqToHom inclusion).op otherDegree = otherModule.presheaf.map (homOfLE inclusion.le).op otherDegree :=
  rfl

/-- **Base change of Čech cochains commutes with the differentials.** -/
theorem cechBaseChange_d (degree : ℕ) (element : Γ(extensionScheme, ⊤) ⊗[Γ(baseScheme, baseOpen)] CechCochain cover moduleSheaf.presheaf degree) :
    cechBaseChange hfV moduleSheaf cover hUV hf hU commutativity (degree + 1)
        ((cechDifferential moduleSheaf cover hUV hU degree).lTensor Γ(extensionScheme, ⊤) element) =
      ((cechComplex (fun faceIndex ↦ pullbackMap ⁻¹ᵁ cover faceIndex)).obj ((pullback pullbackMap).obj moduleSheaf).presheaf).d degree (degree + 1)
        (cechBaseChange hfV moduleSheaf cover hUV hf hU commutativity degree element) := by
  induction element using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add element otherElement hz hz' => simp only [map_add, hz, hz']
  | tmul extensionScalar cochain =>
    funext simplex
    rw [LinearMap.lTensor_tmul, cechBaseChange_tmul, cechDifferential_apply,
      cechComplex_d_apply, cechComplex_d_apply]
    simp only [pullbackSection, map_sum, map_zsmul, Finset.smul_sum, smul_comm _ ((-1 : ℤ) ^ _)]
    refine Finset.sum_congr rfl fun faceIndex _ ↦ ?_
    congr 1
    rw [cechBaseChange_tmul]
    change ((pullback pullbackMap).obj moduleSheaf).presheaf.map _ (_ • pullbackSection pullbackMap
      (moduleSheaf.presheaf.map (homOfLE _).op _)) = ((pullback pullbackMap).obj moduleSheaf).presheaf.map _
        (((pullback pullbackMap).obj moduleSheaf).presheaf.map _ (_ • pullbackSection pullbackMap _))
    rw [pullbackSection_map, presheaf_map_eqToHom_eq_homOfLE, presheaf_map_eqToHom_eq_homOfLE,
      presheaf_map_appLE_smul, presheaf_map_appLE_smul, presheaf_map_appLE_smul,
      TopCat.Presheaf.map_homOfLE_map_homOfLE_apply, TopCat.Presheaf.map_homOfLE_map_homOfLE_apply]


omit [Fintype coverIndex] [DecidableEq coverIndex] in
include hf in
/-- **Exactness of the base-changed Čech complex.** If the Čech complex of `pullbackMap^* moduleSheaf` for the cover
`pullbackMap⁻¹ cover` is exact in degree `1`, then so is `B ⊗[A] Č(cover, moduleSheaf)`. -/
theorem exact_lTensor_cechDifferential [Finite coverIndex] (square : IsPullback pullbackMap pulledProjection projection baseMap)
    (hV : IsAffineOpen baseOpen) [IsAffine extensionScheme]
    (hUa : ∀ (degree : ℕ) (simplex : Fin (degree + 1) → coverIndex), IsAffineOpen (⨅ position, cover (simplex position)))
    (he : ∀ (degree : ℕ) (simplex : Fin (degree + 1) → coverIndex), ∃ generator : Γ(moduleSheaf, ⨅ position, cover (simplex position)), IsFreeGenerator generator)
    (hex : ((cechComplex (fun faceIndex ↦ pullbackMap ⁻¹ᵁ cover faceIndex)).obj ((pullback pullbackMap).obj moduleSheaf).presheaf).ExactAt 1) :
    Function.Exact ((cechDifferential moduleSheaf cover hUV hU 0).lTensor Γ(extensionScheme, ⊤))
      ((cechDifferential moduleSheaf cover hUV hU 1).lTensor Γ(extensionScheme, ⊤)) := by
  classical
  have := Fintype.ofFinite coverIndex
  rw [exactAt_cechComplex_iff] at hex
  have hb (degree : ℕ) := cechBaseChange_bijective hfV moduleSheaf cover hUV hf hU square hV hUa he degree
  intro element
  constructor
  · intro hz
    have h1 := cechBaseChange_d hfV moduleSheaf cover hUV hf hU square.w 1 element
    rw [hz, map_zero] at h1
    obtain ⟨cochain, hc⟩ := hex _ h1.symm
    obtain ⟨primitive, rfl⟩ := (hb 0).2 cochain
    refine ⟨primitive, (hb 1).1 ?_⟩
    rw [cechBaseChange_d]
    exact hc
  · rintro ⟨primitive, rfl⟩
    refine (hb 2).1 ?_
    rw [cechBaseChange_d, cechBaseChange_d, map_zero]
    exact congr($(((cechComplex (fun faceIndex ↦ pullbackMap ⁻¹ᵁ cover faceIndex)).obj
      ((pullback pullbackMap).obj moduleSheaf).presheaf).d_comp_d 0 1 2) _)

end Cech

section Sheaf

open TopCat.Presheaf

variable (moduleSheaf : sourceScheme.Modules) {coverIndex : Type schemeUniverse} (cover : coverIndex → sourceScheme.Opens) {unionOpen : sourceScheme.Opens} (hU : ⨆ faceIndex, cover faceIndex = unionOpen)

include hU in
lemma iInf_le_of_iSup_eq (element : Fin 1 → coverIndex) : ⨅ position, cover (element position) ≤ unionOpen :=
  (iInf_le _ 0).trans (hU ▸ le_iSup cover (element 0))

include hU in
/-- The Čech `0`-cochains of scalar section are determined by the section: two sections over the
union of scalar cover with the same restrictions to its members agree. -/
lemma eq_of_forall_presheaf_map_eq (sectionValue otherSection : Γ(moduleSheaf, unionOpen))
    (inclusion : ∀ element : Fin 1 → coverIndex, moduleSheaf.presheaf.map (homOfLE (iInf_le_of_iSup_eq cover hU element)).op sectionValue =
      moduleSheaf.presheaf.map (homOfLE (iInf_le_of_iSup_eq cover hU element)).op otherSection) : sectionValue = otherSection :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨moduleSheaf.presheaf, moduleSheaf.isSheaf⟩ (fun element : Fin 1 → coverIndex ↦ ⨅ position, cover (element position)) unionOpen
    (fun element ↦ homOfLE (iInf_le_of_iSup_eq cover hU element))
    (fun sectionValue hx ↦ by
      rw [← hU] at hx
      obtain ⟨faceIndex, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨fun _ ↦ faceIndex, by simpa using hi⟩) sectionValue otherSection inclusion

include hU in
/-- **Čech `0`-cocycles glue.** A Čech `0`-cocycle of scalar cover of `unionOpen` is the family of
restrictions of scalar section over `unionOpen`. -/
lemma exists_presheaf_map_eq_of_cechComplex_d_eq_zero (cochain : CechCochain cover moduleSheaf.presheaf 0)
    (hc : ((cechComplex cover).obj moduleSheaf.presheaf).d 0 1 cochain = 0) :
    ∃ sectionValue : Γ(moduleSheaf, unionOpen), ∀ element : Fin 1 → coverIndex,
      moduleSheaf.presheaf.map (homOfLE (iInf_le_of_iSup_eq cover hU element)).op sectionValue = cochain element := by
  obtain ⟨sectionValue, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨moduleSheaf.presheaf, moduleSheaf.isSheaf⟩
    (fun element : Fin 1 → coverIndex ↦ ⨅ position, cover (element position)) unionOpen (fun element ↦ homOfLE (iInf_le_of_iSup_eq cover hU element))
    (fun sectionValue hx ↦ by
      rw [← hU] at hx
      obtain ⟨faceIndex, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨fun _ ↦ faceIndex, by simpa using hi⟩) cochain
    (fun element otherElement ↦ map_inf_eq_of_cechComplex_d_zero cover moduleSheaf.presheaf cochain hc element otherElement)
  exact ⟨sectionValue, hs⟩

end Sheaf

end AlgebraicGeometry.Scheme.Modules
