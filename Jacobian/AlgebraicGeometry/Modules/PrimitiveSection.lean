import Jacobian.AlgebraicGeometry.Cohomology.Affine.CechBaseChange
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechExact
import Jacobian.AlgebraicGeometry.Picard.Presheaf
import Jacobian.LinearAlgebra.TensorProduct.Exact
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Primitive sections after arbitrary affine base change

Let a line bundle on a proper flat family have vanishing first higher direct
image after every base change. A section admitting a linear functional with value
one stays nonzero after every nonempty affine base change, without a flatness
assumption on that base change. In particular, every element of a local basis of
the direct image stays nonzero under the canonical pullback of sections.

The proof computes sections by a finite trivializing affine Čech cover. Applying
universal vanishing to square-zero algebras gives tensor exactness for arbitrary
modules, so the zero-cycles embed after arbitrary tensor extension.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse basisUniverse

open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite TopCat.Presheaf
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

private lemma finite_trivializing_affine_cover {coverScheme : Scheme.{schemeUniverse}} (moduleSheaf : coverScheme.Modules)
    [moduleSheaf.IsInvertible] {unionOpen : coverScheme.Opens} (hW : IsCompact (unionOpen : Set coverScheme)) :
    ∃ (coverIndex : Type schemeUniverse) (_ : Finite coverIndex) (cover : coverIndex → coverScheme.Opens), (∀ index, IsAffineOpen (cover index)) ∧
      (∀ index, cover index ≤ unionOpen) ∧ ⨆ index, cover index = unionOpen ∧ ∀ index, ∃ generator : Γ(moduleSheaf, cover index), IsFreeGenerator generator := by
  choose cover hxU hUW he using fun localSection : unionOpen ↦ exists_isFreeGenerator moduleSheaf localSection.2
  obtain ⟨sectionValue, hs⟩ := hW.elim_finite_subcover (fun localSection : unionOpen ↦ ((cover localSection).1 : Set coverScheme))
    (fun localSection ↦ (cover localSection).1.isOpen) (fun localSection hx ↦ Set.mem_iUnion.mpr ⟨⟨localSection, hx⟩, hxU _⟩)
  refine ⟨sectionValue, inferInstance, fun localSection ↦ (cover localSection).1, fun localSection ↦ (cover localSection).2, fun localSection ↦ hUW localSection, ?_,
    fun localSection ↦ he localSection⟩
  refine le_antisymm (iSup_le fun localSection ↦ hUW localSection) fun localSection hx ↦ ?_
  obtain ⟨simplex, hys, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨simplex, hys⟩, hxy⟩

/-- Finite intersections of affine opens lying over an affine open of the target of scalar
separated morphism are affine. -/
private lemma affine_intersections_over_affine {coverScheme parameter : Scheme.{schemeUniverse}} (projection : coverScheme ⟶ parameter) [IsSeparated projection]
    {baseOpen : parameter.Opens} (hV : IsAffineOpen baseOpen) {coverIndex : Type schemeUniverse} (cover : coverIndex → coverScheme.Opens)
    (hU : ∀ index, IsAffineOpen (cover index)) (hUV : ∀ index, cover index ≤ projection ⁻¹ᵁ baseOpen) {degree : ℕ} (simplex : Fin (degree + 1) → coverIndex) :
    IsAffineOpen (⨅ position, cover (simplex position)) := by
  have square := isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal projection)) baseOpen hV
  have key : ∀ (sectionValue : Finset (Fin (degree + 1))), sectionValue.Nonempty →
      IsAffineOpen (⨅ position ∈ sectionValue, cover (simplex position)) ∧ ⨅ position ∈ sectionValue, cover (simplex position) ≤ projection ⁻¹ᵁ baseOpen := by
    intro sectionValue hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton scalar => simpa using ⟨hU (simplex scalar), hUV (simplex scalar)⟩
    | cons scalar sectionValue ha hs ih =>
      rw [Finset.cons_eq_insert, Finset.iInf_insert]
      exact ⟨square _ (hUV _) _ ih.2 (hU _) ih.1, inf_le_left.trans (hUV _)⟩
  simpa using (key Finset.univ Finset.univ_nonempty).1



/-- Functions on an affine open `baseOpen` pulled back along `Spec squareZeroRing ⟶ Spec Γ(parameter, baseOpen) ⟶ parameter` are their
images under `coefficientMap : Γ(parameter, baseOpen) ⟶ squareZeroRing`. -/
private lemma affine_scalar_spec_map {parameter : Scheme.{schemeUniverse}} {baseOpen : parameter.Opens}
    (hV : IsAffineOpen baseOpen) {squareZeroRing : CommRingCat.{schemeUniverse}} (coefficientMap : Γ(parameter, baseOpen) ⟶ squareZeroRing)
    (inclusionCondition : ⊤ ≤ (Spec.map coefficientMap ≫ hV.fromSpec) ⁻¹ᵁ baseOpen) (scalar : Γ(parameter, baseOpen)) :
    (Scheme.ΓSpecIso squareZeroRing).hom ((Spec.map coefficientMap ≫ hV.fromSpec).appLE baseOpen ⊤ inclusionCondition scalar) = coefficientMap scalar := by
  have : (Spec.map coefficientMap ≫ hV.fromSpec).appLE baseOpen ⊤ inclusionCondition ≫ (Scheme.ΓSpecIso squareZeroRing).hom = coefficientMap := by
    have e₁ : hV.fromSpec.appLE baseOpen ⊤ hV.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
      rw [Scheme.Hom.appLE, hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      convert Category.comp_id _
      exact (Spec Γ(parameter, baseOpen)).presheaf.map_id _
    rw [← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ _ hV.fromSpec_preimage_self.ge (by simp), e₁,
      Category.assoc, Scheme.Hom.appLE_top_top_eq_appTop, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  exact congr($this scalar)


set_option maxHeartbeats 1600000 in
/-- A section with a coordinate functional taking it to one cannot vanish after
any nonempty affine base change, provided the actual first higher direct image
vanishes after every base change. In particular this applies to every vector
of a local basis of the direct image of a sufficiently positive curve line. -/
theorem pullback_primitive_section_ne_zero
    {baseField : Type schemeUniverse} [Field baseField] {sourceScheme : Scheme.{schemeUniverse}}
    (sourceMap : sourceScheme ⟶ Spec (.of baseField)) [Flat sourceMap] [IsProper sourceMap] [LocallyOfFinitePresentation sourceMap]
    [∀ parameter : Over (Spec (.of baseField)), HasInjectiveResolutions (Limits.pullback sourceMap parameter.hom).Modules]
    {parameter : Over (Spec (.of baseField))} (moduleSheaf : (Limits.pullback sourceMap parameter.hom).Modules) [moduleSheaf.IsInvertible]
    (hH1 : ∀ (furtherParameter : Over (Spec (.of baseField))) (furtherChange : furtherParameter ⟶ parameter),
      IsZero ((higherDirectImage (Limits.pullback.snd sourceMap furtherParameter.hom) 1).obj
        ((Scheme.Modules.pullback (baseChangeMap sourceMap furtherChange)).obj moduleSheaf)))
    {baseOpen : parameter.left.Opens} (hV : IsAffineOpen baseOpen)
    (sectionValue : Γ((pushforward (Limits.pullback.snd sourceMap parameter.hom)).obj moduleSheaf, baseOpen))
    (coordinate : Γ((pushforward (Limits.pullback.snd sourceMap parameter.hom)).obj moduleSheaf, baseOpen) →ₗ[Γ(parameter.left, baseOpen)]
      Γ(parameter.left, baseOpen)) (hs : coordinate sectionValue = 1)
    {extensionParameter : Over (Spec (.of baseField))} (baseChange : extensionParameter ⟶ parameter) [IsAffine extensionParameter.left]
    [Nontrivial Γ(extensionParameter.left, ⊤)] (hi : ⊤ ≤ baseChange.left ⁻¹ᵁ baseOpen) :
    pullbackSection (baseChangeMap sourceMap baseChange)
      (show Γ(moduleSheaf, Limits.pullback.snd sourceMap parameter.hom ⁻¹ᵁ baseOpen) from sectionValue) ≠ 0 := by
  classical
  let parameterProjection := Limits.pullback.snd sourceMap parameter.hom
  have hW := parameterProjection.isCompact_preimage hV.isCompact
  obtain ⟨coverIndex, _, cover, hUa, hUV, hUsup, he⟩ := finite_trivializing_affine_cover moduleSheaf hW
  have := Fintype.ofFinite coverIndex
  let instC : ∀ (degree : ℕ) (simplex : Fin (degree + 1) → coverIndex), Module Γ(parameter.left, baseOpen) Γ(moduleSheaf, ⨅ position, cover (simplex position)) :=
    fun degree simplex ↦ Module.compHom _ (parameterProjection.appLE baseOpen _ (iInf_le_preimage_of_forall_le cover hUV simplex)).hom
  have hU : ∀ (degree : ℕ) (simplex : Fin (degree + 1) → coverIndex) (scalar : Γ(parameter.left, baseOpen)) (localSection : Γ(moduleSheaf, ⨅ position, cover (simplex position))),
      scalar • localSection = parameterProjection.appLE baseOpen _ (iInf_le_preimage_of_forall_le cover hUV simplex) scalar • localSection :=
    fun _ _ _ _ ↦ rfl
  have hUa' (degree : ℕ) (simplex : Fin (degree + 1) → coverIndex) : IsAffineOpen (⨅ position, cover (simplex position)) :=
    affine_intersections_over_affine parameterProjection hV cover hUa hUV simplex
  have he' (degree : ℕ) (simplex : Fin (degree + 1) → coverIndex) : ∃ generator : Γ(moduleSheaf, ⨅ position, cover (simplex position)), IsFreeGenerator generator := by
    obtain ⟨generator, he⟩ := he (simplex 0)
    exact ⟨_, he.map (iInf_le _ 0)⟩
  have hexB : ∀ (furtherParameter : Over (Spec (.of baseField))) (furtherChange : furtherParameter ⟶ parameter) [IsAffine furtherParameter.left]
      (hj : ⊤ ≤ furtherChange.left ⁻¹ᵁ baseOpen),
      letI := (furtherChange.left.appLE baseOpen ⊤ hj).hom.toAlgebra
      Function.Exact ((cechDifferential moduleSheaf cover hUV hU 0).lTensor Γ(furtherParameter.left, ⊤))
        ((cechDifferential moduleSheaf cover hUV hU 1).lTensor Γ(furtherParameter.left, ⊤)) := by
    intro furtherParameter furtherChange _ hj
    let := (furtherChange.left.appLE baseOpen ⊤ hj).hom.toAlgebra
    have square := isPullback_baseChangeMap sourceMap furtherChange
    have : ((Scheme.Modules.pullback (baseChangeMap sourceMap furtherChange)).obj moduleSheaf).IsInvertible :=
      Scheme.Modules.isInvertible_pullback (baseChangeMap sourceMap furtherChange) moduleSheaf
    have hZ : IsZero ((higherDirectImage (Limits.pullback.snd sourceMap furtherParameter.hom) 1).obj
        ((Scheme.Modules.pullback (baseChangeMap sourceMap furtherChange)).obj moduleSheaf)) :=
      hH1 furtherParameter furtherChange
    have hsup : ⨆ baseChange, baseChangeMap sourceMap furtherChange ⁻¹ᵁ cover baseChange = ⊤ := by
      rw [← Scheme.Hom.preimage_iSup, hUsup, ← Scheme.Hom.comp_preimage, square.w,
        Scheme.Hom.comp_preimage, eq_top_iff]
      exact (Scheme.Hom.preimage_top _).ge.trans (Scheme.Hom.preimage_mono _ hj)
    exact exact_lTensor_cechDifferential hj moduleSheaf cover hUV rfl hU square hV hUa' he'
      (exactAt_cechComplex_of_isZero_higherDirectImage (Limits.pullback.snd sourceMap furtherParameter.hom) _
        (fun baseChange ↦ isAffineOpen_preimage_of_isPullback square hV hj (hUV baseChange) (hUa baseChange)) hsup _ 1 hZ)
  have hexM : ∀ (testModule : Type schemeUniverse) [AddCommGroup testModule] [Module Γ(parameter.left, baseOpen) testModule],
      Function.Exact ((cechDifferential moduleSheaf cover hUV hU 0).lTensor testModule)
        ((cechDifferential moduleSheaf cover hUV hU 1).lTensor testModule) := by
    intro testModule _ _
    let : Module Γ(parameter.left, baseOpen)ᵐᵒᵖ testModule :=
      Module.compHom testModule ((RingHom.id Γ(parameter.left, baseOpen)).fromOpposite fun _ _ ↦ mul_comm _ _)
    have : IsCentralScalar Γ(parameter.left, baseOpen) testModule := ⟨fun _ _ ↦ rfl⟩
    let squareZeroRing := CommRingCat.of (TrivSqZeroExt Γ(parameter.left, baseOpen) testModule)
    let coefficientMap : Γ(parameter.left, baseOpen) ⟶ squareZeroRing := CommRingCat.ofHom (algebraMap _ _)
    let furtherParameter : Over (Spec (.of baseField)) := Over.mk (Spec.map coefficientMap ≫ hV.fromSpec ≫ parameter.hom)
    let furtherChange : furtherParameter ⟶ parameter := Over.homMk (Spec.map coefficientMap ≫ hV.fromSpec) (by simp [furtherParameter])
    have hj : ⊤ ≤ furtherChange.left ⁻¹ᵁ baseOpen := by
      change ⊤ ≤ (Spec.map coefficientMap ≫ hV.fromSpec) ⁻¹ᵁ baseOpen
      rw [Scheme.Hom.comp_preimage, hV.fromSpec_preimage_self, Scheme.Hom.preimage_top]
    have : IsAffine furtherParameter.left := inferInstanceAs (IsAffine (Spec squareZeroRing))
    have inclusionCondition := hexB furtherParameter furtherChange hj
    let := (furtherChange.left.appLE baseOpen ⊤ hj).hom.toAlgebra
    have key (scalar : Γ(parameter.left, baseOpen)) (localSection : Γ(furtherParameter.left, ⊤)) :
        (Scheme.ΓSpecIso squareZeroRing).hom (scalar • localSection) =
          TrivSqZeroExt.inl scalar * (Scheme.ΓSpecIso squareZeroRing).hom localSection := by
      rw [Algebra.smul_def, map_mul]
      congr 1
      exact affine_scalar_spec_map hV coefficientMap hj scalar
    let functionValue : Γ(furtherParameter.left, ⊤) →ₗ[Γ(parameter.left, baseOpen)] testModule :=
      { toFun localSection := ((Scheme.ΓSpecIso squareZeroRing).hom localSection).snd
        map_add' localSection otherLocalSection := by rw [map_add, TrivSqZeroExt.snd_add]
        map_smul' scalar localSection := by
          rw [key, TrivSqZeroExt.inl_mul_eq_smul, RingHom.id_apply]
          exact TrivSqZeroExt.snd_smul scalar _ }
    let inclusion : testModule →ₗ[Γ(parameter.left, baseOpen)] Γ(furtherParameter.left, ⊤) :=
      { toFun element := (Scheme.ΓSpecIso squareZeroRing).inv (TrivSqZeroExt.inr element)
        map_add' firstElement secondElement := by simp
        map_smul' scalar element := by
          apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso squareZeroRing).hom).1
          rw [RingHom.id_apply, key, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply,
            TrivSqZeroExt.inl_mul_inr] }
    exact Function.Exact.lTensor_of_retract inclusion functionValue
      (LinearMap.ext fun element ↦ by simp [functionValue, inclusion]) inclusionCondition
  have hflat (degree : ℕ) : Module.Flat Γ(parameter.left, baseOpen) (CechCochain cover moduleSheaf.presheaf degree) := by
    have (simplex : Fin (degree + 1) → coverIndex) : Module.Flat Γ(parameter.left, baseOpen) Γ(moduleSheaf, ⨅ position, cover (simplex position)) := by
      obtain ⟨generator, he⟩ := he' degree simplex
      let := (parameterProjection.appLE baseOpen _ (iInf_le_preimage_of_forall_le cover hUV simplex)).hom.toAlgebra
      have : Module.Flat Γ(parameter.left, baseOpen) Γ(Limits.pullback sourceMap parameter.hom, ⨅ position, cover (simplex position)) :=
        HasRingHomProperty.appLE @Flat parameterProjection inferInstance ⟨baseOpen, hV⟩ ⟨_, hUa' degree simplex⟩ _
      let trivialization : Γ(Limits.pullback sourceMap parameter.hom, ⨅ position, cover (simplex position)) →ₗ[Γ(parameter.left, baseOpen)] Γ(moduleSheaf, ⨅ position, cover (simplex position)) :=
        { toFun functionValue := functionValue • generator
          map_add' firstFunction secondFunction := add_smul firstFunction secondFunction generator
          map_smul' scalar functionValue := by
            rw [RingHom.id_apply, hU, Algebra.smul_def, mul_smul]
            rfl }
      exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective trivialization he.bijective).symm
    exact Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := Γ(parameter.left, baseOpen))
      (M := fun simplex : Fin (degree + 1) → coverIndex ↦ Γ(moduleSheaf, ⨅ position, cover (simplex position)))).symm
  let := (baseChange.left.appLE baseOpen ⊤ hi).hom.toAlgebra
  have : Module.Flat Γ(parameter.left, baseOpen) (CechCochain cover moduleSheaf.presheaf (0 + 1)) := hflat _
  have : Module.Flat Γ(parameter.left, baseOpen) (CechCochain cover moduleSheaf.presheaf (1 + 1)) := hflat _
  have hinj := Module.Flat.lTensor_injective_ker_subtype (cechDifferential moduleSheaf cover hUV hU 0)
    (cechDifferential moduleSheaf cover hUV hU 1) (cechDifferential_comp moduleSheaf cover hUV hU 0) hexM Γ(extensionParameter.left, ⊤)
  let restrictionMap : Γ((pushforward parameterProjection).obj moduleSheaf, baseOpen) →ₗ[Γ(parameter.left, baseOpen)] CechCochain cover moduleSheaf.presheaf 0 :=
    { toFun localSection simplex := moduleSheaf.presheaf.map (homOfLE (iInf_le_of_iSup_eq cover hUsup simplex)).op localSection
      map_add' localSection otherLocalSection := by funext simplex; exact map_add _ _ _
      map_smul' scalar localSection := by
        funext simplex
        change moduleSheaf.presheaf.map (homOfLE (iInf_le_of_iSup_eq cover hUsup simplex)).op
            ((parameterProjection.app baseOpen scalar) • (show Γ(moduleSheaf, parameterProjection ⁻¹ᵁ baseOpen) from localSection)) =
          (parameterProjection.appLE baseOpen _ (iInf_le_preimage_of_forall_le cover hUV simplex) scalar) •
            moduleSheaf.presheaf.map (homOfLE (iInf_le_of_iSup_eq cover hUsup simplex)).op localSection
        rw [Scheme.Modules.map_smul, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply,
          Scheme.Hom.appLE_map] }
  have hρ₀ (localSection : Γ((pushforward parameterProjection).obj moduleSheaf, baseOpen)) : restrictionMap localSection ∈ LinearMap.ker
      (cechDifferential moduleSheaf cover hUV hU 0) :=
    cechComplex_d_zero_restrict cover moduleSheaf.presheaf localSection (iInf_le_of_iSup_eq cover hUsup)
  let cyclesEquiv : Γ((pushforward parameterProjection).obj moduleSheaf, baseOpen) ≃ₗ[Γ(parameter.left, baseOpen)]
      LinearMap.ker (cechDifferential moduleSheaf cover hUV hU 0) :=
    LinearEquiv.ofBijective (restrictionMap.codRestrict _ hρ₀)
      ⟨fun localSection otherLocalSection hxx' ↦ eq_of_forall_presheaf_map_eq moduleSheaf cover hUsup localSection otherLocalSection fun simplex ↦
        congr_fun (congrArg Subtype.val hxx') simplex, fun c ↦ by
        obtain ⟨localSection, hx⟩ := exists_presheaf_map_eq_of_cechComplex_d_eq_zero moduleSheaf cover hUsup c.1 c.2
        exact ⟨localSection, Subtype.ext (funext hx)⟩⟩
  have hne : ((1 : Γ(extensionParameter.left, ⊤)) ⊗ₜ[Γ(parameter.left, baseOpen)] restrictionMap sectionValue) ≠ 0 := by
    intro h0
    have h1 : ((LinearMap.ker (cechDifferential moduleSheaf cover hUV hU 0)).subtype.lTensor Γ(extensionParameter.left, ⊤))
        ((1 : Γ(extensionParameter.left, ⊤)) ⊗ₜ cyclesEquiv sectionValue) = 0 := h0
    have h2 := hinj (h1.trans (map_zero _).symm)
    have h3 := congrArg (TensorProduct.rid Γ(parameter.left, baseOpen) Γ(extensionParameter.left, ⊤))
      (congrArg ((coordinate.comp cyclesEquiv.symm.toLinearMap).lTensor Γ(extensionParameter.left, ⊤)) h2)
    have h4 : (coordinate.comp cyclesEquiv.symm.toLinearMap) (cyclesEquiv sectionValue) = 1 := by
      change coordinate (cyclesEquiv.symm (cyclesEquiv sectionValue)) = 1
      rw [cyclesEquiv.symm_apply_apply, hs]
    rw [map_zero, map_zero, LinearMap.lTensor_tmul, h4,
      TensorProduct.rid_tmul, one_smul] at h3
    exact one_ne_zero h3
  have square := isPullback_baseChangeMap sourceMap baseChange
  intro hzero
  apply hne
  refine (cechBaseChange_bijective hi moduleSheaf cover hUV rfl hU square hV hUa' he' 0).1 ?_
  rw [map_zero]
  funext simplex
  rw [cechBaseChange_tmul]
  have : restrictionMap sectionValue simplex = moduleSheaf.presheaf.map (homOfLE (iInf_le_of_iSup_eq cover hUsup simplex)).op sectionValue := rfl
  rw [this, pullbackSection_map, map_one, one_smul]
  erw [hzero]
  rw [map_zero, map_zero]
  rfl


/-- Every vector of an actual local basis stays nonzero after any nonempty
affine base change; the coordinate functional exhibits its primitivity. -/
theorem pullback_basis_section_ne_zero
    {baseField : Type schemeUniverse} [Field baseField] {sourceScheme : Scheme.{schemeUniverse}}
    (sourceMap : sourceScheme ⟶ Spec (.of baseField)) [Flat sourceMap] [IsProper sourceMap] [LocallyOfFinitePresentation sourceMap]
    [∀ parameter : Over (Spec (.of baseField)), HasInjectiveResolutions (Limits.pullback sourceMap parameter.hom).Modules]
    {parameter : Over (Spec (.of baseField))} (moduleSheaf : (Limits.pullback sourceMap parameter.hom).Modules) [moduleSheaf.IsInvertible]
    (hH1 : ∀ (furtherParameter : Over (Spec (.of baseField))) (basisIndex : furtherParameter ⟶ parameter),
      IsZero ((higherDirectImage (Limits.pullback.snd sourceMap furtherParameter.hom) 1).obj
        ((Scheme.Modules.pullback (baseChangeMap sourceMap basisIndex)).obj moduleSheaf)))
    {baseOpen : parameter.left.Opens} (hV : IsAffineOpen baseOpen)
    {coverIndex : Type basisUniverse}
    (basis : Module.Basis coverIndex Γ(parameter.left, baseOpen)
      Γ((pushforward (Limits.pullback.snd sourceMap parameter.hom)).obj moduleSheaf, baseOpen)) (basisIndex : coverIndex)
    {extensionParameter : Over (Spec (.of baseField))} (baseChange : extensionParameter ⟶ parameter) [IsAffine extensionParameter.left]
    [Nontrivial Γ(extensionParameter.left, ⊤)] (hi : ⊤ ≤ baseChange.left ⁻¹ᵁ baseOpen) :
    pullbackSection (baseChangeMap sourceMap baseChange)
      (show Γ(moduleSheaf, Limits.pullback.snd sourceMap parameter.hom ⁻¹ᵁ baseOpen) from basis basisIndex) ≠ 0 := by
  exact pullback_primitive_section_ne_zero sourceMap moduleSheaf hH1 hV (basis basisIndex) (basis.coord basisIndex)
    (by simp) baseChange hi

end AlgebraicGeometry.Scheme.Modules
