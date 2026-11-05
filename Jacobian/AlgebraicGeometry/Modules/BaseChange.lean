import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Jacobian.Algebra.Category.Ring.Pushout
import Jacobian.AlgebraicGeometry.Modules.AffineSections

/-!
# Base change of sections on affine opens
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe schemeUniverse
open CategoryTheory Limits TopologicalSpace Opposite TensorProduct

namespace AlgebraicGeometry.Scheme.Hom

lemma appLE_top_top_eq_appTop
    {scheme target : Scheme.{schemeUniverse}} (morphism : scheme ⟶ target)
    (inclusion : ⊤ ≤ morphism ⁻¹ᵁ ⊤) : morphism.appLE ⊤ ⊤ inclusion = morphism.appTop := by
  simp [AlgebraicGeometry.Scheme.Hom.appLE, AlgebraicGeometry.Scheme.Hom.appTop]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme baseScheme : Scheme.{schemeUniverse}} (structureMap : scheme ⟶ baseScheme) (coherentSheaf : scheme.Modules)

/-- The sections `Γ(ℱ, W)` of an `𝒪_X`-module over an open `W`, as a module over the global
functions `Γ(S, ⊤)` of the target of `f : X ⟶ S`, through `f^♯ : Γ(S, ⊤) ⟶ Γ(X, ⊤)` followed by
restriction to `W`. -/
noncomputable def sectionsModule (openSubset : scheme.Opens) : ModuleCat.{schemeUniverse} Γ(baseScheme, ⊤) :=
  letI : Module Γ(baseScheme, ⊤) Γ(coherentSheaf, openSubset) :=
    Module.compHom Γ(coherentSheaf, openSubset)
      (structureMap.appTop ≫ scheme.presheaf.map openSubset.leTop.op).hom
  ModuleCat.of Γ(baseScheme, ⊤) Γ(coherentSheaf, openSubset)

variable {pulledScheme extensionScheme : Scheme.{schemeUniverse}} {structureMap : scheme ⟶ baseScheme} {structureMap' : pulledScheme ⟶ extensionScheme} {baseChangeMap : extensionScheme ⟶ baseScheme} {baseChangeMap' : pulledScheme ⟶ scheme}
  (cartesian : IsPullback baseChangeMap' structureMap' structureMap baseChangeMap) (coherentSheaf : scheme.Modules)
  [Algebra Γ(baseScheme, ⊤) Γ(extensionScheme, ⊤)] (hg : algebraMap Γ(baseScheme, ⊤) Γ(extensionScheme, ⊤) = baseChangeMap.appTop.hom)

include cartesian hg in
/-- The functions on the base act compatibly on the sections of `ℱ` and of `g'^* ℱ`. -/
lemma pullbackSection_smul_appTop {openSubset : scheme.Opens} (baseScalar : Γ(baseScheme, ⊤)) (sectionValue : Γ(coherentSheaf, openSubset)) :
    pullbackSection baseChangeMap' (scheme.presheaf.map (homOfLE (le_top : openSubset ≤ ⊤)).op (structureMap.appTop baseScalar) • sectionValue) =
      pulledScheme.presheaf.map (homOfLE (le_top : baseChangeMap' ⁻¹ᵁ openSubset ≤ ⊤)).op (structureMap'.appTop (algebraMap _ _ baseScalar)) •
        pullbackSection baseChangeMap' sectionValue := by
  rw [pullbackSection_smul, hg]
  congr 1
  rw [← CommRingCat.comp_apply, baseChangeMap'.naturality, CommRingCat.comp_apply]
  have sectionSquare :
      structureMap.appLE ⊤ openSubset (by simp) ≫
        baseChangeMap'.appLE openSubset (baseChangeMap' ⁻¹ᵁ openSubset) le_rfl =
      baseChangeMap.appLE ⊤ ⊤ (by simp) ≫
        structureMap'.appLE ⊤ (baseChangeMap' ⁻¹ᵁ openSubset) (by simp) := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, cartesian.w]
  simpa [Scheme.Hom.appLE, Scheme.Hom.appTop, CommRingCat.comp_apply] using
    congrArg (fun sectionMap : Γ(baseScheme, ⊤) ⟶
      Γ(pulledScheme, baseChangeMap' ⁻¹ᵁ openSubset) ↦ sectionMap baseScalar) sectionSquare

/-- The pullback of sections `Γ(ℱ, W) ⟶ Γ(g'^* ℱ, g'⁻¹ W)`, as an additive map between the
modules of sections over the bases. -/
noncomputable def pullbackSectionAddHom (openSubset : scheme.Opens) :
    sectionsModule structureMap coherentSheaf openSubset →+ sectionsModule structureMap' ((pullback baseChangeMap').obj coherentSheaf) (baseChangeMap' ⁻¹ᵁ openSubset) where
  toFun sectionValue := pullbackSection (M := coherentSheaf) (U := openSubset) baseChangeMap' sectionValue
  map_zero' := map_zero (((pullbackPushforwardAdjunction baseChangeMap').unit.app coherentSheaf).app openSubset).hom
  map_add' sectionValue sectionValue' := pullbackSection_add baseChangeMap' (moduleSheaf := coherentSheaf) (openSubset := openSubset) sectionValue sectionValue'

omit [Algebra Γ(baseScheme, ⊤) Γ(extensionScheme, ⊤)] in
lemma pullbackSectionAddHom_apply (openSubset : scheme.Opens) (sectionValue : sectionsModule structureMap coherentSheaf openSubset) :
    pullbackSectionAddHom (structureMap := structureMap) (structureMap' := structureMap') (baseChangeMap' := baseChangeMap') coherentSheaf openSubset sectionValue =
      pullbackSection (M := coherentSheaf) (U := openSubset) baseChangeMap' sectionValue :=
  rfl

include cartesian hg in
lemma pullbackSectionAddHom_smul (openSubset : scheme.Opens) (baseScalar : Γ(baseScheme, ⊤)) (sectionValue : sectionsModule structureMap coherentSheaf openSubset) :
    pullbackSectionAddHom (structureMap := structureMap) (structureMap' := structureMap') (baseChangeMap' := baseChangeMap') coherentSheaf openSubset (baseScalar • sectionValue) =
      algebraMap Γ(baseScheme, ⊤) Γ(extensionScheme, ⊤) baseScalar • pullbackSectionAddHom (structureMap := structureMap) (structureMap' := structureMap') (baseChangeMap' := baseChangeMap') coherentSheaf openSubset sectionValue :=
  pullbackSection_smul_appTop cartesian coherentSheaf hg (openSubset := openSubset) baseScalar sectionValue

/-- The additive map underlying `AlgebraicGeometry.Scheme.Modules.sectionsModuleBaseChange`. -/
noncomputable def sectionsModuleBaseChangeAddHom (cartesian : IsPullback baseChangeMap' structureMap' structureMap baseChangeMap) (coherentSheaf : scheme.Modules)
    (hg : algebraMap Γ(baseScheme, ⊤) Γ(extensionScheme, ⊤) = baseChangeMap.appTop.hom) (openSubset : scheme.Opens) :
    Γ(extensionScheme, ⊤) ⊗[Γ(baseScheme, ⊤)] sectionsModule structureMap coherentSheaf openSubset →+
      sectionsModule structureMap' ((pullback baseChangeMap').obj coherentSheaf) (baseChangeMap' ⁻¹ᵁ openSubset) :=
  TensorProduct.liftAddHom (R := Γ(baseScheme, ⊤)) (M := Γ(extensionScheme, ⊤)) (N := sectionsModule structureMap coherentSheaf openSubset)
    (P := sectionsModule structureMap' ((pullback baseChangeMap').obj coherentSheaf) (baseChangeMap' ⁻¹ᵁ openSubset))
    { toFun extensionScalar := (DistribSMul.toAddMonoidHom _ extensionScalar).comp
        (pullbackSectionAddHom (structureMap := structureMap) (structureMap' := structureMap') (baseChangeMap' := baseChangeMap') coherentSheaf openSubset)
      map_zero' := AddMonoidHom.ext fun sectionValue ↦ zero_smul Γ(extensionScheme, ⊤)
        (pullbackSectionAddHom (structureMap := structureMap) (structureMap' := structureMap') (baseChangeMap' := baseChangeMap') coherentSheaf openSubset sectionValue)
      map_add' extensionScalar extensionScalar' := AddMonoidHom.ext fun sectionValue ↦ add_smul extensionScalar extensionScalar'
        (pullbackSectionAddHom (structureMap := structureMap) (structureMap' := structureMap') (baseChangeMap' := baseChangeMap') coherentSheaf openSubset sectionValue) }
    (fun baseScalar extensionScalar sectionValue ↦ by
      change (baseScalar • extensionScalar) • pullbackSectionAddHom (structureMap := structureMap) (structureMap' := structureMap') (baseChangeMap' := baseChangeMap') coherentSheaf openSubset sectionValue =
        extensionScalar • pullbackSectionAddHom (structureMap := structureMap) (structureMap' := structureMap') (baseChangeMap' := baseChangeMap') coherentSheaf openSubset (baseScalar • sectionValue)
      rw [pullbackSectionAddHom_smul cartesian coherentSheaf hg, smul_smul, Algebra.smul_def, mul_comm])

lemma sectionsModuleBaseChangeAddHom_tmul (openSubset : scheme.Opens) (extensionScalar : Γ(extensionScheme, ⊤))
    (sectionValue : sectionsModule structureMap coherentSheaf openSubset) :
    sectionsModuleBaseChangeAddHom cartesian coherentSheaf hg openSubset (extensionScalar ⊗ₜ sectionValue) =
      extensionScalar • pullbackSectionAddHom (structureMap := structureMap) (structureMap' := structureMap') (baseChangeMap' := baseChangeMap') coherentSheaf openSubset sectionValue :=
  TensorProduct.liftAddHom_tmul (R := Γ(baseScheme, ⊤)) (M := Γ(extensionScheme, ⊤)) (N := sectionsModule structureMap coherentSheaf openSubset)
    (P := sectionsModule structureMap' ((pullback baseChangeMap').obj coherentSheaf) (baseChangeMap' ⁻¹ᵁ openSubset)) _ _ _ _

/-- **Base change of sections.** The map `B ⊗[A] Γ(ℱ, W) ⟶ Γ(g'^* ℱ, g'⁻¹ W)`,
`b ⊗ m ↦ b • g'^* m`, for `A = Γ(S, ⊤)` and `B = Γ(T, ⊤)`. -/
noncomputable def sectionsModuleBaseChange (cartesian : IsPullback baseChangeMap' structureMap' structureMap baseChangeMap) (coherentSheaf : scheme.Modules)
    (hg : algebraMap Γ(baseScheme, ⊤) Γ(extensionScheme, ⊤) = baseChangeMap.appTop.hom) (openSubset : scheme.Opens) :
    Γ(extensionScheme, ⊤) ⊗[Γ(baseScheme, ⊤)] sectionsModule structureMap coherentSheaf openSubset →ₗ[Γ(extensionScheme, ⊤)]
      sectionsModule structureMap' ((pullback baseChangeMap').obj coherentSheaf) (baseChangeMap' ⁻¹ᵁ openSubset) where
  toAddHom := (sectionsModuleBaseChangeAddHom cartesian coherentSheaf hg openSubset).toAddHom
  map_smul' scalar element := by
    change sectionsModuleBaseChangeAddHom cartesian coherentSheaf hg openSubset (scalar • element) =
      scalar • sectionsModuleBaseChangeAddHom cartesian coherentSheaf hg openSubset element
    induction element using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | add element otherElement hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
    | tmul extensionScalar sectionValue =>
      rw [TensorProduct.smul_tmul', sectionsModuleBaseChangeAddHom_tmul,
        sectionsModuleBaseChangeAddHom_tmul, smul_eq_mul, mul_smul]

lemma sectionsModuleBaseChange_tmul (openSubset : scheme.Opens) (extensionScalar : Γ(extensionScheme, ⊤)) (sectionValue : sectionsModule structureMap coherentSheaf openSubset) :
    sectionsModuleBaseChange cartesian coherentSheaf hg openSubset (extensionScalar ⊗ₜ sectionValue) =
      extensionScalar • pullbackSectionAddHom (structureMap := structureMap) (structureMap' := structureMap') (baseChangeMap' := baseChangeMap') coherentSheaf openSubset sectionValue :=
  sectionsModuleBaseChangeAddHom_tmul cartesian coherentSheaf hg openSubset extensionScalar sectionValue

/-- **Base change of sections over an affine open.** If `S` and `T` are affine, `ℱ` is
quasi-coherent and `W` is an affine open of `X`, the map `B ⊗[A] Γ(ℱ, W) ⟶ Γ(g'^* ℱ, g'⁻¹ W)` is
bijective: it is the composite
`B ⊗[A] Γ(ℱ, W) ≅ Γ(ℱ, W) ⊗[Γ(X, W)] (Γ(X, W) ⊗[A] B) ≅ Γ(ℱ, W) ⊗[Γ(X, W)] Γ(Y, g'⁻¹ W)
≅ Γ(g'^* ℱ, g'⁻¹ W)`, using that `g'⁻¹ W = W ×_S T` is affine with ring of functions
`Γ(X, W) ⊗[A] B`. -/
theorem bijective_sectionsModuleBaseChange [IsAffine baseScheme] [IsAffine extensionScheme]
    [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) coherentSheaf] {openSubset : scheme.Opens} (hW : IsAffineOpen openSubset) :
    Function.Bijective (sectionsModuleBaseChange cartesian coherentSheaf hg openSubset) := by
  have hW' : IsAffineOpen (baseChangeMap' ⁻¹ᵁ openSubset) :=
    by
      have : IsAffineHom baseChangeMap' := MorphismProperty.of_isPullback (P := @IsAffineHom) cartesian.flip inferInstance
      exact hW.preimage baseChangeMap'
  let : Algebra Γ(baseScheme, ⊤) Γ(scheme, openSubset) := (structureMap.appLE ⊤ openSubset (by simp)).hom.toAlgebra
  let : Algebra Γ(scheme, openSubset) Γ(pulledScheme, baseChangeMap' ⁻¹ᵁ openSubset) := (baseChangeMap'.appLE openSubset (baseChangeMap' ⁻¹ᵁ openSubset) le_rfl).hom.toAlgebra
  let : Module Γ(scheme, openSubset) (sectionsModule structureMap coherentSheaf openSubset) := inferInstanceAs (Module Γ(scheme, openSubset) Γ(coherentSheaf, openSubset))
  have : IsScalarTower Γ(baseScheme, ⊤) Γ(scheme, openSubset) (sectionsModule structureMap coherentSheaf openSubset) := ⟨fun baseScalar sectionScalar sectionValue ↦ by
    change (structureMap.appLE ⊤ openSubset _ baseScalar * sectionScalar) • (sectionValue : Γ(coherentSheaf, openSubset)) =
      scheme.presheaf.map (homOfLE (le_top : openSubset ≤ ⊤)).op (structureMap.appTop baseScalar) • sectionScalar • (sectionValue : Γ(coherentSheaf, openSubset))
    rw [mul_smul]
    rfl⟩

  obtain ⟨e₁, he₁⟩ := exists_linearEquiv_pullback_sections baseChangeMap' coherentSheaf hW hW' le_rfl

  have hUY : baseChangeMap' ⁻¹ᵁ openSubset = baseChangeMap' ⁻¹ᵁ openSubset ⊓ structureMap' ⁻¹ᵁ ⊤ := by simp
  have hpush := (isIso_pushoutSection_iff cartesian (US := ⊤) (UT := ⊤) (by simp) (by simp) hUY).mp
    (isIso_pushoutSection_of_isAffineOpen cartesian _ _ hUY (isAffineOpen_top baseScheme) (isAffineOpen_top extensionScheme) hW)
  let sectionEquiv := hpush.flip.tensorEquiv (baseAlgebra' := Γ(scheme, openSubset)) (extensionAlgebra := Γ(extensionScheme, ⊤)) rfl (by
    rw [Scheme.Hom.appLE_top_top_eq_appTop, hg]
    rfl)
  have hε (sectionScalar : Γ(scheme, openSubset)) (extensionScalar : Γ(extensionScheme, ⊤)) : sectionEquiv (sectionScalar ⊗ₜ extensionScalar) = baseChangeMap'.appLE openSubset (baseChangeMap' ⁻¹ᵁ openSubset) le_rfl sectionScalar *
      structureMap'.appLE ⊤ (baseChangeMap' ⁻¹ᵁ openSubset) (by simp) extensionScalar :=
    hpush.flip.tensorEquiv_tmul _ _ sectionScalar extensionScalar
  let εₗ : Γ(scheme, openSubset) ⊗[Γ(baseScheme, ⊤)] Γ(extensionScheme, ⊤) ≃ₗ[Γ(scheme, openSubset)] Γ(pulledScheme, baseChangeMap' ⁻¹ᵁ openSubset) :=
    { sectionEquiv.toAddEquiv with
      map_smul' sectionScalar element := by
        change sectionEquiv (sectionScalar • element) = sectionScalar • sectionEquiv element
        rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, hε, map_one, mul_one, Algebra.smul_def]
        rfl }
  let tensorEquiv : Γ(extensionScheme, ⊤) ⊗[Γ(baseScheme, ⊤)] sectionsModule structureMap coherentSheaf openSubset ≃+
      sectionsModule structureMap' ((pullback baseChangeMap').obj coherentSheaf) (baseChangeMap' ⁻¹ᵁ openSubset) :=
    (TensorProduct.comm Γ(baseScheme, ⊤) Γ(extensionScheme, ⊤) (sectionsModule structureMap coherentSheaf openSubset)).toAddEquiv.trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(baseScheme, ⊤) Γ(scheme, openSubset) Γ(scheme, openSubset)
        (sectionsModule structureMap coherentSheaf openSubset) Γ(extensionScheme, ⊤)).symm.toAddEquiv.trans
      ((εₗ.lTensor (sectionsModule structureMap coherentSheaf openSubset)).toAddEquiv.trans
      ((TensorProduct.comm Γ(scheme, openSubset) (sectionsModule structureMap coherentSheaf openSubset) Γ(pulledScheme, baseChangeMap' ⁻¹ᵁ openSubset)).toAddEquiv.trans
        e₁.toAddEquiv)))
  suffices compatibility : ∀ element, sectionsModuleBaseChange cartesian coherentSheaf hg openSubset element = tensorEquiv element by
    have : ⇑(sectionsModuleBaseChange cartesian coherentSheaf hg openSubset) = ⇑tensorEquiv := funext compatibility
    rw [this]
    exact tensorEquiv.bijective
  intro element
  induction element using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add element otherElement hx hy => rw [map_add, map_add, hx, hy]
  | tmul extensionScalar sectionValue =>
    rw [sectionsModuleBaseChange_tmul]
    change _ = e₁ (TensorProduct.comm _ _ _ (εₗ.lTensor _
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(baseScheme, ⊤) Γ(scheme, openSubset) Γ(scheme, openSubset)
        (sectionsModule structureMap coherentSheaf openSubset) Γ(extensionScheme, ⊤)).symm (sectionValue ⊗ₜ extensionScalar))))
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.lTensor_tmul,
      TensorProduct.comm_tmul]
    change _ = e₁ (sectionEquiv (1 ⊗ₜ extensionScalar) ⊗ₜ (sectionValue : Γ(coherentSheaf, openSubset)))
    rw [hε, map_one, one_mul, ← mul_one (structureMap'.appLE ⊤ (baseChangeMap' ⁻¹ᵁ openSubset) _ extensionScalar), ← smul_eq_mul,
      ← TensorProduct.smul_tmul', e₁.map_smul, he₁]
    simp only [homOfLE_refl, op_id]
    change structureMap'.appLE ⊤ (baseChangeMap' ⁻¹ᵁ openSubset) _ extensionScalar •
        pullbackSection baseChangeMap' (M := coherentSheaf) sectionValue =
      structureMap'.appLE ⊤ (baseChangeMap' ⁻¹ᵁ openSubset) _ extensionScalar •
        (((pullback baseChangeMap').obj coherentSheaf).presheaf.map
          (𝟙 (op (baseChangeMap' ⁻¹ᵁ openSubset))))
          (pullbackSection baseChangeMap' (M := coherentSheaf) sectionValue)
    exact congrArg
      (fun sectionMap : Γ((pullback baseChangeMap').obj coherentSheaf,
          baseChangeMap' ⁻¹ᵁ openSubset) ⟶
          Γ((pullback baseChangeMap').obj coherentSheaf, baseChangeMap' ⁻¹ᵁ openSubset) ↦
        structureMap'.appLE ⊤ (baseChangeMap' ⁻¹ᵁ openSubset) _ extensionScalar •
          sectionMap (pullbackSection baseChangeMap' (M := coherentSheaf) sectionValue))
      (((pullback baseChangeMap').obj coherentSheaf).presheaf.map_id
        (op (baseChangeMap' ⁻¹ᵁ openSubset))).symm

end AlgebraicGeometry.Scheme.Modules
