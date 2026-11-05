import Jacobian.RingTheory.Flat.DescentAlgebra
import Jacobian.Algebra.Category.Ring.Pushout
import Jacobian.AlgebraicGeometry.GlobalSections.FlatBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

variable {coverScheme base scheme : Scheme.{schemeUniverse}} [IsAffine coverScheme] [IsAffine base] [IsAffine scheme] (coverMap : coverScheme ⟶ base) [Flat coverMap]
  (structureMap : scheme ⟶ coverScheme)

noncomputable abbrev coactionUnit : scheme ⟶ pullback (structureMap ≫ coverMap) coverMap :=
  pullback.lift (𝟙 scheme) structureMap (by simp)

noncomputable abbrev coactionForget :
    pullback (pullback.snd (structureMap ≫ coverMap) coverMap ≫ coverMap) coverMap ⟶ pullback (structureMap ≫ coverMap) coverMap :=
  pullback.map _ _ _ _ (pullback.fst _ _) (𝟙 coverScheme) (𝟙 base) (by simp [pullback.condition]) (by simp)

noncomputable abbrev coactionMap (coaction : pullback (structureMap ≫ coverMap) coverMap ⟶ scheme)
    (coaction_over : coaction ≫ structureMap = pullback.snd _ _) :
    pullback (pullback.snd (structureMap ≫ coverMap) coverMap ≫ coverMap) coverMap ⟶ pullback (structureMap ≫ coverMap) coverMap :=
  pullback.map _ _ _ _ coaction (𝟙 coverScheme) (𝟙 base) (by rw [reassoc_of% coaction_over]; simp) (by simp)

theorem exists_isPullback_of_coaction (coaction : pullback (structureMap ≫ coverMap) coverMap ⟶ scheme)
    (coaction_over : coaction ≫ structureMap = pullback.snd _ _) (counit : coactionUnit coverMap structureMap ≫ coaction = 𝟙 scheme)
    (coassociativity : coactionMap coverMap structureMap coaction coaction_over ≫ coaction = coactionForget coverMap structureMap ≫ coaction) :
    ∃ (descendedScheme : Scheme.{schemeUniverse}) (descendedStructure : descendedScheme ⟶ base) (descentMap : scheme ⟶ descendedScheme), IsPullback descentMap structureMap descendedStructure coverMap ∧
      coaction ≫ descentMap = pullback.fst _ _ ≫ descentMap := by
  let baseRing : CommRingCat.{schemeUniverse} := Γ(base, ⊤)
  let coverRing : CommRingCat.{schemeUniverse} := Γ(coverScheme, ⊤)
  let totalRing : CommRingCat.{schemeUniverse} := Γ(scheme, ⊤)
  let _ : Algebra baseRing coverRing := coverMap.appTop.hom.toAlgebra
  let _ : Algebra coverRing totalRing := structureMap.appTop.hom.toAlgebra
  let _ : Algebra baseRing totalRing := (structureMap ≫ coverMap).appTop.hom.toAlgebra
  have : IsScalarTower baseRing coverRing totalRing := IsScalarTower.of_algebraMap_eq fun element ↦ rfl
  have hflat : Module.Flat baseRing coverRing := coverMap.flat_appTop
  have hP := isPushout_appTop_of_flat coverMap (structureMap ≫ coverMap)
  let sectionsEquiv : coverRing ⊗[baseRing] totalRing ≃+* Γ(pullback (structureMap ≫ coverMap) coverMap, ⊤) := hP.tensorEquiv rfl rfl
  have sectionsEquiv_tmul : ∀ (scalar : coverRing) (element : totalRing),
      sectionsEquiv (scalar ⊗ₜ element) = (pullback.snd (structureMap ≫ coverMap) coverMap).appTop scalar * (pullback.fst (structureMap ≫ coverMap) coverMap).appTop element :=
    hP.tensorEquiv_tmul rfl rfl
  let ringCoaction : totalRing →+* coverRing ⊗[baseRing] totalRing := sectionsEquiv.symm.toRingHom.comp coaction.appTop.hom
  have ringCoaction_apply : ∀ element, sectionsEquiv (ringCoaction element) = coaction.appTop element := fun element ↦ by
    change sectionsEquiv (sectionsEquiv.symm _) = _
    rw [RingEquiv.apply_symm_apply]
  have hγv' : ∀ scalar, coaction.appTop (structureMap.appTop scalar) = (pullback.snd (structureMap ≫ coverMap) coverMap).appTop scalar := fun scalar ↦
    congr(((Scheme.Hom.appTop $coaction_over).hom) scalar)
  let algebraCoaction : totalRing →ₐ[coverRing] coverRing ⊗[baseRing] totalRing :=
    { ringCoaction with
      commutes' := fun scalar ↦ by
        change ringCoaction (algebraMap coverRing totalRing scalar) = algebraMap coverRing (coverRing ⊗[baseRing] totalRing) scalar
        apply sectionsEquiv.injective
        rw [ringCoaction_apply, Algebra.TensorProduct.algebraMap_apply, sectionsEquiv_tmul, map_one, mul_one]
        exact hγv' scalar }
  have algebraCoaction_apply : ∀ element, sectionsEquiv (algebraCoaction element) = coaction.appTop element := ringCoaction_apply
  have hd₁ : coactionUnit coverMap structureMap ≫ pullback.fst (structureMap ≫ coverMap) coverMap = 𝟙 _ := pullback.lift_fst _ _ _
  have hd₂ : coactionUnit coverMap structureMap ≫ pullback.snd (structureMap ≫ coverMap) coverMap = structureMap := pullback.lift_snd _ _ _
  have hmul : ∀ tensor : coverRing ⊗[baseRing] totalRing,
      Algebra.TensorProduct.mulMap baseRing coverRing totalRing tensor = (coactionUnit coverMap structureMap).appTop (sectionsEquiv tensor) := by
    intro tensor
    induction tensor using TensorProduct.induction_on with
    | zero => simp
    | tmul scalar element =>
      rw [sectionsEquiv_tmul, map_mul, Algebra.TensorProduct.mulMap_tmul, Algebra.smul_def]
      have first_eq : (coactionUnit coverMap structureMap).appTop ((pullback.snd (structureMap ≫ coverMap) coverMap).appTop scalar) = structureMap.appTop scalar :=
        congr(((Scheme.Hom.appTop $hd₂).hom) scalar)
      have second_eq : (coactionUnit coverMap structureMap).appTop ((pullback.fst (structureMap ≫ coverMap) coverMap).appTop element) = element :=
        congr(((Scheme.Hom.appTop $hd₁).hom) element)
      rw [first_eq, second_eq]
      rfl
    | add firstTensor tensor first_eq second_eq => simp only [map_add, first_eq, second_eq]
  have hcounit : ∀ element, Algebra.TensorProduct.mulMap baseRing coverRing totalRing (algebraCoaction element) = element := fun element ↦ by
    rw [hmul, algebraCoaction_apply]
    exact congr(((Scheme.Hom.appTop $counit).hom) element)
  let _ : Algebra baseRing Γ(pullback (structureMap ≫ coverMap) coverMap, ⊤) :=
    (pullback.snd (structureMap ≫ coverMap) coverMap ≫ coverMap).appTop.hom.toAlgebra
  have hP₂ := isPushout_appTop_of_flat coverMap (pullback.snd (structureMap ≫ coverMap) coverMap ≫ coverMap)
  let iteratedEquiv : coverRing ⊗[baseRing] Γ(pullback (structureMap ≫ coverMap) coverMap, ⊤) ≃+*
      Γ(pullback (pullback.snd (structureMap ≫ coverMap) coverMap ≫ coverMap) coverMap, ⊤) := hP₂.tensorEquiv rfl rfl
  have iteratedEquiv_tmul : ∀ (scalar : coverRing) (globalSection : Γ(pullback (structureMap ≫ coverMap) coverMap, ⊤)), iteratedEquiv (scalar ⊗ₜ globalSection) =
      (pullback.snd (pullback.snd (structureMap ≫ coverMap) coverMap ≫ coverMap) coverMap).appTop scalar *
        (pullback.fst (pullback.snd (structureMap ≫ coverMap) coverMap ≫ coverMap) coverMap).appTop globalSection :=
    hP₂.tensorEquiv_tmul rfl rfl
  let sectionsAlgEquiv : coverRing ⊗[baseRing] totalRing ≃ₐ[baseRing] Γ(pullback (structureMap ≫ coverMap) coverMap, ⊤) :=
    { sectionsEquiv with
      commutes' := fun baseScalar ↦ by
        change sectionsEquiv (algebraMap baseRing (coverRing ⊗[baseRing] totalRing) baseScalar) = algebraMap baseRing Γ(pullback (structureMap ≫ coverMap) coverMap, ⊤) baseScalar
        rw [Algebra.TensorProduct.algebraMap_apply, sectionsEquiv_tmul, map_one, mul_one]
        rfl }
  have sectionsAlgEquiv_apply : ∀ tensor, sectionsAlgEquiv tensor = sectionsEquiv tensor := fun _ ↦ rfl
  let iteratedMap : coverRing ⊗[baseRing] (coverRing ⊗[baseRing] totalRing) →+* Γ(pullback (pullback.snd (structureMap ≫ coverMap) coverMap ≫ coverMap) coverMap, ⊤) :=
    iteratedEquiv.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id baseRing coverRing) sectionsAlgEquiv.toAlgHom).toRingHom
  have iteratedMap_injective : Function.Injective iteratedMap := by
    have : ⇑iteratedMap = iteratedEquiv ∘ (Algebra.TensorProduct.congr (AlgEquiv.refl (R := baseRing) (A₁ := coverRing)) sectionsAlgEquiv) := by
      ext tensor
      simp [iteratedMap, Algebra.TensorProduct.congr_apply]
    rw [this]
    exact iteratedEquiv.injective.comp
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := baseRing) (A₁ := coverRing)) sectionsAlgEquiv).injective
  have iteratedMap_tmul : ∀ (scalar : coverRing) (tensor : coverRing ⊗[baseRing] totalRing), iteratedMap (scalar ⊗ₜ tensor) =
      (pullback.snd (pullback.snd (structureMap ≫ coverMap) coverMap ≫ coverMap) coverMap).appTop scalar *
        (pullback.fst (pullback.snd (structureMap ≫ coverMap) coverMap ≫ coverMap) coverMap).appTop (sectionsEquiv tensor) := by
    intro scalar tensor
    simp [iteratedMap, iteratedEquiv_tmul, sectionsAlgEquiv_apply]
  have hγ₁₂ : coactionMap coverMap structureMap coaction coaction_over ≫ pullback.snd (structureMap ≫ coverMap) coverMap =
      pullback.snd (pullback.snd (structureMap ≫ coverMap) coverMap ≫ coverMap) coverMap := by simp
  have hγ₁₁ : coactionMap coverMap structureMap coaction coaction_over ≫ pullback.fst (structureMap ≫ coverMap) coverMap = pullback.fst _ _ ≫ coaction := by simp
  have hπ₁₂ : coactionForget coverMap structureMap ≫ pullback.snd (structureMap ≫ coverMap) coverMap =
      pullback.snd (pullback.snd (structureMap ≫ coverMap) coverMap ≫ coverMap) coverMap := by simp
  have hπ₁₁ : coactionForget coverMap structureMap ≫ pullback.fst (structureMap ≫ coverMap) coverMap =
      pullback.fst _ _ ≫ pullback.fst (structureMap ≫ coverMap) coverMap := by simp
  have hΘδ : ∀ tensor, iteratedMap (Algebra.TensorProduct.map (AlgHom.id baseRing coverRing) (algebraCoaction.restrictScalars baseRing) tensor) =
      (coactionMap coverMap structureMap coaction coaction_over).appTop (sectionsEquiv tensor) := by
    intro tensor
    induction tensor using TensorProduct.induction_on with
    | zero => simp
    | tmul scalar element =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.restrictScalars_apply, iteratedMap_tmul,
        sectionsEquiv_tmul, map_mul, algebraCoaction_apply]
      congr 1
      · exact (congr(((Scheme.Hom.appTop $hγ₁₂).hom) scalar)).symm
      · exact (congr(((Scheme.Hom.appTop $hγ₁₁).hom) element)).symm
    | add firstTensor tensor first_eq second_eq => simp only [map_add, first_eq, second_eq]
  have hΘinc : ∀ tensor, iteratedMap (Algebra.TensorProduct.map (AlgHom.id baseRing coverRing)
      (Algebra.TensorProduct.includeRight (R := baseRing) (A := coverRing) (B := totalRing)) tensor) =
      (coactionForget coverMap structureMap).appTop (sectionsEquiv tensor) := by
    intro tensor
    induction tensor using TensorProduct.induction_on with
    | zero => simp
    | tmul scalar element =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply,
        iteratedMap_tmul, sectionsEquiv_tmul, sectionsEquiv_tmul, map_one, one_mul, map_mul]
      congr 1
      · exact (congr(((Scheme.Hom.appTop $hπ₁₂).hom) scalar)).symm
      · exact (congr(((Scheme.Hom.appTop $hπ₁₁).hom) element)).symm
    | add firstTensor tensor first_eq second_eq => simp only [map_add, first_eq, second_eq]
  have hcoassoc : ∀ element, Algebra.TensorProduct.map (AlgHom.id baseRing coverRing) (algebraCoaction.restrictScalars baseRing) (algebraCoaction element) =
      Algebra.TensorProduct.map (AlgHom.id baseRing coverRing) Algebra.TensorProduct.includeRight (algebraCoaction element) := by
    intro element
    apply iteratedMap_injective
    rw [hΘδ, hΘinc, algebraCoaction_apply]
    exact congr(((Scheme.Hom.appTop $coassociativity).hom) element)
  let datum : Algebra.DescentDatum baseRing coverRing totalRing := ⟨algebraCoaction, hcounit, hcoassoc⟩
  let invariants : Subalgebra baseRing totalRing := datum.descended
  let comparison : coverRing ⊗[baseRing] invariants ≃ₐ[coverRing] totalRing := datum.descendedEquiv
  have comparison_tmul : ∀ (scalar : coverRing) (element : invariants), comparison (scalar ⊗ₜ element) = scalar • (element : totalRing) := fun scalar element ↦ by
    change datum.descendedEquiv (scalar ⊗ₜ element) = _
    rw [datum.descendedEquiv_apply, datum.descendedMap_tmul]
  have hpush : IsPushout (CommRingCat.ofHom (algebraMap baseRing coverRing))
      (CommRingCat.ofHom (algebraMap baseRing invariants)) (CommRingCat.ofHom (algebraMap coverRing totalRing))
      (CommRingCat.ofHom (algebraMap invariants totalRing)) := by
    refine (CommRingCat.isPushout_tensorProduct baseRing coverRing invariants).of_iso (Iso.refl _) (Iso.refl _)
      (Iso.refl _) comparison.toRingEquiv.toCommRingCatIso (by simp) (by simp) ?_ ?_
    · ext scalar
      simp [comparison_tmul, Algebra.smul_def]
    · ext element
      simp [comparison_tmul]
  have hsq := isPullback_SpecMap_of_isPushout _ _ _ _ hpush
  have hiso : IsPullback coverScheme.isoSpec.inv (Spec.map (CommRingCat.ofHom (algebraMap baseRing coverRing)))
      coverMap base.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨(Scheme.isoSpec_inv_naturality coverMap).symm⟩
  have hQ := hsq.paste_horiz hiso
  have hjw : scheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap coverRing totalRing)) ≫ coverScheme.isoSpec.inv =
      structureMap := by
    rw [← Category.assoc]
    change scheme.toSpecΓ ≫ Spec.map structureMap.appTop ≫ coverScheme.isoSpec.inv = structureMap
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom,
      Iso.hom_inv_id, Category.comp_id]
  have hV : IsPullback scheme.toSpecΓ structureMap
      (Spec.map (CommRingCat.ofHom (algebraMap coverRing totalRing)) ≫ coverScheme.isoSpec.inv) (𝟙 coverScheme) :=
    IsPullback.of_horiz_isIso ⟨by rw [hjw, Category.comp_id]⟩
  refine ⟨Spec (.of invariants), Spec.map (CommRingCat.ofHom (algebraMap baseRing invariants)) ≫ base.isoSpec.inv,
    scheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap invariants totalRing)), ?_, ?_⟩
  · simpa using hV.paste_horiz hQ.flip
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc (pullback.fst _ _),
    Scheme.toSpecΓ_naturality, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext element
  have invariant_eq := datum.coaction_of_mem_descended element.2
  have := algebraCoaction_apply element
  rw [invariant_eq, sectionsEquiv_tmul, map_one, one_mul] at this
  exact this.symm

end AlgebraicGeometry
