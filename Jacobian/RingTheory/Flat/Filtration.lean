import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Tensor

/-!
# Flatness criteria from filtrations

Tensor-product injectivity can be checked successively along powers of an ideal.
These criteria give flatness near a prime and injectivity of multiplication by
an element which is regular on the closed fibre.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct LinearMap

universe universeLevel

namespace Module.Flat

variable {baseRing : Type universeLevel} {moduleType : Type*} [CommRing baseRing] [AddCommGroup moduleType] [Module baseRing moduleType] (ideal : Ideal baseRing)

lemma bijective_rTensor_mkQ_of_smul_eq_zero {auxiliaryModule : Type*} [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule]
    (hN : ∀ index ∈ ideal, ∀ degree : auxiliaryModule, index • degree = 0) :
    Function.Bijective ((ideal • (⊤ : Submodule baseRing moduleType)).mkQ.rTensor auxiliaryModule) := by
  refine ⟨?_, rTensor_surjective _ (Submodule.mkQ_surjective _)⟩
  rw [injective_iff_map_eq_zero]
  intro value hx
  have hex := _root_.rTensor_exact auxiliaryModule (LinearMap.exact_subtype_mkQ (ideal • (⊤ : Submodule baseRing moduleType)))
    (Submodule.mkQ_surjective _)
  obtain ⟨otherValue, rfl⟩ := (hex value).1 hx
  clear hx hex
  induction otherValue using TensorProduct.inductionOn with
  | add otherValue thirdValue hy hz => simp [hy, hz]
  | tmul moduleElement degree =>
    obtain ⟨moduleElement, hm⟩ := moduleElement
    simp only [rTensor_tmul, Submodule.subtype_apply]
    induction hm using Submodule.smul_induction_on' with
    | smul coefficient hr moduleElement _ => rw [smul_tmul, hN coefficient hr degree, tmul_zero]
    | add moduleElement _ m' _ condition h' => rw [add_tmul, condition, h', add_zero]

lemma lTensor_subtype_injective_of_smul_eq_zero
    [Flat (baseRing ⧸ ideal) (moduleType ⧸ ideal • (⊤ : Submodule baseRing moduleType))] {auxiliaryModule : Type*} [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule]
    (hN : ∀ index ∈ ideal, ∀ degree : auxiliaryModule, index • degree = 0) (N' : Submodule baseRing auxiliaryModule) :
    Function.Injective (N'.subtype.lTensor moduleType) := by
  set M' := moduleType ⧸ ideal • (⊤ : Submodule baseRing moduleType)
  have hN' : ∀ index ∈ ideal, ∀ degree : N', index • degree = 0 := fun index hi degree ↦ Subtype.ext (hN index hi degree)
  have h₁ := bijective_rTensor_mkQ_of_smul_eq_zero (moduleType := moduleType) ideal hN
  have h₂ := bijective_rTensor_mkQ_of_smul_eq_zero (moduleType := moduleType) ideal hN'
  have hcomm : (N'.subtype.lTensor M').comp ((ideal • (⊤ : Submodule baseRing moduleType)).mkQ.rTensor N') =
      ((ideal • (⊤ : Submodule baseRing moduleType)).mkQ.rTensor auxiliaryModule).comp (N'.subtype.lTensor moduleType) := by
    ext; rfl
  suffices condition : Function.Injective (N'.subtype.lTensor M') by
    intro value otherValue hxy
    apply h₂.1
    apply condition
    have hx := congr($hcomm value)
    have hy := congr($hcomm otherValue)
    simp only [LinearMap.comp_apply] at hx hy
    rw [hx, hy, hxy]
  have hNt : Module.IsTorsionBySet baseRing auxiliaryModule ideal := fun degree index ↦ hN index index.2 degree
  have hN't : Module.IsTorsionBySet baseRing N' ideal := fun degree index ↦ hN' index index.2 degree
  let := hNt.module
  let := hN't.module
  have hsurj : Function.Surjective (algebraMap baseRing (baseRing ⧸ ideal)) := Ideal.Quotient.mk_surjective
  have : CompatibleSMul baseRing (baseRing ⧸ ideal) M' auxiliaryModule := CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  have : CompatibleSMul baseRing (baseRing ⧸ ideal) M' N' := CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  let function : N' →ₗ[baseRing ⧸ ideal] auxiliaryModule :=
    { toFun := N'.subtype
      map_add' := by simp
      map_smul' := by
        rintro ⟨coefficient⟩ degree
        exact N'.subtype.map_smul coefficient degree }
  have hf : Function.Injective (function.lTensor M') :=
    Flat.lTensor_preserves_injective_linearMap function Subtype.val_injective
  let equivalence := equivOfCompatibleSMul baseRing (baseRing ⧸ ideal) baseRing M' auxiliaryModule
  let e' := equivOfCompatibleSMul baseRing (baseRing ⧸ ideal) baseRing M' N'
  have key : N'.subtype.lTensor M' = equivalence.toLinearMap ∘ₗ (function.lTensor M').restrictScalars baseRing ∘ₗ
      e'.symm.toLinearMap := by
    ext moduleElement degree
    rfl
  rw [key]
  simpa using hf

lemma lTensor_smul_top_subtype_injective {submodule : Type*} [AddCommGroup submodule] [Module baseRing submodule] [Flat baseRing submodule]
    (hI : Function.Injective (ideal.subtype.lTensor moduleType)) :
    Function.Injective ((ideal • (⊤ : Submodule baseRing submodule)).subtype.lTensor moduleType) := by

  let multiplierValue : ideal ⊗[baseRing] submodule →ₗ[baseRing] submodule := TensorProduct.lid baseRing submodule ∘ₗ ideal.subtype.rTensor submodule
  have hu : Function.Injective multiplierValue :=
    (TensorProduct.lid baseRing submodule).injective.comp (Flat.rTensor_preserves_injective_linearMap _
      Subtype.val_injective)
  have hrange : LinearMap.range multiplierValue = ideal • (⊤ : Submodule baseRing submodule) := by
    apply le_antisymm
    · rintro _ ⟨value, rfl⟩
      induction value using TensorProduct.inductionOn with
      | add value otherValue hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | tmul index function => exact Submodule.smul_mem_smul index.2 trivial
    · rw [Submodule.smul_le]
      intro index hi function _
      exact ⟨⟨index, hi⟩ ⊗ₜ function, by simp [multiplierValue]⟩
  let equivalence : ideal ⊗[baseRing] submodule ≃ₗ[baseRing] ↥(ideal • (⊤ : Submodule baseRing submodule)) :=
    (LinearEquiv.ofInjective multiplierValue hu).trans (LinearEquiv.ofEq _ _ hrange)

  let auxiliaryValue : moduleType ⊗[baseRing] (ideal ⊗[baseRing] submodule) →ₗ[baseRing] moduleType ⊗[baseRing] submodule :=
    (TensorProduct.rid baseRing moduleType).toLinearMap.rTensor submodule ∘ₗ (ideal.subtype.lTensor moduleType).rTensor submodule ∘ₗ
      (TensorProduct.assoc baseRing moduleType ideal submodule).symm.toLinearMap
  have hv : Function.Injective auxiliaryValue :=
    (Flat.rTensor_preserves_injective_linearMap _ (TensorProduct.rid baseRing moduleType).injective).comp
      ((Flat.rTensor_preserves_injective_linearMap _ hI).comp
        (TensorProduct.assoc baseRing moduleType ideal submodule).symm.injective)
  have hcomp : (ideal • (⊤ : Submodule baseRing submodule)).subtype.lTensor moduleType ∘ₗ equivalence.toLinearMap.lTensor moduleType = auxiliaryValue := by
    ext moduleElement index function
    simp [equivalence, multiplierValue, auxiliaryValue, LinearEquiv.ofInjective_apply, smul_tmul']
  have : (ideal • (⊤ : Submodule baseRing submodule)).subtype.lTensor moduleType =
      auxiliaryValue ∘ₗ (equivalence.symm.toLinearMap.lTensor moduleType) := by
    rw [← hcomp, LinearMap.comp_assoc, ← LinearMap.lTensor_comp]
    simp
  rw [this]
  exact hv.comp (LinearEquiv.injective (equivalence.symm.lTensor moduleType))

lemma lTensor_subtype_injective_of_flat
    (hQ : ∀ (auxiliaryModule : Type universeLevel) [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule], (∀ index ∈ ideal, ∀ degree : auxiliaryModule, index • degree = 0) →
      ∀ N' : Submodule baseRing auxiliaryModule, Function.Injective (N'.subtype.lTensor moduleType))
    {submodule : Type universeLevel} [AddCommGroup submodule] [Module baseRing submodule] [Flat baseRing submodule]
    (hI : Function.Injective (ideal.subtype.lTensor moduleType)) (residueRing : Submodule baseRing submodule)
    (hK : ideal • (⊤ : Submodule baseRing submodule) ≤ residueRing) :
    Function.Injective (residueRing.subtype.lTensor moduleType) := by
  set primeIdeal := ideal • (⊤ : Submodule baseRing submodule)
  let K' : Submodule baseRing (submodule ⧸ primeIdeal) := residueRing.map primeIdeal.mkQ
  let prime : residueRing →ₗ[baseRing] K' := (primeIdeal.mkQ.restrict fun value hx ↦ Submodule.mem_map_of_mem hx)
  have hq : Function.Surjective prime := by
    rintro ⟨_, value, hx, rfl⟩
    exact ⟨⟨value, hx⟩, rfl⟩
  have hex : Function.Exact (Submodule.inclusion hK) prime := by
    intro value
    constructor
    · intro condition
      have : (value : submodule) ∈ primeIdeal := by
        simpa [prime, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using congr(($condition : submodule ⧸ primeIdeal))
      exact ⟨⟨value, this⟩, rfl⟩
    · rintro ⟨otherValue, rfl⟩
      apply Subtype.ext
      simp [prime, (Submodule.Quotient.mk_eq_zero primeIdeal).mpr otherValue.2]
  have hkill : ∀ index ∈ ideal, ∀ degree : submodule ⧸ primeIdeal, index • degree = 0 := by
    intro index hi degree
    induction degree using Submodule.Quotient.induction_on with
    | H degree =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hi trivial
  have hQ' := hQ _ hkill K'
  have hP := lTensor_smul_top_subtype_injective ideal (submodule := submodule) hI
  rw [injective_iff_map_eq_zero]
  intro thirdValue hz
  have hcomm : K'.subtype ∘ₗ prime = primeIdeal.mkQ ∘ₗ residueRing.subtype := by ext; rfl
  have h1 : prime.lTensor moduleType thirdValue = 0 := by
    apply hQ'
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomm,
      LinearMap.lTensor_comp, LinearMap.comp_apply, hz, map_zero]
  obtain ⟨multiplierValue, rfl⟩ := ((_root_.lTensor_exact moduleType hex hq) thirdValue).1 h1
  have h2 : primeIdeal.subtype.lTensor moduleType multiplierValue = 0 := by
    rw [← hz, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    rfl
  rw [hP (h2.trans (map_zero _).symm), map_zero]

lemma lTensor_inclusion_injective_of_smul_le
    (hQ : ∀ (auxiliaryModule : Type universeLevel) [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule], (∀ index ∈ ideal, ∀ degree : auxiliaryModule, index • degree = 0) →
      ∀ N' : Submodule baseRing auxiliaryModule, Function.Injective (N'.subtype.lTensor moduleType))
    (hI : Function.Injective (ideal.subtype.lTensor moduleType)) {auxiliaryModule : Type universeLevel} [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule]
    {localizedModule L' : Submodule baseRing auxiliaryModule} (hLL' : localizedModule ≤ L')
    (hI' : ideal • L' ≤ localizedModule) : Function.Injective ((Submodule.inclusion hLL').lTensor moduleType) := by

  obtain ⟨submodule, _, _, _, φ, hφ⟩ : ∃ (submodule : Type universeLevel) (_ : AddCommGroup submodule) (_ : Module baseRing submodule)
      (_ : Flat baseRing submodule) (φ : submodule →ₗ[baseRing] L'), Function.Surjective φ :=
    ⟨L' →₀ baseRing, inferInstance, inferInstance, inferInstance, Finsupp.linearCombination baseRing id,
      fun value ↦ ⟨Finsupp.single value 1, by rw [Finsupp.linearCombination_single, one_smul]; rfl⟩⟩
  let L₀ : Submodule baseRing L' := localizedModule.comap L'.subtype
  let residueRing : Submodule baseRing submodule := L₀.comap φ
  have hK : ideal • (⊤ : Submodule baseRing submodule) ≤ residueRing := by
    rw [Submodule.smul_le]
    intro index hi function _
    change (φ (index • function) : auxiliaryModule) ∈ localizedModule
    rw [map_smul, Submodule.coe_smul]
    exact hI' (Submodule.smul_mem_smul hi (φ function).2)
  have hKinj := lTensor_subtype_injective_of_flat ideal hQ hI residueRing hK

  let eL : L₀ ≃ₗ[baseRing] localizedModule := Submodule.comapSubtypeEquivOfLe hLL'
  let φK : residueRing →ₗ[baseRing] L₀ := φ.restrict fun value hx ↦ hx
  have hφK : Function.Surjective φK := by
    rintro ⟨otherValue, hy⟩
    obtain ⟨value, rfl⟩ := hφ otherValue
    exact ⟨⟨value, hy⟩, rfl⟩
  have hcomm : (Submodule.inclusion hLL') ∘ₗ eL.toLinearMap = L₀.subtype := by
    ext value
    rfl
  suffices condition : Function.Injective (L₀.subtype.lTensor moduleType) by
    rw [← hcomm, LinearMap.lTensor_comp, LinearMap.coe_comp] at condition
    have := condition.of_comp
    rw [← LinearEquiv.coe_lTensor] at this
    intro value otherValue hxy
    obtain ⟨value, rfl⟩ := (eL.lTensor moduleType).surjective value
    obtain ⟨otherValue, rfl⟩ := (eL.lTensor moduleType).surjective otherValue
    rw [condition hxy]
  rw [injective_iff_map_eq_zero]
  intro thirdValue hz
  obtain ⟨exponent, rfl⟩ := LinearMap.lTensor_surjective moduleType hφK thirdValue
  have hsq : L₀.subtype ∘ₗ φK = φ ∘ₗ residueRing.subtype := by ext; rfl
  have hk : φ.lTensor moduleType (residueRing.subtype.lTensor moduleType exponent) = 0 := by
    rw [← LinearMap.comp_apply (φ.lTensor moduleType), ← LinearMap.lTensor_comp, ← hsq,
      LinearMap.lTensor_comp, LinearMap.comp_apply, hz]
  have hexφ : Function.Exact (LinearMap.ker φ).subtype φ := LinearMap.exact_subtype_ker_map φ
  obtain ⟨witness, hw⟩ := ((_root_.lTensor_exact moduleType hexφ hφ) _).1 hk
  have hle : LinearMap.ker φ ≤ residueRing := fun value hx ↦ by
    change φ value ∈ L₀
    rw [LinearMap.mem_ker.mp hx]
    exact zero_mem _
  have hk' : exponent = (Submodule.inclusion hle).lTensor moduleType witness := by
    apply hKinj
    rw [← hw, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    rfl
  have hzero : φK ∘ₗ Submodule.inclusion hle = 0 := by
    ext value
    exact congr(($(LinearMap.mem_ker.mp value.2) : auxiliaryModule))
  rw [hk', ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hzero]
  simp

lemma map_eq_zero_of_lTensor_subtype_eq_zero_of_flat
    (hQ : ∀ (auxiliaryModule : Type universeLevel) [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule], (∀ index ∈ ideal, ∀ degree : auxiliaryModule, index • degree = 0) →
      ∀ N' : Submodule baseRing auxiliaryModule, Function.Injective (N'.subtype.lTensor moduleType))
    {submodule : Type universeLevel} [AddCommGroup submodule] [Module baseRing submodule] [Flat baseRing submodule] (residueRing : Submodule baseRing submodule)
    (hK : ideal • (⊤ : Submodule baseRing submodule) ≤ residueRing) {ambientScheme : Type*} [AddCommGroup ambientScheme] [Module baseRing ambientScheme]
    (ψ : moduleType ⊗[baseRing] residueRing →ₗ[baseRing] ambientScheme)
    (hψ : ∀ exponent : moduleType ⊗[baseRing] ideal, TensorProduct.rid baseRing moduleType (ideal.subtype.lTensor moduleType exponent) = 0 → ∀ function : submodule,
      ψ ((((toSpanSingleton baseRing submodule function) ∘ₗ ideal.subtype).codRestrict residueRing
        fun index ↦ hK (Submodule.smul_mem_smul index.2 trivial)).lTensor moduleType exponent) = 0)
    (thirdValue : moduleType ⊗[baseRing] residueRing) (hz : residueRing.subtype.lTensor moduleType thirdValue = 0) : ψ thirdValue = 0 := by
  set primeIdeal := ideal • (⊤ : Submodule baseRing submodule)
  let K' : Submodule baseRing (submodule ⧸ primeIdeal) := residueRing.map primeIdeal.mkQ
  let prime : residueRing →ₗ[baseRing] K' := (primeIdeal.mkQ.restrict fun value hx ↦ Submodule.mem_map_of_mem hx)
  have hq : Function.Surjective prime := by
    rintro ⟨_, value, hx, rfl⟩
    exact ⟨⟨value, hx⟩, rfl⟩
  have hex : Function.Exact (Submodule.inclusion hK) prime := by
    intro value
    constructor
    · intro condition
      have : (value : submodule) ∈ primeIdeal := by
        simpa [prime, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using congr(($condition : submodule ⧸ primeIdeal))
      exact ⟨⟨value, this⟩, rfl⟩
    · rintro ⟨otherValue, rfl⟩
      apply Subtype.ext
      simp [prime, (Submodule.Quotient.mk_eq_zero primeIdeal).mpr otherValue.2]
  have hkill : ∀ index ∈ ideal, ∀ degree : submodule ⧸ primeIdeal, index • degree = 0 := by
    intro index hi degree
    induction degree using Submodule.Quotient.induction_on with
    | H degree =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hi trivial
  have hQ' := hQ _ hkill K'
  have hcomm : K'.subtype ∘ₗ prime = primeIdeal.mkQ ∘ₗ residueRing.subtype := by ext; rfl
  have h1 : prime.lTensor moduleType thirdValue = 0 := by
    apply hQ'
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomm,
      LinearMap.lTensor_comp, LinearMap.comp_apply, hz, map_zero]
  obtain ⟨multiplierValue, rfl⟩ := ((_root_.lTensor_exact moduleType hex hq) thirdValue).1 h1
  have h2 : primeIdeal.subtype.lTensor moduleType multiplierValue = 0 := by
    rw [← hz, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    rfl

  let ν : ideal ⊗[baseRing] submodule →ₗ[baseRing] primeIdeal := (TensorProduct.lid baseRing submodule ∘ₗ ideal.subtype.rTensor submodule).codRestrict primeIdeal
    fun value ↦ by
      induction value using TensorProduct.inductionOn with
      | add value otherValue hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | tmul index function => exact Submodule.smul_mem_smul index.2 trivial
  have hν : Function.Surjective ν := by
    rintro ⟨otherValue, hy⟩
    induction hy using Submodule.smul_induction_on' with
    | smul index hi function _ => exact ⟨⟨index, hi⟩ ⊗ₜ function, rfl⟩
    | add value hx otherValue hy hx' hy' =>
      obtain ⟨factor, ha⟩ := hx'
      obtain ⟨otherFactor, hb⟩ := hy'
      exact ⟨factor + otherFactor, by rw [map_add, ha, hb]; rfl⟩
  obtain ⟨auxiliaryValue, rfl⟩ := LinearMap.lTensor_surjective moduleType hν multiplierValue
  set μ : moduleType ⊗[baseRing] ideal →ₗ[baseRing] moduleType := (TensorProduct.rid baseRing moduleType).toLinearMap ∘ₗ ideal.subtype.lTensor moduleType
  have hΦ : (primeIdeal.subtype ∘ₗ ν).lTensor moduleType ∘ₗ (TensorProduct.assoc baseRing moduleType ideal submodule).toLinearMap =
      μ.rTensor submodule := by
    ext moduleElement index function
    simp [ν, μ, smul_tmul]
  have hΨ : μ.rTensor submodule ((TensorProduct.assoc baseRing moduleType ideal submodule).symm auxiliaryValue) = 0 := by
    rw [← hΦ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LinearMap.lTensor_comp, LinearMap.comp_apply, h2]
  have hexμ : Function.Exact (LinearMap.ker μ).subtype μ := LinearMap.exact_subtype_ker_map μ
  obtain ⟨witness, hw⟩ := ((rTensor_exact submodule hexμ) _).1 hΨ
  rw [← LinearEquiv.apply_symm_apply (TensorProduct.assoc baseRing moduleType ideal submodule) auxiliaryValue, ← hw]
  have key (parameter : moduleType ⊗[baseRing] ideal) (function : submodule) :
      (Submodule.inclusion hK).lTensor moduleType (ν.lTensor moduleType (TensorProduct.assoc baseRing moduleType ideal submodule (parameter ⊗ₜ function))) =
        (((toSpanSingleton baseRing submodule function) ∘ₗ ideal.subtype).codRestrict residueRing
          fun index ↦ hK (Submodule.smul_mem_smul index.2 trivial)).lTensor moduleType parameter := by
    induction parameter using TensorProduct.inductionOn with
    | add value otherValue hx hy => rw [add_tmul, map_add, map_add, map_add, hx, hy, map_add]
    | tmul moduleElement index => rfl
  clear hw
  induction witness using TensorProduct.inductionOn with
  | add value otherValue hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul exponent function =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, key]
    exact hψ exponent exponent.2 function

private lemma exists_lTensor_ker_preimage
    {baseAlgebra targetAlgebra : Type*} [AddCommGroup baseAlgebra] [AddCommGroup targetAlgebra]
    [Module baseRing baseAlgebra] [Module baseRing targetAlgebra]
    (localizer : baseAlgebra →ₗ[baseRing] targetAlgebra) (hg : Function.Surjective localizer)
    (value : moduleType ⊗[baseRing] baseAlgebra) (hx : localizer.lTensor moduleType value = 0) :
    ∃ witness : moduleType ⊗[baseRing] (LinearMap.ker localizer), (LinearMap.ker localizer).subtype.lTensor moduleType witness = value := by
  have hex : Function.Exact ((LinearMap.ker localizer).subtype.lTensor moduleType) (localizer.lTensor moduleType) :=
    _root_.lTensor_exact (R := baseRing) (M := ↥(LinearMap.ker localizer)) (N := baseAlgebra) (P := targetAlgebra)
      (f := (LinearMap.ker localizer).subtype) (g := localizer) moduleType
      (LinearMap.exact_subtype_ker_map localizer) hg
  exact (hex value).1 hx

theorem lTensor_subtype_injective_of_forall_ker
    (hQ : ∀ (auxiliaryModule : Type universeLevel) [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule], (∀ index ∈ ideal, ∀ degree : auxiliaryModule, index • degree = 0) →
      ∀ N' : Submodule baseRing auxiliaryModule, Function.Injective (N'.subtype.lTensor moduleType))
    {auxiliaryModule : Type universeLevel} [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule] (localizedModule : Submodule baseRing auxiliaryModule)
    (hL : ideal • (⊤ : Submodule baseRing auxiliaryModule) ≤ localizedModule)
    (hK : ∀ exponent : moduleType ⊗[baseRing] ideal, TensorProduct.rid baseRing moduleType (ideal.subtype.lTensor moduleType exponent) = 0 → ∀ degree : auxiliaryModule,
      (((toSpanSingleton baseRing auxiliaryModule degree) ∘ₗ ideal.subtype).codRestrict localizedModule
        fun index ↦ hL (Submodule.smul_mem_smul index.2 trivial)).lTensor moduleType exponent = 0) :
    Function.Injective (localizedModule.subtype.lTensor moduleType) := by
  let submodule := auxiliaryModule →₀ baseRing
  let φ : submodule →ₗ[baseRing] auxiliaryModule := Finsupp.linearCombination baseRing id
  have hφ : Function.Surjective φ := fun value ↦
    ⟨Finsupp.single value 1, by rw [Finsupp.linearCombination_single, one_smul]; rfl⟩
  let LF : Submodule baseRing submodule := localizedModule.comap φ
  have hLF : ideal • (⊤ : Submodule baseRing submodule) ≤ LF := by
    rw [Submodule.smul_le]
    intro index hi function _
    change φ (index • function) ∈ localizedModule
    rw [map_smul]
    exact hL (Submodule.smul_mem_smul hi trivial)
  let φL : LF →ₗ[baseRing] localizedModule := φ.restrict fun value hx ↦ hx
  have hφL : Function.Surjective φL := by
    rintro ⟨otherValue, hy⟩
    obtain ⟨value, rfl⟩ := hφ otherValue
    exact ⟨⟨value, hy⟩, rfl⟩
  rw [injective_iff_map_eq_zero]
  intro value hx
  obtain ⟨otherValue, rfl⟩ := LinearMap.lTensor_surjective moduleType hφL value
  have hsq : localizedModule.subtype ∘ₗ φL = φ ∘ₗ LF.subtype := by ext; rfl
  have hz : φ.lTensor moduleType (LF.subtype.lTensor moduleType otherValue) = 0 := by
    rw [← LinearMap.comp_apply (φ.lTensor moduleType), ← LinearMap.lTensor_comp, ← hsq,
      LinearMap.lTensor_comp, LinearMap.comp_apply, hx]
  obtain ⟨witness, hw⟩ := exists_lTensor_ker_preimage (baseRing := baseRing)
    (moduleType := moduleType) (baseAlgebra := submodule) (targetAlgebra := auxiliaryModule)
    φ hφ (LF.subtype.lTensor moduleType otherValue) hz
  have hle : LinearMap.ker φ ≤ LF := fun value hx ↦ by
    change φ value ∈ localizedModule
    rw [LinearMap.mem_ker.mp hx]
    exact zero_mem _
  have hzero : φL ∘ₗ Submodule.inclusion hle = 0 := by
    ext value
    exact congr(($(LinearMap.mem_ker.mp value.2) : auxiliaryModule))
  have hw' : φL.lTensor moduleType ((Submodule.inclusion hle).lTensor moduleType witness) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hzero]
    simp
  have hdiff : LF.subtype.lTensor moduleType (otherValue - (Submodule.inclusion hle).lTensor moduleType witness) = 0 := by
    rw [map_sub, sub_eq_zero, ← hw, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    rfl
  have := map_eq_zero_of_lTensor_subtype_eq_zero_of_flat ideal hQ LF hLF (φL.lTensor moduleType)
    (fun exponent hk function ↦ by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      convert hK exponent hk (φ function) using 3
      ext index
      simp [φL, φ, LinearMap.restrict_apply])
    _ hdiff
  rwa [map_sub, hw', sub_zero] at this

lemma lTensor_subtype_injective_of_pow_le
    (hQ : ∀ (auxiliaryModule : Type universeLevel) [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule], (∀ index ∈ ideal, ∀ degree : auxiliaryModule, index • degree = 0) →
      ∀ N' : Submodule baseRing auxiliaryModule, Function.Injective (N'.subtype.lTensor moduleType))
    (hI : Function.Injective (ideal.subtype.lTensor moduleType))
    (degree : ℕ) {localizedModule : Ideal baseRing} (hL : ideal ^ degree ≤ localizedModule) : Function.Injective (localizedModule.subtype.lTensor moduleType) := by
  induction degree generalizing localizedModule with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, top_le_iff] at hL
    subst hL
    have : (⊤ : Ideal baseRing).subtype = (LinearEquiv.ofTop (⊤ : Ideal baseRing) rfl).toLinearMap := rfl
    rw [this, ← LinearEquiv.coe_lTensor]
    exact LinearEquiv.injective _
  | succ degree ih =>
    have hle : localizedModule ≤ localizedModule ⊔ ideal ^ degree := le_sup_left
    have hsmul : ideal • (localizedModule ⊔ ideal ^ degree) ≤ localizedModule := by
      rw [Submodule.smul_sup, smul_eq_mul, smul_eq_mul, ← pow_succ']
      exact sup_le (Ideal.mul_le.mpr fun factor _ otherFactor hb ↦ localizedModule.mul_mem_left factor hb) hL
    have h₁ := ih (localizedModule := localizedModule ⊔ ideal ^ degree) le_sup_right
    have h₂ := lTensor_inclusion_injective_of_smul_le ideal hQ hI hle hsmul
    have : localizedModule.subtype = (localizedModule ⊔ ideal ^ degree).subtype ∘ₗ Submodule.inclusion hle := rfl
    rw [this, LinearMap.lTensor_comp, LinearMap.coe_comp]
    exact h₁.comp h₂

lemma range_lTensor_smul_top_subtype_le {auxiliaryModule : Type*} [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule]
    (baseIdeal : Ideal baseRing) :
    LinearMap.range ((baseIdeal • (⊤ : Submodule baseRing auxiliaryModule)).subtype.lTensor moduleType) ≤
      baseIdeal • (⊤ : Submodule baseRing (moduleType ⊗[baseRing] auxiliaryModule)) := by
  rintro _ ⟨value, rfl⟩
  induction value using TensorProduct.inductionOn with
  | add value otherValue hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul moduleElement degree =>
    obtain ⟨degree, hn⟩ := degree
    simp only [lTensor_tmul, Submodule.subtype_apply]
    induction hn using Submodule.smul_induction_on' with
    | smul coefficient hr degree _ =>
      rw [tmul_smul]
      exact Submodule.smul_mem_smul hr trivial
    | add degree _ n' _ condition h' => rw [tmul_add]; exact Submodule.add_mem _ condition h'

/-- A tensor injectivity criterion for flatness using an ideal in the Jacobson radical. -/
theorem of_lTensor_injective_of_forall {algebraRing : Type*} [CommRing algebraRing] [Algebra baseRing algebraRing]
    [IsNoetherianRing baseRing] [IsNoetherianRing algebraRing] [Module algebraRing moduleType] [IsScalarTower baseRing algebraRing moduleType]
    [Module.Finite algebraRing moduleType] (hIS : ideal.map (algebraMap baseRing algebraRing) ≤ Ideal.jacobson ⊥)
    (hQ : ∀ (auxiliaryModule : Type universeLevel) [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule], (∀ index ∈ ideal, ∀ degree : auxiliaryModule, index • degree = 0) →
      ∀ N' : Submodule baseRing auxiliaryModule, Function.Injective (N'.subtype.lTensor moduleType))
    (hI : Function.Injective (ideal.subtype.lTensor moduleType)) : Flat baseRing moduleType := by
  rw [iff_lTensor_injective']
  intro baseIdeal
  rw [injective_iff_map_eq_zero]
  intro value hx

  have step1 (degree : ℕ) :
      value ∈ LinearMap.range ((Submodule.comap baseIdeal.subtype (ideal ^ degree)).subtype.lTensor moduleType) := by
    set localizedModule := baseIdeal ⊔ ideal ^ degree
    have hJL : baseIdeal ≤ localizedModule := le_sup_left
    have hL := lTensor_subtype_injective_of_pow_le ideal hQ hI degree
      (localizedModule := localizedModule) le_sup_right
    have h0 : (Submodule.inclusion hJL).lTensor moduleType value = 0 := by
      apply hL
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, map_zero]
      exact hx
    let π : baseIdeal →ₗ[baseRing] baseRing ⧸ ideal ^ degree := (ideal ^ degree).mkQ ∘ₗ baseIdeal.subtype
    let πJ : baseIdeal →ₗ[baseRing] LinearMap.range π := π.rangeRestrict
    have hπJ : Function.Surjective πJ := LinearMap.surjective_rangeRestrict π
    have hrange : ∀ otherValue : localizedModule, (ideal ^ degree).mkQ (otherValue : baseRing) ∈ LinearMap.range π := by
      rintro ⟨otherValue, hy⟩
      obtain ⟨factor, ha, otherFactor, hb, rfl⟩ := Submodule.mem_sup.mp hy
      refine ⟨⟨factor, ha⟩, ?_⟩
      simp [π, Ideal.Quotient.eq_zero_iff_mem.mpr hb]
    let πL : localizedModule →ₗ[baseRing] LinearMap.range π :=
      ((ideal ^ degree).mkQ ∘ₗ localizedModule.subtype).codRestrict _ hrange
    have hfac : πJ = πL ∘ₗ Submodule.inclusion hJL := rfl
    have hex : Function.Exact (Submodule.comap baseIdeal.subtype (ideal ^ degree)).subtype πJ := by
      rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]
      ext otherValue
      simp [π, Ideal.Quotient.eq_zero_iff_mem]
    apply ((_root_.lTensor_exact moduleType hex hπJ) value).1
    rw [hfac, LinearMap.lTensor_comp, LinearMap.comp_apply, h0, map_zero]

  obtain ⟨exponent, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul ideal baseIdeal
  have step2 (degree : ℕ) : value ∈ ideal ^ degree • (⊤ : Submodule baseRing (moduleType ⊗[baseRing] baseIdeal)) := by
    have hle : Submodule.comap baseIdeal.subtype (ideal ^ (degree + exponent)) ≤ ideal ^ degree • (⊤ : Submodule baseRing baseIdeal) := by
      intro otherValue hy
      have hy' : (otherValue : baseRing) ∈ ideal ^ (degree + exponent) • (⊤ : Ideal baseRing) ⊓ baseIdeal := by
        simpa [smul_eq_mul, Ideal.mul_top] using hy
      rw [hk _ (Nat.le_add_left exponent degree), Nat.add_sub_cancel] at hy'
      have hy'' : (otherValue : baseRing) ∈ Submodule.map baseIdeal.subtype (ideal ^ degree • (⊤ : Submodule baseRing baseIdeal)) := by
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
        exact Submodule.smul_mono le_rfl inf_le_right hy'
      obtain ⟨thirdValue, hz, hzy⟩ := hy''
      rwa [← Subtype.ext hzy]
    obtain ⟨otherValue, rfl⟩ := step1 (degree + exponent)
    have : (Submodule.comap baseIdeal.subtype (ideal ^ (degree + exponent))).subtype =
        (ideal ^ degree • (⊤ : Submodule baseRing baseIdeal)).subtype ∘ₗ Submodule.inclusion hle := rfl
    rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply]
    exact range_lTensor_smul_top_subtype_le (ideal ^ degree) ⟨_, rfl⟩

  have : Module.Finite baseRing baseIdeal := IsNoetherian.finite baseRing baseIdeal
  have hfin : Module.Finite algebraRing (moduleType ⊗[baseRing] baseIdeal) :=
    Module.Finite.equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange baseRing algebraRing algebraRing moduleType baseIdeal)
  have hkrull := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := moduleType ⊗[baseRing] baseIdeal) _ hIS
  have : value ∈ (⨅ index : ℕ, ideal.map (algebraMap baseRing algebraRing) ^ index • ⊤ : Submodule algebraRing (moduleType ⊗[baseRing] baseIdeal)) := by
    rw [Submodule.mem_iInf]
    intro degree
    have condition := step2 degree
    rw [← Ideal.map_pow]
    refine Submodule.smul_induction_on condition (fun coefficient hr otherValue _ ↦ ?_) (fun _ _ ↦ Submodule.add_mem _)
    rw [← algebraMap_smul algebraRing coefficient otherValue]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
  rwa [hkrull] at this

/-- Flatness follows from a flat quotient and injectivity on ideals containing the defining ideal. -/
theorem of_flat_quotient_of_lTensor_injective {algebraRing : Type*} [CommRing algebraRing] [Algebra baseRing algebraRing]
    [IsNoetherianRing baseRing] [IsNoetherianRing algebraRing] [Module algebraRing moduleType] [IsScalarTower baseRing algebraRing moduleType]
    [Module.Finite algebraRing moduleType] [Flat (baseRing ⧸ ideal) (moduleType ⧸ ideal • (⊤ : Submodule baseRing moduleType))]
    (hIS : ideal.map (algebraMap baseRing algebraRing) ≤ Ideal.jacobson ⊥)
    (hI : Function.Injective (ideal.subtype.lTensor moduleType)) : Flat baseRing moduleType :=
  of_lTensor_injective_of_forall ideal hIS
    (fun _ _ _ hN N' ↦ lTensor_subtype_injective_of_smul_eq_zero ideal hN N') hI

section Element

variable {algebraRing : Type*} [CommRing algebraRing] [Algebra baseRing algebraRing] [Module algebraRing moduleType] [IsScalarTower baseRing algebraRing moduleType]

private lemma rTensor_toLinearMap_injective_of_smul_eq_zero [Flat baseRing moduleType] [ideal.IsMaximal] (scalar : algebraRing)
    (hs : ∀ moduleElement : moduleType, scalar • moduleElement ∈ ideal • (⊤ : Submodule baseRing moduleType) → moduleElement ∈ ideal • (⊤ : Submodule baseRing moduleType))
    {auxiliaryModule : Type*} [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule] (hN : ∀ index ∈ ideal, ∀ degree : auxiliaryModule, index • degree = 0) :
    Function.Injective ((DistribSMul.toLinearMap baseRing moduleType scalar).rTensor auxiliaryModule) := by
  let := Ideal.Quotient.field ideal
  set primeIdeal := ideal • (⊤ : Submodule baseRing moduleType)
  set φ := DistribSMul.toLinearMap baseRing moduleType scalar
  have hφP : primeIdeal ≤ primeIdeal.comap φ := by
    rw [Submodule.smul_le]
    intro index hi moduleElement _
    change scalar • (index • moduleElement) ∈ primeIdeal
    rw [smul_comm]
    exact Submodule.smul_mem_smul hi trivial
  let φ' : (moduleType ⧸ primeIdeal) →ₗ[baseRing] (moduleType ⧸ primeIdeal) := primeIdeal.mapQ primeIdeal φ hφP
  have hφ' : Function.Injective φ' := by
    rw [injective_iff_map_eq_zero]
    intro value hx
    induction value using Submodule.Quotient.induction_on with
    | H moduleElement =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.Quotient.mk_eq_zero]
      exact hs moduleElement hx
  have hβ := bijective_rTensor_mkQ_of_smul_eq_zero (moduleType := moduleType) ideal hN
  have hcomm : (primeIdeal.mkQ.rTensor auxiliaryModule).comp (φ.rTensor auxiliaryModule) = (φ'.rTensor auxiliaryModule).comp (primeIdeal.mkQ.rTensor auxiliaryModule) := by
    ext; rfl
  suffices condition : Function.Injective (φ'.rTensor auxiliaryModule) by
    have := condition.comp hβ.1
    rw [← LinearMap.coe_comp, ← hcomm, LinearMap.coe_comp] at this
    exact this.of_comp
  have hNt : Module.IsTorsionBySet baseRing auxiliaryModule ideal := fun degree index ↦ hN index index.2 degree
  let := hNt.module
  have hsurj : Function.Surjective (algebraMap baseRing (baseRing ⧸ ideal)) := Ideal.Quotient.mk_surjective
  have : CompatibleSMul baseRing (baseRing ⧸ ideal) (moduleType ⧸ primeIdeal) auxiliaryModule :=
    CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  let ψ : (moduleType ⧸ primeIdeal) →ₗ[baseRing ⧸ ideal] (moduleType ⧸ primeIdeal) :=
    { toFun := φ'
      map_add' := by simp
      map_smul' := by
        rintro ⟨coefficient⟩ degree
        exact φ'.map_smul coefficient degree }
  have : Module.Free (baseRing ⧸ ideal) auxiliaryModule := Module.Free.of_divisionRing _ _
  have hψ : Function.Injective (ψ.rTensor auxiliaryModule) :=
    Flat.rTensor_preserves_injective_linearMap ψ hφ'
  let equivalence := equivOfCompatibleSMul baseRing (baseRing ⧸ ideal) baseRing (moduleType ⧸ primeIdeal) auxiliaryModule
  have key : φ'.rTensor auxiliaryModule = equivalence.toLinearMap ∘ₗ (ψ.rTensor auxiliaryModule).restrictScalars baseRing ∘ₗ
      equivalence.symm.toLinearMap := by
    ext moduleElement degree
    rfl
  rw [key]
  simpa using hψ

/-- An element regular on the closed fibre acts injectively after tensoring a finite flat module. -/
theorem rTensor_toLinearMap_injective [IsNoetherianRing algebraRing] [Module.Finite algebraRing moduleType] [Flat baseRing moduleType]
    [ideal.IsMaximal] (hIS : ideal.map (algebraMap baseRing algebraRing) ≤ Ideal.jacobson ⊥) (scalar : algebraRing)
    (hs : ∀ moduleElement : moduleType, scalar • moduleElement ∈ ideal • (⊤ : Submodule baseRing moduleType) → moduleElement ∈ ideal • (⊤ : Submodule baseRing moduleType))
    (auxiliaryModule : Type*) [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule] [Module.Finite baseRing auxiliaryModule] :
    Function.Injective ((DistribSMul.toLinearMap baseRing moduleType scalar).rTensor auxiliaryModule) := by
  set φ := DistribSMul.toLinearMap baseRing moduleType scalar

  have step1 (degree : ℕ) : ∀ (auxiliaryModule : Type u_3) [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule],
      (∀ index ∈ ideal ^ degree, ∀ value : auxiliaryModule, index • value = 0) → Function.Injective (φ.rTensor auxiliaryModule) := by
    induction degree with
    | zero =>
      intro auxiliaryModule _ _ hN
      have : Subsingleton auxiliaryModule := ⟨fun value otherValue ↦ by
        rw [← one_smul baseRing value, ← one_smul baseRing otherValue, hN 1 (by simp) value, hN 1 (by simp) otherValue]⟩
      intro value otherValue _
      exact Subsingleton.elim _ _
    | succ degree ih =>
      intro auxiliaryModule _ _ hN
      set N₁ := ideal • (⊤ : Submodule baseRing auxiliaryModule)
      have hN₁ : ∀ index ∈ ideal ^ degree, ∀ value : N₁, index • value = 0 := by
        rintro index hi ⟨value, hx⟩
        apply Subtype.ext
        change index • value = 0
        induction hx using Submodule.smul_induction_on' with
        | smul coefficient hr value _ =>
          rw [smul_smul]
          exact hN _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hi hr) value
        | add value _ otherValue _ hx hy => rw [smul_add, hx, hy, add_zero]
      have hN₂ : ∀ index ∈ ideal, ∀ value : auxiliaryModule ⧸ N₁, index • value = 0 := by
        intro index hi value
        induction value using Submodule.Quotient.induction_on with
        | H value =>
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          exact Submodule.smul_mem_smul hi trivial
      have h₁ := ih N₁ hN₁
      have h₂ := rTensor_toLinearMap_injective_of_smul_eq_zero ideal scalar hs hN₂
      have hinc : Function.Injective (N₁.subtype.lTensor moduleType) :=
        Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
      have hex := _root_.lTensor_exact moduleType (LinearMap.exact_subtype_mkQ N₁)
        (Submodule.mkQ_surjective N₁)
      rw [injective_iff_map_eq_zero]
      intro value hx
      have hx' : φ.rTensor _ (N₁.mkQ.lTensor moduleType value) = 0 := by
        rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
          ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hx, map_zero]
      obtain ⟨otherValue, rfl⟩ := (hex value).1 (h₂ (hx'.trans (map_zero _).symm))
      have hy : φ.rTensor _ otherValue = 0 := by
        apply hinc
        rw [map_zero, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
          ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hx]
      rw [h₁ (hy.trans (map_zero _).symm), map_zero]

  rw [injective_iff_map_eq_zero]
  intro value hx
  have h2 (degree : ℕ) : value ∈ ideal ^ degree • (⊤ : Submodule baseRing (moduleType ⊗[baseRing] auxiliaryModule)) := by
    set Nn := ideal ^ degree • (⊤ : Submodule baseRing auxiliaryModule)
    have hNn : ∀ index ∈ ideal ^ degree, ∀ otherValue : auxiliaryModule ⧸ Nn, index • otherValue = 0 := by
      intro index hi otherValue
      induction otherValue using Submodule.Quotient.induction_on with
      | H otherValue =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul hi trivial
    have hinj := step1 degree (auxiliaryModule ⧸ Nn) hNn
    have hex := _root_.lTensor_exact moduleType (LinearMap.exact_subtype_mkQ Nn)
      (Submodule.mkQ_surjective Nn)
    have h0 : Nn.mkQ.lTensor moduleType value = 0 := by
      apply hinj
      rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hx, map_zero]
    obtain ⟨otherValue, rfl⟩ := (hex value).1 h0
    exact range_lTensor_smul_top_subtype_le (ideal ^ degree) ⟨otherValue, rfl⟩
  have hfin : Module.Finite algebraRing (moduleType ⊗[baseRing] auxiliaryModule) :=
    Module.Finite.equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange baseRing algebraRing algebraRing moduleType auxiliaryModule)
  have hkrull := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := moduleType ⊗[baseRing] auxiliaryModule) _ hIS
  have : value ∈ (⨅ index : ℕ, ideal.map (algebraMap baseRing algebraRing) ^ index • ⊤ : Submodule algebraRing (moduleType ⊗[baseRing] auxiliaryModule)) := by
    rw [Submodule.mem_iInf]
    intro degree
    rw [← Ideal.map_pow]
    refine Submodule.smul_induction_on (h2 degree) (fun coefficient hr otherValue _ ↦ ?_)
      (fun _ _ ↦ Submodule.add_mem _)
    rw [← algebraMap_smul algebraRing coefficient otherValue]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
  rwa [hkrull] at this

end Element

lemma exists_rid_lTensor_eq_of_mem_smul_top {moduleElement : moduleType} (hm : moduleElement ∈ ideal • (⊤ : Submodule baseRing moduleType)) :
    ∃ otherValue : moduleType ⊗[baseRing] ideal, TensorProduct.rid baseRing moduleType (ideal.subtype.lTensor moduleType otherValue) = moduleElement := by
  induction hm using Submodule.smul_induction_on' with
  | smul coefficient hr moduleElement _ => exact ⟨moduleElement ⊗ₜ ⟨coefficient, hr⟩, by simp⟩
  | add moduleElement _ m' _ condition h' =>
    obtain ⟨otherValue, hy⟩ := condition
    obtain ⟨y', hy'⟩ := h'
    exact ⟨otherValue + y', by rw [map_add, map_add, hy, hy']⟩

/-- A quotient of a flat module by an endomorphism is flat when that endomorphism stays injective
modulo every ideal. -/
theorem quotient_range [Flat baseRing moduleType] (φ : moduleType →ₗ[baseRing] moduleType)
    (condition : ∀ (baseIdeal : Ideal baseRing) (moduleElement : moduleType), φ moduleElement ∈ baseIdeal • (⊤ : Submodule baseRing moduleType) → moduleElement ∈ baseIdeal • (⊤ : Submodule baseRing moduleType)) :
    Flat baseRing (moduleType ⧸ LinearMap.range φ) := by
  rw [iff_lTensor_injective']
  intro baseIdeal
  set quotientAlgebra := moduleType ⧸ LinearMap.range φ
  set π := (LinearMap.range φ).mkQ
  have hnat (otherValue : moduleType ⊗[baseRing] baseIdeal) : π (TensorProduct.rid baseRing moduleType (baseIdeal.subtype.lTensor moduleType otherValue)) =
      TensorProduct.rid baseRing quotientAlgebra (baseIdeal.subtype.lTensor quotientAlgebra (π.rTensor baseIdeal otherValue)) := by
    induction otherValue using TensorProduct.inductionOn with
    | add otherValue y' condition h' => simp only [map_add] at condition h' ⊢; rw [condition, h']
    | tmul moduleElement otherIndex => simp
  have hφnat (otherValue : moduleType ⊗[baseRing] baseIdeal) : φ (TensorProduct.rid baseRing moduleType (baseIdeal.subtype.lTensor moduleType otherValue)) =
      TensorProduct.rid baseRing moduleType (baseIdeal.subtype.lTensor moduleType (φ.rTensor baseIdeal otherValue)) := by
    induction otherValue using TensorProduct.inductionOn with
    | add otherValue y' condition h' => simp only [map_add] at condition h' ⊢; rw [condition, h']
    | tmul moduleElement otherIndex => simp
  rw [injective_iff_map_eq_zero]
  intro thirdValue hz
  obtain ⟨otherValue, rfl⟩ := LinearMap.rTensor_surjective baseIdeal (Submodule.mkQ_surjective (LinearMap.range φ)) thirdValue
  have hα : Function.Injective (baseIdeal.subtype.lTensor moduleType) :=
    Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  set factor := TensorProduct.rid baseRing moduleType (baseIdeal.subtype.lTensor moduleType otherValue)
  have ha : factor ∈ LinearMap.range φ := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    change π factor = 0
    rw [hnat, hz, map_zero]
  obtain ⟨moduleElement, hm⟩ := ha
  have haJ : factor ∈ baseIdeal • (⊤ : Submodule baseRing moduleType) := by
    have hy : baseIdeal.subtype.lTensor moduleType otherValue ∈ baseIdeal • (⊤ : Submodule baseRing (moduleType ⊗[baseRing] baseRing)) := by
      have hJ : (baseIdeal • (⊤ : Submodule baseRing baseRing)) = baseIdeal := by simp [smul_eq_mul]
      have : baseIdeal.subtype = (baseIdeal • (⊤ : Submodule baseRing baseRing)).subtype ∘ₗ
          (LinearEquiv.ofEq _ _ hJ.symm).toLinearMap := rfl
      rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply]
      exact range_lTensor_smul_top_subtype_le (moduleType := moduleType) baseIdeal ⟨_, rfl⟩
    have := Submodule.smul_top_le_comap_smul_top baseIdeal (TensorProduct.rid baseRing moduleType).toLinearMap hy
    simpa [factor] using this
  obtain ⟨y', hy'⟩ := exists_rid_lTensor_eq_of_mem_smul_top baseIdeal (condition baseIdeal moduleElement (hm ▸ haJ))
  have hyy' : otherValue = φ.rTensor baseIdeal y' := by
    apply hα
    apply (TensorProduct.rid baseRing moduleType).injective
    change factor = _
    rw [← hm, ← hy', hφnat]
  rw [hyy', ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  have : π ∘ₗ φ = 0 := by
    ext moduleElement
    simp [π]
  rw [this, LinearMap.rTensor_zero, LinearMap.zero_apply]

end Module.Flat
