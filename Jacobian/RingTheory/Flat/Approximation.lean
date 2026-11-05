import Jacobian.RingTheory.LocalRing.ResidueField.RegularFiber
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.TensorProduct.DirectLimitFG

/-!
# Descent of module flatness to a finitely generated subalgebra

Let `R₀` be Noetherian, `S₀` a finite type `R₀`-algebra and `M₀` a finite
`S₀`-module. If its base change to an arbitrary `R₀`-algebra is flat over
that algebra, it is flat over every sufficiently large finitely generated
intermediate subalgebra. The construction first descends flatness at a prime,
then uses the open flat locus and a finite relation for the unit ideal.

The finite module is not required to be flat at the initial stage. No
Noetherian hypothesis is imposed on the ambient algebra.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Module

section Equiv

variable {R₀ R₁ S₀ M₀ : Type*} [CommRing R₀] [CommRing R₁] [CommRing S₀] [Algebra R₀ R₁]
  [Algebra R₀ S₀] [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

variable (M₀) in
/-- A scalar extension of a module tensored with a further module can be
identified with their tensor product over the original base. -/
noncomputable def baseChangeTensorEquiv (tensorModule : Type*) [AddCommGroup tensorModule] [Module R₀ tensorModule] [Module R₁ tensorModule]
    [IsScalarTower R₀ R₁ tensorModule] :
    ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀) ⊗[R₁] tensorModule ≃ₗ[S₀] M₀ ⊗[R₀] tensorModule :=
  ((AlgebraTensorModule.rightComm R₁ S₀ (R₁ ⊗[R₀] S₀) (R₁ ⊗[R₀] S₀) M₀ tensorModule).restrictScalars
    S₀).trans <|
  (TensorProduct.congr
    ({ Algebra.TensorProduct.tensorCancelEquiv (R₁ := R₁) (S₀ := S₀) tensorModule with
      map_smul' := fun algebraElement otherValue ↦ by
        rw [← algebraMap_smul (R₁ ⊗[R₀] S₀) algebraElement otherValue]
        exact Algebra.TensorProduct.tensorCancelEquiv_smul tensorModule algebraElement otherValue } :
      (R₁ ⊗[R₀] S₀) ⊗[R₁] tensorModule ≃ₗ[S₀] S₀ ⊗[R₀] tensorModule)
    (LinearEquiv.refl S₀ M₀)).trans <|
  (TensorProduct.comm S₀ _ M₀).trans (AlgebraTensorModule.cancelBaseChange R₀ S₀ S₀ M₀ tensorModule)

variable (tensorModule : Type*) [AddCommGroup tensorModule] [Module R₀ tensorModule] [Module R₁ tensorModule] [IsScalarTower R₀ R₁ tensorModule]

@[simp]
lemma baseChangeTensorEquiv_tmul (scalar : R₁) (algebraElement : S₀) (moduleElement : M₀) (kernelElement : tensorModule) :
    baseChangeTensorEquiv M₀ tensorModule (((scalar ⊗ₜ[R₀] algebraElement) ⊗ₜ[S₀] moduleElement) ⊗ₜ[R₁] kernelElement) = (algebraElement • moduleElement) ⊗ₜ (scalar • kernelElement) :=
  rfl

lemma baseChangeTensorEquiv_lTensor {tensorModule' : Type*} [AddCommGroup tensorModule'] [Module R₀ tensorModule'] [Module R₁ tensorModule']
    [IsScalarTower R₀ R₁ tensorModule'] (function : tensorModule' →ₗ[R₁] tensorModule) (otherValue : ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀) ⊗[R₁] tensorModule') :
    baseChangeTensorEquiv M₀ tensorModule (function.lTensor _ otherValue) =
      (function.restrictScalars R₀).lTensor M₀ (baseChangeTensorEquiv M₀ tensorModule' otherValue) := by
  induction otherValue using TensorProduct.inductionOn with
  | add value otherValue hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul value kernelElement =>
    induction value using TensorProduct.inductionOn with
    | add value otherValue hx hy => simp only [add_tmul, map_add, hx, hy]
    | tmul otherCoefficient moduleElement =>
      induction otherCoefficient using TensorProduct.inductionOn with
      | add value otherValue hx hy => simp only [add_tmul, map_add, hx, hy]
      | tmul scalar algebraElement => simp

lemma baseChangeTensorEquiv_smul (scalar : R₁) (algebraElement : S₀) (otherValue : ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀) ⊗[R₁] tensorModule) :
    baseChangeTensorEquiv M₀ tensorModule ((scalar ⊗ₜ[R₀] algebraElement : R₁ ⊗[R₀] S₀) • otherValue) =
      algebraElement • (DistribSMul.toLinearMap R₀ tensorModule scalar).lTensor M₀ (baseChangeTensorEquiv M₀ tensorModule otherValue) := by
  induction otherValue using TensorProduct.inductionOn with
  | add value otherValue hx hy => rw [smul_add, map_add, hx, hy, map_add, map_add, smul_add]
  | tmul value kernelElement =>
    induction value using TensorProduct.inductionOn with
    | add value otherValue hx hy => simp only [add_tmul, smul_add, map_add, hx, hy]
    | tmul otherCoefficient moduleElement =>
      induction otherCoefficient using TensorProduct.inductionOn with
      | add value otherValue hx hy => simp only [add_tmul, smul_add, map_add, hx, hy]
      | tmul scalar' algebraElement' =>
        rw [smul_tmul', smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
          baseChangeTensorEquiv_tmul, baseChangeTensorEquiv_tmul, LinearMap.lTensor_tmul,
          smul_tmul', DistribSMul.toLinearMap_apply, mul_smul, mul_smul]

lemma baseChangeTensorEquiv_algebraMap_smul (algebraElement : S₀)
    (otherValue : ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀) ⊗[R₁] tensorModule) :
    baseChangeTensorEquiv M₀ tensorModule (algebraMap S₀ (R₁ ⊗[R₀] S₀) algebraElement • otherValue) =
      algebraElement • baseChangeTensorEquiv M₀ tensorModule otherValue := by
  rw [algebraMap_smul, map_smul]

/-- Tensor injectivity after extension of scalars is equivalent to tensor
injectivity over the original base. -/
lemma lTensor_baseChange_injective_iff {tensorModule' : Type*} [AddCommGroup tensorModule'] [Module R₀ tensorModule']
    [Module R₁ tensorModule'] [IsScalarTower R₀ R₁ tensorModule'] (function : tensorModule' →ₗ[R₁] tensorModule) :
    Function.Injective (function.lTensor ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀)) ↔
      Function.Injective ((function.restrictScalars R₀).lTensor M₀) := by
  have : ⇑(function.lTensor ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀)) = (baseChangeTensorEquiv M₀ tensorModule).symm ∘
      ((function.restrictScalars R₀).lTensor M₀) ∘ (baseChangeTensorEquiv M₀ tensorModule') := by
    funext otherValue
    simp only [Function.comp_apply]
    rw [LinearEquiv.eq_symm_apply, baseChangeTensorEquiv_lTensor]
  rw [this, EquivLike.comp_injective, EquivLike.injective_comp]

/-- Flatness of the scalar-extended module is detected by tensoring ideals
of the extension ring over the original base. -/
lemma flat_baseChange_iff :
    Flat R₁ ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀) ↔
      ∀ testIdeal : Ideal R₁, Function.Injective ((testIdeal.subtype.restrictScalars R₀).lTensor M₀) := by
  rw [Flat.iff_lTensor_injective']
  exact forall_congr' fun testIdeal ↦ lTensor_baseChange_injective_iff R₁ testIdeal.subtype

end Equiv

section Localization

variable {R₀ R₁ S₀ M₀ : Type*} [CommRing R₀] [CommRing R₁] [CommRing S₀] [Algebra R₀ R₁]
  [Algebra R₀ S₀] [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

/-- Tensor injectivity at the prime below implies tensor injectivity after
localizing the scalar-extended module. -/
theorem lTensor_injective_localizedModule_baseChange (q₁ : Ideal (R₁ ⊗[R₀] S₀)) [q₁.IsPrime]
    {tensorModule tensorModule' : Type*} [AddCommGroup tensorModule] [Module R₀ tensorModule] [Module R₁ tensorModule] [IsScalarTower R₀ R₁ tensorModule]
    [AddCommGroup tensorModule'] [Module R₀ tensorModule'] [Module R₁ tensorModule'] [IsScalarTower R₀ R₁ tensorModule'] (function : tensorModule' →ₗ[R₁] tensorModule)
    (condition : Function.Injective ((function.restrictScalars R₀).lTensor
      (LocalizedModule (q₁.comap (algebraMap S₀ (R₁ ⊗[R₀] S₀))).primeCompl M₀))) :
    Function.Injective
      (function.lTensor (LocalizedModule q₁.primeCompl ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀))) := by
  set q₀ := q₁.comap (algebraMap S₀ (R₁ ⊗[R₀] S₀))
  rw [lTensor_injective_iff_of_isLocalizedModule (algebraRing := S₀) q₀.primeCompl
    (LocalizedModule.mkLinearMap q₀.primeCompl M₀)] at condition
  rw [lTensor_injective_iff_of_isLocalizedModule (algebraRing := R₁ ⊗[R₀] S₀) q₁.primeCompl
    (LocalizedModule.mkLinearMap q₁.primeCompl _)]
  intro otherValue hy
  obtain ⟨localizer, ht, hty⟩ := condition (baseChangeTensorEquiv M₀ tensorModule' otherValue) (by
    rw [← baseChangeTensorEquiv_lTensor, hy, map_zero])
  refine ⟨algebraMap S₀ (R₁ ⊗[R₀] S₀) localizer, ht, ?_⟩
  apply (baseChangeTensorEquiv M₀ tensorModule').injective
  rw [baseChangeTensorEquiv_algebraMap_smul, hty, map_zero]

end Localization

section LocalCriterion

universe u

variable {R₀ R₁ S₀ M₀ : Type u} [CommRing R₀] [CommRing R₁] [CommRing S₀] [Algebra R₀ R₁]
  [Algebra R₀ S₀] [AddCommGroup M₀] [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

/-- A localized scalar extension is flat when the corresponding kernel
elements vanish after extension of the base ideal. -/
theorem flat_localizedModule_baseChange_of_forall [IsNoetherianRing R₀] [IsNoetherianRing R₁]
    [Algebra.FiniteType R₀ S₀] [Module.Finite S₀ M₀] (q₁ : Ideal (R₁ ⊗[R₀] S₀)) [q₁.IsPrime]
    (condition : ∀ kernelTensor : M₀ ⊗[R₀] ((q₁.comap (algebraMap S₀ (R₁ ⊗[R₀] S₀))).comap (algebraMap R₀ S₀)),
      TensorProduct.rid R₀ M₀ (Submodule.subtype _ |>.lTensor M₀ kernelTensor) = 0 →
      (((Algebra.linearMap R₀ R₁) ∘ₗ Submodule.subtype _).codRestrict
        ((((q₁.comap (algebraMap S₀ (R₁ ⊗[R₀] S₀))).comap
          (algebraMap R₀ S₀)).map (algebraMap R₀ R₁)).restrictScalars R₀)
        (fun coefficient ↦ Ideal.mem_map_of_mem _ coefficient.2)).lTensor M₀ kernelTensor = 0) :
    Flat R₁ (LocalizedModule q₁.primeCompl ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀)) := by
  classical
  set q₀ := q₁.comap (algebraMap S₀ (R₁ ⊗[R₀] S₀))
  set p₀ := q₀.comap (algebraMap R₀ S₀)
  set I₁ : Ideal R₁ := p₀.map (algebraMap R₀ R₁)
  set extendedIdeal := I₁.restrictScalars R₀
  set idealMap : p₀ →ₗ[R₀] extendedIdeal := ((Algebra.linearMap R₀ R₁) ∘ₗ p₀.subtype).codRestrict extendedIdeal
    (fun coefficient ↦ Ideal.mem_map_of_mem _ coefficient.2)
  set M₀' := LocalizedModule q₀.primeCompl M₀
  set M₁ := LocalizedModule q₁.primeCompl ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀)
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing R₀ S₀
  have : IsNoetherianRing (R₁ ⊗[R₀] S₀) := Algebra.FiniteType.isNoetherianRing R₁ _
  have hbij : ∀ scalar ∉ p₀, Function.Bijective (fun moduleElement : M₀' ↦ scalar • moduleElement) := by
    intro scalar hr
    have hu := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap q₀.primeCompl M₀)
      (⟨algebraMap R₀ S₀ scalar, hr⟩ : q₀.primeCompl)
    rw [Module.End.isUnit_iff] at hu
    convert hu using 1
    ext moduleElement
    simp [Module.algebraMap_end_apply, algebraMap_smul]
  have hQ₀ : ∀ (auxiliaryModule : Type u) [AddCommGroup auxiliaryModule] [Module R₀ auxiliaryModule], (∀ index ∈ p₀, ∀ size : auxiliaryModule, index • size = 0) →
      ∀ auxiliaryModule' : Submodule R₀ auxiliaryModule, Function.Injective (auxiliaryModule'.subtype.lTensor M₀') :=
    fun auxiliaryModule _ _ hN auxiliaryModule' ↦ Flat.lTensor_subtype_injective_of_bijective_smul p₀ hbij hN auxiliaryModule'
  have hloc : ∀ kernelElement : M₀' ⊗[R₀] p₀, TensorProduct.rid R₀ M₀' (p₀.subtype.lTensor M₀' kernelElement) = 0 →
      idealMap.lTensor M₀' kernelElement = 0 := by
    intro kernelElement hk
    let localizationMap : M₀ →ₗ[S₀] M₀' := LocalizedModule.mkLinearMap q₀.primeCompl M₀
    let generators' : M₀ ⊗[R₀] p₀ →ₗ[S₀] M₀' ⊗[R₀] p₀ := AlgebraTensorModule.rTensor R₀ p₀ localizationMap
    let gL : M₀ ⊗[R₀] extendedIdeal →ₗ[S₀] M₀' ⊗[R₀] extendedIdeal := AlgebraTensorModule.rTensor R₀ extendedIdeal localizationMap
    have : IsLocalizedModule q₀.primeCompl generators' := IsLocalizedModule.rTensor (A := S₀) _ localizationMap
    have : IsLocalizedModule q₀.primeCompl gL := IsLocalizedModule.rTensor (A := S₀) _ localizationMap
    let μ₀ : M₀' ⊗[R₀] p₀ →ₗ[S₀] M₀' := (AlgebraTensorModule.rid R₀ S₀ M₀').toLinearMap ∘ₗ
      AlgebraTensorModule.lTensor S₀ M₀' p₀.subtype
    let μ' : M₀ ⊗[R₀] p₀ →ₗ[S₀] M₀ := (AlgebraTensorModule.rid R₀ S₀ M₀).toLinearMap ∘ₗ
      AlgebraTensorModule.lTensor S₀ M₀ p₀.subtype
    have hnat1 (value : M₀ ⊗[R₀] p₀) : μ₀ (generators' value) = localizationMap (μ' value) := by
      induction value using TensorProduct.inductionOn with
      | add value otherValue hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
      | tmul moduleElement coefficient =>
        simp only [μ₀, μ', generators', localizationMap, LinearMap.comp_apply, AlgebraTensorModule.rTensor_tmul,
          AlgebraTensorModule.lTensor_tmul, LinearEquiv.coe_coe, AlgebraTensorModule.rid_tmul,
          Submodule.subtype_apply]
        rw [← algebraMap_smul S₀ (coefficient : R₀) moduleElement, map_smul, algebraMap_smul]
    have hnat2 (value : M₀ ⊗[R₀] p₀) : AlgebraTensorModule.lTensor S₀ M₀' idealMap (generators' value) =
        gL (AlgebraTensorModule.lTensor S₀ M₀ idealMap value) := by
      induction value using TensorProduct.inductionOn with
      | add value otherValue hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
      | tmul algebraElement coefficient => rfl
    obtain ⟨⟨kernelElement', algebraElement⟩, hs⟩ := IsLocalizedModule.surj q₀.primeCompl generators' kernelElement
    simp only [Submonoid.smul_def] at hs
    have h1 : localizationMap (μ' kernelElement') = 0 := by
      rw [← hnat1, ← hs, map_smul]
      change (algebraElement : S₀) • (TensorProduct.rid R₀ M₀' (p₀.subtype.lTensor M₀' kernelElement)) = 0
      rw [hk, smul_zero]
    obtain ⟨localizer, ht⟩ := (IsLocalizedModule.eq_zero_iff q₀.primeCompl (f := localizationMap)).mp h1
    rw [Submonoid.smul_def, ← map_smul] at ht
    have h3 : AlgebraTensorModule.lTensor S₀ M₀ idealMap ((localizer : S₀) • kernelElement') = 0 := condition _ ht
    have h4 : ((localizer : S₀) * algebraElement) • AlgebraTensorModule.lTensor S₀ M₀' idealMap kernelElement = 0 := by
      rw [mul_smul, ← map_smul, hs, ← map_smul, ← map_smul generators', hnat2, h3, map_zero]
    have hu := IsLocalizedModule.map_units gL ⟨localizer * algebraElement, mul_mem localizer.2 algebraElement.2⟩
    refine (Module.End.isUnit_iff _).mp hu |>.1 ?_
    rw [map_zero, Module.algebraMap_end_apply]
    exact h4
  have hI₀ : Function.Injective (extendedIdeal.subtype.lTensor M₀') := by
    have hL : p₀ • (⊤ : Submodule R₀ R₁) ≤ extendedIdeal := by
      rw [Submodule.smul_le]
      intro coefficient ha size _
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    refine Flat.lTensor_subtype_injective_of_forall_ker p₀ hQ₀ extendedIdeal hL fun kernelElement hk size ↦ ?_
    let mn : extendedIdeal →ₗ[R₀] extendedIdeal := (DistribSMul.toLinearMap R₁ I₁ size).restrictScalars R₀
    have : ((LinearMap.toSpanSingleton R₀ R₁ size) ∘ₗ p₀.subtype).codRestrict extendedIdeal
        (fun index ↦ hL (Submodule.smul_mem_smul index.2 trivial)) = mn ∘ₗ idealMap := by
      ext coefficient
      simp [idealMap, Algebra.smul_def, mul_comm]
      rfl
    rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply, hloc kernelElement hk, map_zero]
  have hIS : I₁.map (algebraMap R₁ (Localization.AtPrime q₁)) ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.map_le_iff_le_comap,
      Ideal.map_le_iff_le_comap]
    intro coefficient ha
    rw [Ideal.mem_comap, Ideal.mem_comap,
      IsScalarTower.algebraMap_apply R₁ (R₁ ⊗[R₀] S₀) (Localization.AtPrime q₁),
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q₁) q₁,
      ← IsScalarTower.algebraMap_apply R₀ R₁ (R₁ ⊗[R₀] S₀),
      ← (Algebra.TensorProduct.includeRight : S₀ →ₐ[R₀] R₁ ⊗[R₀] S₀).commutes coefficient]
    exact ha
  refine Flat.of_lTensor_injective_of_forall (algebraRing := Localization.AtPrime q₁) (moduleType := M₁) I₁ hIS
    ?_ ?_
  · intro auxiliaryModule _ _ hN auxiliaryModule'
    let : Module R₀ auxiliaryModule := Module.compHom auxiliaryModule (algebraMap R₀ R₁)
    have : IsScalarTower R₀ R₁ auxiliaryModule := ⟨fun scalar algebraElement size ↦ by
      change (scalar • algebraElement) • size = algebraMap R₀ R₁ scalar • algebraElement • size
      rw [Algebra.smul_def, mul_smul]⟩
    apply lTensor_injective_localizedModule_baseChange q₁ auxiliaryModule'.subtype
    exact hQ₀ auxiliaryModule (fun index hi size ↦ hN _ (Ideal.mem_map_of_mem _ hi) size) (auxiliaryModule'.restrictScalars R₀)
  · exact lTensor_injective_localizedModule_baseChange q₁ I₁.subtype hI₀

end LocalCriterion

section FiniteStage

variable {R₀ ambientRing M₀ : Type*} [CommRing R₀] [CommRing ambientRing] [Algebra R₀ ambientRing] [AddCommGroup M₀]
  [Module R₀ M₀]

/-- A kernel element which vanishes after extension to the ambient algebra
already vanishes over every subalgebra containing a finite coefficient set. -/
theorem exists_finset_lTensor_eq_zero_of_injective [IsNoetherianRing R₀] (baseIdeal : Ideal R₀)
    (hp : Function.Injective
      (((baseIdeal.map (algebraMap R₀ ambientRing)).subtype.restrictScalars R₀).lTensor M₀))
    (kernelTensor : M₀ ⊗[R₀] baseIdeal) (hξ : TensorProduct.rid R₀ M₀ (baseIdeal.subtype.lTensor M₀ kernelTensor) = 0) :
    ∃ coefficients : Finset ambientRing, ∀ R₁ : Subalgebra R₀ ambientRing, (coefficients : Set ambientRing) ⊆ R₁ →
      (((Algebra.linearMap R₀ R₁) ∘ₗ baseIdeal.subtype).codRestrict
        ((baseIdeal.map (algebraMap R₀ R₁)).restrictScalars R₀)
        (fun coefficient ↦ Ideal.mem_map_of_mem _ coefficient.2)).lTensor M₀ kernelTensor = 0 := by
  classical
  set testIdeal := baseIdeal.map (algebraMap R₀ ambientRing)
  let idealExtension : baseIdeal →ₗ[R₀] testIdeal :=
    { toFun := fun coefficient ↦ ⟨algebraMap R₀ ambientRing coefficient, Ideal.mem_map_of_mem _ coefficient.2⟩
      map_add' := fun coefficient otherCoefficient ↦ Subtype.ext (by simp)
      map_smul' := fun scalar coefficient ↦ Subtype.ext (by simp [Algebra.smul_def]) }
  have hinj : Function.Injective (AlgebraTensorModule.rTensor R₀ M₀ testIdeal.subtype) := by
    have : ⇑(AlgebraTensorModule.rTensor R₀ M₀ testIdeal.subtype) = (TensorProduct.comm R₀ M₀ ambientRing) ∘
        ((testIdeal.subtype.restrictScalars R₀).lTensor M₀) ∘ (TensorProduct.comm R₀ testIdeal M₀) := by
      funext value
      induction value using TensorProduct.inductionOn with
      | add value otherValue hx hy => simp only [map_add, hx, hy, Function.comp_apply]
      | tmul generator moduleElement => rfl
    rw [this]
    exact (TensorProduct.comm R₀ M₀ ambientRing).injective.comp
      (hp.comp (TensorProduct.comm R₀ testIdeal M₀).injective)
  have himage : ∀ value : M₀ ⊗[R₀] baseIdeal, AlgebraTensorModule.rTensor R₀ M₀ testIdeal.subtype
      (idealExtension.rTensor M₀ (TensorProduct.comm R₀ M₀ baseIdeal value)) =
        (1 : ambientRing) ⊗ₜ TensorProduct.rid R₀ M₀ (baseIdeal.subtype.lTensor M₀ value) := by
    intro value
    induction value using TensorProduct.inductionOn with
    | add value otherValue hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add, tmul_add]
    | tmul algebraElement coefficient =>
      simp [idealExtension, Algebra.algebraMap_eq_smul_one, smul_tmul]
  set sourcePrime := LinearMap.range idealExtension
  have hPfg : sourcePrime.FG := by
    change (LinearMap.range idealExtension).FG
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map idealExtension
  set localizer := idealExtension.rangeRestrict.rTensor M₀ (TensorProduct.comm R₀ M₀ baseIdeal kernelTensor)
  have ht : sourcePrime.subtype.rTensor M₀ localizer = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply (sourcePrime.subtype.rTensor M₀), ← LinearMap.rTensor_comp]
    change AlgebraTensorModule.rTensor R₀ M₀ testIdeal.subtype
      (idealExtension.rTensor M₀ (TensorProduct.comm R₀ M₀ baseIdeal kernelTensor)) = 0
    rw [himage, hξ, tmul_zero]
  obtain ⟨targetPrime, hPQ, ⟨G, hG⟩, hQ⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hPfg ht
  have hrep : ∀ generators : testIdeal, ∃ (size : ℕ) (coefficients : Fin size → ambientRing) (idealElements : Fin size → baseIdeal),
      ∑ index, coefficients index * algebraMap R₀ ambientRing (idealElements index) = generators := by
    intro generators
    obtain ⟨size, coefficients, idealElements, hcd⟩ := Submodule.mem_span_set'.mp generators.2
    choose coefficient ha had using fun index ↦ (idealElements index).2
    exact ⟨size, coefficients, fun index ↦ ⟨coefficient index, ha index⟩, by rw [← hcd]; simp [had, smul_eq_mul]⟩
  choose size coefficients idealElements hcd using hrep
  refine ⟨G.biUnion fun generators ↦ Finset.univ.image (coefficients generators), fun R₁ hT ↦ ?_⟩
  set I₁ := (baseIdeal.map (algebraMap R₀ R₁)).restrictScalars R₀
  have hmem : ∀ value ∈ I₁, ((value : R₁) : ambientRing) ∈ testIdeal := by
    intro value hx
    have := Ideal.mem_map_of_mem R₁.val.toRingHom hx
    rwa [Ideal.map_map, show R₁.val.toRingHom.comp (algebraMap R₀ R₁) = algebraMap R₀ ambientRing from
      RingHom.ext fun scalar ↦ by simp] at this
  let coefficientEmbedding : I₁ →ₗ[R₀] testIdeal :=
    { toFun := fun value ↦ ⟨((value : R₁) : ambientRing), hmem value value.2⟩
      map_add' := fun value otherValue ↦ rfl
      map_smul' := fun scalar value ↦ Subtype.ext (by simp [Algebra.smul_def]) }
  have hκ : Function.Injective coefficientEmbedding := fun value otherValue condition ↦
    Subtype.ext (Subtype.ext congr(($condition : ambientRing)))
  have hQκ : targetPrime ≤ LinearMap.range coefficientEmbedding := by
    rw [← hG, Submodule.span_le]
    intro generators hg
    have hc : ∀ index, coefficients generators index ∈ R₁ := fun index ↦
      hT (Finset.mem_biUnion.mpr ⟨generators, hg, Finset.mem_image_of_mem _ (Finset.mem_univ index)⟩)
    refine ⟨⟨∑ index, ⟨coefficients generators index, hc index⟩ * algebraMap R₀ R₁ (idealElements generators index), ?_⟩, Subtype.ext ?_⟩
    · exact Submodule.sum_mem _ fun index _ ↦
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (idealElements generators index).2)
    · simp [coefficientEmbedding, ← hcd generators]
  obtain ⟨liftingMap, hψ⟩ : ∃ liftingMap : targetPrime →ₗ[R₀] I₁, liftingMap ∘ₗ Submodule.inclusion hPQ ∘ₗ idealExtension.rangeRestrict =
      ((Algebra.linearMap R₀ R₁) ∘ₗ baseIdeal.subtype).codRestrict I₁
        (fun coefficient ↦ Ideal.mem_map_of_mem _ coefficient.2) := by
    refine ⟨(LinearEquiv.ofInjective coefficientEmbedding hκ).symm.toLinearMap ∘ₗ Submodule.inclusion hQκ,
      LinearMap.ext fun coefficient ↦ hκ ?_⟩
    change coefficientEmbedding ((LinearEquiv.ofInjective coefficientEmbedding hκ).symm _) = _
    rw [LinearEquiv.ofInjective_symm_apply]
    rfl
  have key : (liftingMap ∘ₗ Submodule.inclusion hPQ ∘ₗ idealExtension.rangeRestrict).rTensor M₀
      (TensorProduct.comm R₀ M₀ baseIdeal kernelTensor) = liftingMap.rTensor M₀ ((Submodule.inclusion hPQ).rTensor M₀ localizer) := by
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply, LinearMap.rTensor_comp, LinearMap.comp_apply]
  rw [← hψ, ← (TensorProduct.comm R₀ baseIdeal M₀).apply_symm_apply kernelTensor, TensorProduct.comm_symm,
    LinearMap.lTensor_comm, key, hQ, map_zero, map_zero]


end FiniteStage

section AtPrime

universe u

variable {R₀ S₀ M₀ : Type u} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀] [AddCommGroup M₀]
  [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

/-- Flatness of a finite module at a prime descends to a finitely generated
subalgebra of the ambient algebra. -/
theorem exists_fg_flat_localizedModule_baseChange {ambientRing : Type u} [CommRing ambientRing] [Algebra R₀ ambientRing]
    [IsNoetherianRing R₀] [Algebra.FiniteType R₀ S₀] [Module.Finite S₀ M₀]
    (hA : Flat ambientRing ((ambientRing ⊗[R₀] S₀) ⊗[S₀] M₀)) (primeIdeal : Ideal (ambientRing ⊗[R₀] S₀)) [primeIdeal.IsPrime] :
    ∃ R₁ : Subalgebra R₀ ambientRing, R₁.FG ∧ IsNoetherianRing R₁ ∧
      Flat R₁ (LocalizedModule
        (primeIdeal.comap (Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ S₀)).toRingHom).primeCompl
        ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀)) := by
  classical
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing R₀ S₀
  set q₀ : Ideal S₀ := primeIdeal.comap (algebraMap S₀ (ambientRing ⊗[R₀] S₀))
  set p₀ : Ideal R₀ := q₀.comap (algebraMap R₀ S₀)
  let μ' : M₀ ⊗[R₀] p₀ →ₗ[S₀] M₀ := (AlgebraTensorModule.rid R₀ S₀ M₀).toLinearMap ∘ₗ
    AlgebraTensorModule.lTensor S₀ M₀ p₀.subtype
  have : Module.Finite S₀ (M₀ ⊗[R₀] p₀) :=
    Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange R₀ S₀ S₀ M₀ p₀)
  obtain ⟨kernelGenerators, hΞ⟩ : (LinearMap.ker μ').FG := IsNoetherian.noetherian _
  have hV : ∀ kernelTensor ∈ kernelGenerators, ∃ coefficients : Finset ambientRing, ∀ R₁ : Subalgebra R₀ ambientRing, (coefficients : Set ambientRing) ⊆ R₁ →
      (((Algebra.linearMap R₀ R₁) ∘ₗ p₀.subtype).codRestrict
        ((p₀.map (algebraMap R₀ R₁)).restrictScalars R₀)
        (fun coefficient ↦ Ideal.mem_map_of_mem _ coefficient.2)).lTensor M₀ kernelTensor = 0 := fun kernelTensor hξ ↦
    exists_finset_lTensor_eq_zero_of_injective p₀ (flat_baseChange_iff.mp hA _) kernelTensor (by
      have condition : kernelTensor ∈ LinearMap.ker μ' := hΞ ▸ Submodule.subset_span hξ
      exact condition)
  choose! coefficients hT using hV
  set R₁ := Algebra.adjoin R₀ ((kernelGenerators.biUnion coefficients : Finset ambientRing) : Set ambientRing)
  have : Algebra.FiniteType R₀ R₁ := Algebra.FiniteType.adjoin_of_finite (Finset.finite_toSet _)
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R₀ R₁
  refine ⟨R₁, Subalgebra.fg_adjoin_finset _, this, ?_⟩
  set q₁ := primeIdeal.comap (Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ S₀)).toRingHom
  have hq : q₁.comap (algebraMap S₀ (R₁ ⊗[R₀] S₀)) = q₀ := by
    rw [Ideal.comap_comap]
    congr 1
  apply flat_localizedModule_baseChange_of_forall q₁
  rw [hq]
  intro kernelTensor hξ
  have hξ' : kernelTensor ∈ Submodule.span S₀ (kernelGenerators : Set (M₀ ⊗[R₀] p₀)) := hΞ ▸ LinearMap.mem_ker.mpr hξ
  set idealMap := ((Algebra.linearMap R₀ R₁) ∘ₗ p₀.subtype).codRestrict
    ((p₀.map (algebraMap R₀ R₁)).restrictScalars R₀) (fun coefficient ↦ Ideal.mem_map_of_mem _ coefficient.2)
  change AlgebraTensorModule.lTensor S₀ M₀ idealMap kernelTensor = 0
  clear hξ
  induction hξ' using Submodule.span_induction with
  | mem value hx =>
    exact hT value hx R₁ (subset_trans (Finset.subset_biUnion_of_mem coefficients hx) Algebra.subset_adjoin)
  | zero => exact map_zero _
  | add value otherValue _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul coefficient value _ hx => rw [map_smul, hx, smul_zero]

end AtPrime

section Global

universe u

variable {R₀ S₀ M₀ : Type u} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀] [AddCommGroup M₀]
  [Module R₀ M₀] [Module S₀ M₀] [IsScalarTower R₀ S₀ M₀]

/-- Flatness at a prime of the extended module is preserved by a map
of base algebras. -/
theorem flat_localizedModule_baseChange_map {stageRing stageRing' : Type u} [CommRing stageRing] [CommRing stageRing']
    [Algebra R₀ stageRing] [Algebra R₀ stageRing'] (function : stageRing →ₐ[R₀] stageRing') (targetPrime : Ideal (stageRing' ⊗[R₀] S₀)) [targetPrime.IsPrime]
    (sourcePrime : Ideal (stageRing ⊗[R₀] S₀)) [sourcePrime.IsPrime]
    (hPQ : targetPrime.comap (Algebra.TensorProduct.map function (AlgHom.id R₀ S₀)).toRingHom = sourcePrime)
    (condition : Flat stageRing (LocalizedModule sourcePrime.primeCompl ((stageRing ⊗[R₀] S₀) ⊗[S₀] M₀))) :
    Flat stageRing' (LocalizedModule targetPrime.primeCompl ((stageRing' ⊗[R₀] S₀) ⊗[S₀] M₀)) := by
  subst hPQ
  let : Algebra stageRing stageRing' := function.toAlgebra
  have : IsScalarTower R₀ stageRing stageRing' := .of_algebraMap_eq fun scalar ↦ (function.commutes scalar).symm
  set coefficientMap := Algebra.TensorProduct.map function (AlgHom.id R₀ S₀)
  refine (Flat.iff_lTensor_injective' (R := stageRing')
    (M := LocalizedModule targetPrime.primeCompl
      ((stageRing' ⊗[R₀] S₀) ⊗[S₀] M₀))).2 ?_
  intro testIdeal
  rw [lTensor_injective_iff_of_isLocalizedModule (algebraRing := stageRing' ⊗[R₀] S₀) targetPrime.primeCompl
    (LocalizedModule.mkLinearMap targetPrime.primeCompl _)]
  intro otherValue hy
  have hR := (lTensor_injective_iff_of_isLocalizedModule
    (baseRing := stageRing) (algebraRing := stageRing ⊗[R₀] S₀)
    (moduleType := (stageRing ⊗[R₀] S₀) ⊗[S₀] M₀)
    (localizedModule := LocalizedModule (targetPrime.comap coefficientMap.toRingHom).primeCompl
      ((stageRing ⊗[R₀] S₀) ⊗[S₀] M₀))
    (auxiliaryModule := stageRing') (N' := ↥testIdeal)
    (targetPrime.comap coefficientMap.toRingHom).primeCompl
    (LocalizedModule.mkLinearMap (targetPrime.comap coefficientMap.toRingHom).primeCompl ((stageRing ⊗[R₀] S₀) ⊗[S₀] M₀))
    (testIdeal.subtype.restrictScalars stageRing)).1
    (Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
  set equivalence := baseChangeTensorEquiv (R₀ := R₀) (R₁ := stageRing) (S₀ := S₀) M₀ testIdeal
  set equivalence' := baseChangeTensorEquiv (R₀ := R₀) (R₁ := stageRing') (S₀ := S₀) M₀ testIdeal
  set thirdValue := equivalence.symm (equivalence' otherValue)
  obtain ⟨localizer, ht, htz⟩ := hR thirdValue (by
    apply (baseChangeTensorEquiv (R₀ := R₀) (R₁ := stageRing) (S₀ := S₀) M₀ stageRing').injective
    rw [baseChangeTensorEquiv_lTensor, LinearEquiv.apply_symm_apply, map_zero]
    have := congrArg (baseChangeTensorEquiv (R₀ := R₀) (R₁ := stageRing') (S₀ := S₀) M₀ stageRing') hy
    rw [baseChangeTensorEquiv_lTensor, map_zero] at this
    exact this)
  refine ⟨coefficientMap localizer, ht, ?_⟩
  apply equivalence'.injective
  rw [map_zero]
  have key : ∀ localizer : stageRing ⊗[R₀] S₀, equivalence' (coefficientMap localizer • otherValue) = equivalence (localizer • thirdValue) := by
    intro localizer
    induction localizer using TensorProduct.inductionOn with
    | add coefficient otherCoefficient ha hb => rw [map_add, add_smul, map_add, ha, hb, add_smul, map_add]
    | tmul scalar algebraElement =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, baseChangeTensorEquiv_smul,
        baseChangeTensorEquiv_smul, LinearEquiv.apply_symm_apply]
      congr 2
  rw [key, htz, map_zero]

/-- A module is flat over the base if its localizations at all primes
of the algebra are flat over the base. -/
theorem flat_of_forall_flat_localizedModule {stageRing algebraRing auxiliaryModule : Type*} [CommRing stageRing] [CommRing algebraRing]
    [Algebra stageRing algebraRing] [AddCommGroup auxiliaryModule] [Module stageRing auxiliaryModule] [Module algebraRing auxiliaryModule] [IsScalarTower stageRing algebraRing auxiliaryModule]
    (condition : ∀ (targetPrime : Ideal algebraRing) [targetPrime.IsPrime], Flat stageRing (LocalizedModule targetPrime.primeCompl auxiliaryModule)) : Flat stageRing auxiliaryModule := by
  rw [Flat.iff_lTensor_injective']
  intro testIdeal
  rw [injective_iff_map_eq_zero]
  intro otherValue hy
  by_contra hne
  have hI : LinearMap.ker (LinearMap.toSpanSingleton algebraRing _ otherValue) ≠ ⊤ := by
    intro htop
    apply hne
    have : (1 : algebraRing) ∈ LinearMap.ker (LinearMap.toSpanSingleton algebraRing _ otherValue) := htop ▸ Submodule.mem_top
    simpa using this
  obtain ⟨moduleElement, hm, hle⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨localizer, ht, hty⟩ := (lTensor_injective_iff_of_isLocalizedModule moduleElement.primeCompl
    (LocalizedModule.mkLinearMap moduleElement.primeCompl auxiliaryModule) testIdeal.subtype).1
    (Flat.iff_lTensor_injective'.1 (condition moduleElement) testIdeal) otherValue hy
  exact ht (hle (LinearMap.mem_ker.2 hty))

omit [Module R₀ M₀] [IsScalarTower R₀ S₀ M₀] in
/-- The flat locus of a finite scalar-extended module over a Noetherian
base is open. -/
theorem isOpen_setOf_flat_localizedModule_baseChange [Algebra.FiniteType R₀ S₀]
    [Module.Finite S₀ M₀] (stageRing : Type u) [CommRing stageRing] [Algebra R₀ stageRing] [IsNoetherianRing stageRing] :
    IsOpen {targetPrime : PrimeSpectrum (stageRing ⊗[R₀] S₀) |
      Flat stageRing (LocalizedModule targetPrime.asIdeal.primeCompl ((stageRing ⊗[R₀] S₀) ⊗[S₀] M₀))} := by
  rw [isOpen_iff_forall_mem_open]
  intro targetPrime (hQ : Flat stageRing _)
  obtain ⟨generators, hg, hopen⟩ := Flat.exists_notMem_forall_flat_localizedModule
    (baseRing := stageRing) (algebraRing := stageRing ⊗[R₀] S₀)
    (moduleType := (stageRing ⊗[R₀] S₀) ⊗[S₀] M₀) targetPrime.asIdeal hQ
  exact ⟨PrimeSpectrum.basicOpen generators, fun targetPrime' hQ' ↦ hopen targetPrime'.asIdeal hQ',
    PrimeSpectrum.isOpen_basicOpen, hg⟩

omit [Module R₀ M₀] [IsScalarTower R₀ S₀ M₀] in
/-- The inverse image of the flat locus of a Noetherian intermediate
subalgebra is open in the ambient prime spectrum. -/
theorem isOpen_setOf_flat_localizedModule_comap [Algebra.FiniteType R₀ S₀]
    [Module.Finite S₀ M₀] {ambientRing : Type u} [CommRing ambientRing] [Algebra R₀ ambientRing] (stageRing : Subalgebra R₀ ambientRing)
    [IsNoetherianRing stageRing] :
    IsOpen {primeIdeal : PrimeSpectrum (ambientRing ⊗[R₀] S₀) | Flat stageRing (LocalizedModule
      (primeIdeal.asIdeal.comap (Algebra.TensorProduct.map stageRing.val (AlgHom.id R₀ S₀)).toRingHom).primeCompl
      ((stageRing ⊗[R₀] S₀) ⊗[S₀] M₀))} :=
  (isOpen_setOf_flat_localizedModule_baseChange (M₀ := M₀) stageRing).preimage
    (PrimeSpectrum.continuous_comap (Algebra.TensorProduct.map stageRing.val (AlgHom.id R₀ S₀)).toRingHom)

private lemma map_val_map_inclusion {ambientRing : Type u} [CommRing ambientRing] [Algebra R₀ ambientRing] {stageRing stageRing' : Subalgebra R₀ ambientRing}
    (condition : stageRing ≤ stageRing') (value : stageRing ⊗[R₀] S₀) :
    Algebra.TensorProduct.map stageRing'.val (AlgHom.id R₀ S₀)
      (Algebra.TensorProduct.map (Subalgebra.inclusion condition) (AlgHom.id R₀ S₀) value) =
      Algebra.TensorProduct.map stageRing.val (AlgHom.id R₀ S₀) value := by
  induction value using TensorProduct.inductionOn with
  | add coefficient otherCoefficient ha hb => simp only [map_add, ha, hb]
  | tmul coefficient algebraElement => rfl

private lemma map_inclusion_map_inclusion {ambientRing : Type u} [CommRing ambientRing] [Algebra R₀ ambientRing]
    {stageRing stageRing' stageRing'' : Subalgebra R₀ ambientRing} (condition : stageRing ≤ stageRing') (condition' : stageRing' ≤ stageRing'') (value : stageRing ⊗[R₀] S₀) :
    Algebra.TensorProduct.map (Subalgebra.inclusion condition') (AlgHom.id R₀ S₀)
      (Algebra.TensorProduct.map (Subalgebra.inclusion condition) (AlgHom.id R₀ S₀) value) =
      Algebra.TensorProduct.map (Subalgebra.inclusion (condition.trans condition')) (AlgHom.id R₀ S₀) value := by
  induction value using TensorProduct.inductionOn with
  | add coefficient otherCoefficient ha hb => simp only [map_add, ha, hb]
  | tmul coefficient algebraElement => rfl

private lemma map_eq_rTensor {ambientRing : Type u} [CommRing ambientRing] [Algebra R₀ ambientRing] {stageRing stageRing' : Subalgebra R₀ ambientRing}
    (condition : stageRing ≤ stageRing') (value : stageRing ⊗[R₀] S₀) :
    Algebra.TensorProduct.map (Subalgebra.inclusion condition) (AlgHom.id R₀ S₀) value =
      LinearMap.rTensor S₀ (Subalgebra.inclusion condition).toLinearMap value := by
  induction value using TensorProduct.inductionOn with
  | add coefficient otherCoefficient ha hb => simp only [map_add, ha, hb]
  | tmul coefficient algebraElement => rfl

private lemma map_val_eq_rTensor {ambientRing : Type u} [CommRing ambientRing] [Algebra R₀ ambientRing] {stageRing : Subalgebra R₀ ambientRing}
    (value : stageRing ⊗[R₀] S₀) :
    Algebra.TensorProduct.map stageRing.val (AlgHom.id R₀ S₀) value =
      LinearMap.rTensor S₀ stageRing.val.toLinearMap value := by
  induction value using TensorProduct.inductionOn with
  | add coefficient otherCoefficient ha hb => simp only [map_add, ha, hb]
  | tmul coefficient algebraElement => rfl

set_option maxHeartbeats 1000000 in
/-- Flatness of the ambient scalar extension descends to every intermediate
subalgebra containing one finitely generated subalgebra. The original base is
Noetherian, the algebra is finite type, and the module is finite over that
algebra; the ambient algebra need not be Noetherian. -/
theorem exists_fg_forall_flat_baseChange {ambientRing : Type u} [CommRing ambientRing] [Algebra R₀ ambientRing]
    [IsNoetherianRing R₀] [Algebra.FiniteType R₀ S₀] [Module.Finite S₀ M₀]
    (hA : Flat ambientRing ((ambientRing ⊗[R₀] S₀) ⊗[S₀] M₀)) :
    ∃ R₁ : Subalgebra R₀ ambientRing, R₁.FG ∧
      ∀ stageRing : Subalgebra R₀ ambientRing, R₁ ≤ stageRing → Flat stageRing ((stageRing ⊗[R₀] S₀) ⊗[S₀] M₀) := by
  classical
  let stageLocus (stageRing : Subalgebra R₀ ambientRing) : Set (PrimeSpectrum (ambientRing ⊗[R₀] S₀)) :=
    {primeIdeal | Flat stageRing (LocalizedModule
      (primeIdeal.asIdeal.comap (Algebra.TensorProduct.map stageRing.val (AlgHom.id R₀ S₀)).toRingHom).primeCompl
      ((stageRing ⊗[R₀] S₀) ⊗[S₀] M₀))}
  have hcomap {stageRing stageRing' : Subalgebra R₀ ambientRing} (condition : stageRing ≤ stageRing') (primeIdeal : Ideal (ambientRing ⊗[R₀] S₀)) :
      (primeIdeal.comap (Algebra.TensorProduct.map stageRing'.val (AlgHom.id R₀ S₀)).toRingHom).comap
        (Algebra.TensorProduct.map (Subalgebra.inclusion condition) (AlgHom.id R₀ S₀)).toRingHom =
      primeIdeal.comap (Algebra.TensorProduct.map stageRing.val (AlgHom.id R₀ S₀)).toRingHom := by
    rw [Ideal.comap_comap]
    congr 1
    exact RingHom.ext fun value ↦ map_val_map_inclusion condition value
  have hW {stageRing stageRing' : Subalgebra R₀ ambientRing} (condition : stageRing ≤ stageRing') : stageLocus stageRing ⊆ stageLocus stageRing' := fun primeIdeal hq ↦
    flat_localizedModule_baseChange_map (Subalgebra.inclusion condition) _ _ (hcomap condition primeIdeal.asIdeal) hq
  have hWopen (stageRing : {stageRing : Subalgebra R₀ ambientRing // stageRing.FG}) : IsOpen (stageLocus stageRing.1) := by
    have : Algebra.FiniteType R₀ stageRing.1 := (Subalgebra.fg_iff_finiteType _).mp stageRing.2
    have : IsNoetherianRing stageRing.1 := Algebra.FiniteType.isNoetherianRing R₀ stageRing.1
    exact isOpen_setOf_flat_localizedModule_comap (M₀ := M₀) stageRing.1
  have hWcov (primeIdeal : PrimeSpectrum (ambientRing ⊗[R₀] S₀)) :
      ∃ stageRing : {stageRing : Subalgebra R₀ ambientRing // stageRing.FG}, primeIdeal ∈ stageLocus stageRing.1 := by
    obtain ⟨stageRing, hR, -, hflat⟩ := exists_fg_flat_localizedModule_baseChange hA primeIdeal.asIdeal
    exact ⟨⟨stageRing, hR⟩, hflat⟩
  have : Nonempty {stageRing : Subalgebra R₀ ambientRing // stageRing.FG} := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  obtain ⟨⟨R₁, hR₁⟩, hK⟩ := isCompact_univ.elim_directed_cover (fun stageRing ↦ stageLocus stageRing.1) hWopen
    (fun primeIdeal _ ↦ Set.mem_iUnion.mpr (hWcov primeIdeal))
    fun (stageRing stageRing' : {stageRing : Subalgebra R₀ ambientRing // stageRing.FG}) ↦ ⟨⟨stageRing.1 ⊔ stageRing'.1, stageRing.2.sup stageRing'.2⟩,
      hW le_sup_left, hW le_sup_right⟩
  have : Algebra.FiniteType R₀ R₁ := (Subalgebra.fg_iff_finiteType _).mp hR₁
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R₀ R₁
  set flatLocus := {targetPrime : PrimeSpectrum (R₁ ⊗[R₀] S₀) |
      Flat R₁ (LocalizedModule targetPrime.asIdeal.primeCompl ((R₁ ⊗[R₀] S₀) ⊗[S₀] M₀))}
  have hU : IsOpen flatLocus := isOpen_setOf_flat_localizedModule_baseChange R₁
  set nonflatLocus := flatLocusᶜ
  set complementIdeal := PrimeSpectrum.vanishingIdeal nonflatLocus
  set φ₁ := Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ S₀)
  have hZ : ∀ sourcePrime : PrimeSpectrum (R₁ ⊗[R₀] S₀), complementIdeal ≤ sourcePrime.asIdeal → sourcePrime ∈ nonflatLocus := by
    intro sourcePrime hP
    have : sourcePrime ∈ PrimeSpectrum.zeroLocus (complementIdeal : Set (R₁ ⊗[R₀] S₀)) := hP
    rwa [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hU.isClosed_compl.closure_eq] at this
  have hI : complementIdeal.map φ₁ = ⊤ := by
    by_contra hne
    obtain ⟨moduleElement, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmZ := hZ (PrimeSpectrum.comap φ₁.toRingHom ⟨moduleElement, hm.isPrime⟩)
      (Ideal.map_le_iff_le_comap.mp hle)
    exact hmZ (hK (Set.mem_univ (⟨moduleElement, hm.isPrime⟩ : PrimeSpectrum (ambientRing ⊗[R₀] S₀))))
  have h1 : (1 : ambientRing ⊗[R₀] S₀) ∈ Submodule.span (ambientRing ⊗[R₀] S₀) (φ₁ '' complementIdeal) := by
    change (1 : ambientRing ⊗[R₀] S₀) ∈ complementIdeal.map φ₁
    rw [hI]
    exact Submodule.mem_top
  obtain ⟨size, coefficients, generators, hcg⟩ := Submodule.mem_span_set'.mp h1
  choose coefficient ha hag using fun index ↦ (generators index).2
  choose coefficientStage hC hCc using fun index ↦ TensorProduct.Algebra.exists_of_fg (R := R₀) (N := S₀) (coefficients index)
  choose coefficients' hc' using hCc
  obtain ⟨s₁, hs₁⟩ := hR₁
  choose algebraElement hs using hC
  set R₂' : Subalgebra R₀ ambientRing :=
    Algebra.adjoin R₀ ((s₁ ∪ Finset.univ.biUnion algebraElement : Finset ambientRing) : Set ambientRing)
  have hR₁₂ : R₁ ≤ R₂' := by
    rw [← hs₁]
    exact Algebra.adjoin_mono (by simp)
  have hC₂ (index : Fin size) : coefficientStage index ≤ R₂' := by
    rw [← hs index]
    exact Algebra.adjoin_mono (fun value hx ↦ by
      simp only [Finset.coe_union, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ,
        Set.iUnion_true, Set.mem_union, Set.mem_iUnion]
      exact Or.inr ⟨index, hx⟩)
  set liftingMap := Algebra.TensorProduct.map (Subalgebra.inclusion hR₁₂) (AlgHom.id R₀ S₀)
  set unitRelation : R₂' ⊗[R₀] S₀ := ∑ index, LinearMap.rTensor S₀ (Subalgebra.inclusion (hC₂ index)).toLinearMap
    (coefficients' index) * liftingMap (coefficient index)
  have hw : LinearMap.rTensor S₀ R₂'.val.toLinearMap unitRelation =
      LinearMap.rTensor S₀ R₂'.val.toLinearMap 1 := by
    rw [← map_val_eq_rTensor, ← map_val_eq_rTensor, map_one, map_sum, ← hcg]
    refine Finset.sum_congr rfl fun index _ ↦ ?_
    rw [map_mul, ← hag index, smul_eq_mul, ← map_eq_rTensor, map_val_map_inclusion,
      map_val_map_inclusion, map_val_eq_rTensor, hc' index]
  obtain ⟨R₂, hR₂, hR₂fg, hw₂⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq
    (Subalgebra.fg_adjoin_finset _) hw
  refine ⟨R₂, hR₂fg, fun stageRing hR ↦ ?_⟩
  have h₁ : R₁ ≤ stageRing := hR₁₂.trans (hR₂.trans hR)
  set stageInclusion := Algebra.TensorProduct.map (Subalgebra.inclusion h₁) (AlgHom.id R₀ S₀)
  set extensionMap := Algebra.TensorProduct.map (Subalgebra.inclusion (hR₂.trans hR)) (AlgHom.id R₀ S₀)
  have hθ : extensionMap unitRelation = 1 := by
    rw [← map_inclusion_map_inclusion hR₂ hR unitRelation, map_eq_rTensor hR₂ unitRelation, hw₂, ← map_eq_rTensor,
      map_one, map_one]
  have hθψ (value : R₁ ⊗[R₀] S₀) : extensionMap (liftingMap value) = stageInclusion value := map_inclusion_map_inclusion _ _ value
  refine flat_of_forall_flat_localizedModule
    (stageRing := ↥stageRing) (algebraRing := ↥stageRing ⊗[R₀] S₀)
    (auxiliaryModule := (↥stageRing ⊗[R₀] S₀) ⊗[S₀] M₀) ?_
  intro targetPrime _
  refine flat_localizedModule_baseChange_map (Subalgebra.inclusion h₁) targetPrime (targetPrime.comap stageInclusion.toRingHom)
    rfl ?_
  by_contra hP
  have hPZ : (⟨targetPrime.comap stageInclusion.toRingHom, inferInstance⟩ : PrimeSpectrum (R₁ ⊗[R₀] S₀)) ∈ nonflatLocus := hP
  have hQ : (1 : stageRing ⊗[R₀] S₀) ∈ targetPrime := by
    rw [← hθ, map_sum]
    refine Ideal.sum_mem _ fun index _ ↦ ?_
    rw [map_mul, hθψ]
    exact Ideal.mul_mem_left _ _ ((PrimeSpectrum.mem_vanishingIdeal _ _).mp (ha index) _ hPZ)
  exact (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).mpr hQ)

end Global

end Module

end
