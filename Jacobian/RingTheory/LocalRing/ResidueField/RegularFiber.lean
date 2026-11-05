import Jacobian.RingTheory.Flat.LocalCriterion
import Jacobian.RingTheory.Ideal.RegularPrincipal
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Lifting regular principal ideals from fibres

For a flat finitely presented algebra, a quotient which is flat and finitely
presented over the base is locally cut out by a nonzerodivisor whenever its
fibre is. Noetherian approximation removes noetherian hypotheses on the base.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

namespace Algebra.TensorProduct

variable {R₀ R₁ S₀ : Type*} [CommRing R₀] [CommRing R₁] [CommRing S₀] [Algebra R₀ R₁]
  [Algebra R₀ S₀]

/-- Cancellation of a base change in a tensor product of modules. -/
noncomputable def tensorCancelEquiv (auxiliaryModule : Type*) [AddCommGroup auxiliaryModule] [Module R₀ auxiliaryModule] [Module R₁ auxiliaryModule]
    [IsScalarTower R₀ R₁ auxiliaryModule] : (R₁ ⊗[R₀] S₀) ⊗[R₁] auxiliaryModule ≃ₗ[R₀] S₀ ⊗[R₀] auxiliaryModule :=
  ((_root_.TensorProduct.comm R₁ (R₁ ⊗[R₀] S₀) auxiliaryModule).restrictScalars R₀).trans
    ((_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange R₀ R₁ R₁ auxiliaryModule S₀).restrictScalars
      R₀ |>.trans
      (_root_.TensorProduct.comm R₀ auxiliaryModule S₀))

variable (auxiliaryModule : Type*) [AddCommGroup auxiliaryModule] [Module R₀ auxiliaryModule] [Module R₁ auxiliaryModule] [IsScalarTower R₀ R₁ auxiliaryModule]

@[simp]
lemma tensorCancelEquiv_tmul (coefficient : R₁) (scalar : S₀) (degree : auxiliaryModule) :
    tensorCancelEquiv auxiliaryModule ((coefficient ⊗ₜ[R₀] scalar) ⊗ₜ[R₁] degree) = scalar ⊗ₜ (coefficient • degree) := rfl

lemma tensorCancelEquiv_smul (scalar : S₀) (otherValue : (R₁ ⊗[R₀] S₀) ⊗[R₁] auxiliaryModule) :
    tensorCancelEquiv auxiliaryModule ((1 ⊗ₜ[R₀] scalar : R₁ ⊗[R₀] S₀) • otherValue) = scalar • tensorCancelEquiv auxiliaryModule otherValue := by
  induction otherValue using TensorProduct.inductionOn with
  | add value otherValue hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | tmul value degree =>
    induction value using TensorProduct.inductionOn with
    | add value otherValue hx hy => simp only [add_tmul, smul_add, map_add, hx, hy]
    | tmul coefficient s' =>
      rw [smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        tensorCancelEquiv_tmul, tensorCancelEquiv_tmul, smul_tmul', smul_eq_mul]

lemma tensorCancelEquiv_lTensor {N' : Type*} [AddCommGroup N'] [Module R₀ N'] [Module R₁ N']
    [IsScalarTower R₀ R₁ N'] (function : N' →ₗ[R₁] auxiliaryModule) (otherValue : (R₁ ⊗[R₀] S₀) ⊗[R₁] N') :
    tensorCancelEquiv auxiliaryModule (function.lTensor _ otherValue) =
      (function.restrictScalars R₀).lTensor S₀ (tensorCancelEquiv N' otherValue) := by
  induction otherValue using TensorProduct.inductionOn with
  | add value otherValue hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul value degree =>
    induction value using TensorProduct.inductionOn with
    | add value otherValue hx hy => simp only [add_tmul, map_add, hx, hy]
    | tmul coefficient scalar => simp

lemma tensorCancelEquiv_tmul_smul (coefficient : R₁) (scalar : S₀) (otherValue : (R₁ ⊗[R₀] S₀) ⊗[R₁] auxiliaryModule) :
    tensorCancelEquiv auxiliaryModule ((coefficient ⊗ₜ[R₀] scalar : R₁ ⊗[R₀] S₀) • otherValue) =
      scalar • (DistribSMul.toLinearMap R₀ auxiliaryModule coefficient).lTensor S₀ (tensorCancelEquiv auxiliaryModule otherValue) := by
  induction otherValue using TensorProduct.inductionOn with
  | add value otherValue hx hy => rw [smul_add, map_add, hx, hy, map_add, map_add, smul_add]
  | tmul value degree =>
    induction value using TensorProduct.inductionOn with
    | add value otherValue hx hy => simp only [add_tmul, smul_add, map_add, hx, hy]
    | tmul r' s' =>
      rw [smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
        tensorCancelEquiv_tmul, tensorCancelEquiv_tmul, LinearMap.lTensor_tmul, smul_tmul',
        smul_eq_mul, DistribSMul.toLinearMap_apply, mul_smul]

variable {baseAlgebra : Type*} [CommRing baseAlgebra] [Algebra R₀ baseAlgebra] [Algebra R₁ baseAlgebra] [IsScalarTower R₀ R₁ baseAlgebra]

/-- Changing the intermediate base ring in a tensor product. -/
noncomputable def baseChangeTensorEquiv (auxiliaryModule : Type*) [AddCommGroup auxiliaryModule] [Module R₀ auxiliaryModule]
    [Module R₁ auxiliaryModule] [Module baseAlgebra auxiliaryModule] [IsScalarTower R₀ R₁ auxiliaryModule] [IsScalarTower R₀ baseAlgebra auxiliaryModule]
    [IsScalarTower R₁ baseAlgebra auxiliaryModule] :
    (R₁ ⊗[R₀] S₀) ⊗[R₁] auxiliaryModule ≃ₗ[R₀] (baseAlgebra ⊗[R₀] S₀) ⊗[baseAlgebra] auxiliaryModule :=
  (tensorCancelEquiv auxiliaryModule).trans (tensorCancelEquiv auxiliaryModule).symm

lemma baseChangeTensorEquiv_smul (auxiliaryModule : Type*) [AddCommGroup auxiliaryModule] [Module R₀ auxiliaryModule]
    [Module R₁ auxiliaryModule] [Module baseAlgebra auxiliaryModule] [IsScalarTower R₀ R₁ auxiliaryModule] [IsScalarTower R₀ baseAlgebra auxiliaryModule]
    [IsScalarTower R₁ baseAlgebra auxiliaryModule] (scalar : R₁ ⊗[R₀] S₀) (otherValue : (R₁ ⊗[R₀] S₀) ⊗[R₁] auxiliaryModule) :
    baseChangeTensorEquiv auxiliaryModule (scalar • otherValue) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ R₁ baseAlgebra) (AlgHom.id R₀ S₀) scalar •
        baseChangeTensorEquiv (baseAlgebra := baseAlgebra) auxiliaryModule otherValue := by
  apply (tensorCancelEquiv (R₁ := baseAlgebra) (S₀ := S₀) auxiliaryModule).injective
  simp only [baseChangeTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  induction scalar using TensorProduct.inductionOn with
  | add value otherValue hx hy => rw [add_smul, map_add, hx, hy, map_add, add_smul, map_add]
  | tmul coefficient scalar =>
    rw [tensorCancelEquiv_tmul_smul, Algebra.TensorProduct.map_tmul, tensorCancelEquiv_tmul_smul,
      LinearEquiv.apply_symm_apply]
    congr 2
    ext degree
    simp [IsScalarTower.toAlgHom_apply, algebraMap_smul]

end Algebra.TensorProduct

namespace Module

variable {R₀ R₁ S₀ : Type*} [CommRing R₀] [CommRing R₁] [CommRing S₀] [Algebra R₀ R₁]
  [Algebra R₀ S₀]

theorem lTensor_injective_localization_tensor (q₁ : Ideal (R₁ ⊗[R₀] S₀)) [q₁.IsPrime]
    {auxiliaryModule N' : Type*} [AddCommGroup auxiliaryModule] [Module R₀ auxiliaryModule] [Module R₁ auxiliaryModule] [IsScalarTower R₀ R₁ auxiliaryModule]
    [AddCommGroup N'] [Module R₀ N'] [Module R₁ N'] [IsScalarTower R₀ R₁ N'] (function : N' →ₗ[R₁] auxiliaryModule)
    (condition : Function.Injective ((function.restrictScalars R₀).lTensor
      (Localization.AtPrime (q₁.comap Algebra.TensorProduct.includeRight.toRingHom)))) :
    Function.Injective (function.lTensor (Localization.AtPrime q₁)) := by
  set q₀ := q₁.comap (Algebra.TensorProduct.includeRight.toRingHom : S₀ →+* R₁ ⊗[R₀] S₀)
  rw [lTensor_injective_iff_of_isLocalizedModule (algebraRing := S₀) q₀.primeCompl
    (Algebra.linearMap S₀ (Localization.AtPrime q₀))] at condition
  rw [lTensor_injective_iff_of_isLocalizedModule (algebraRing := R₁ ⊗[R₀] S₀) q₁.primeCompl
    (Algebra.linearMap _ (Localization.AtPrime q₁))]
  intro otherValue hy
  obtain ⟨parameter, ht, hty⟩ := condition (Algebra.TensorProduct.tensorCancelEquiv N' otherValue) (by
    rw [← Algebra.TensorProduct.tensorCancelEquiv_lTensor, hy, map_zero])
  refine ⟨1 ⊗ₜ parameter, ht, ?_⟩
  apply (Algebra.TensorProduct.tensorCancelEquiv N').injective
  rw [Algebra.TensorProduct.tensorCancelEquiv_smul, hty, map_zero]

end Module

namespace Module

variable {R₀ baseAlgebra S₀ : Type*} [CommRing R₀] [CommRing baseAlgebra] [Algebra R₀ baseAlgebra] [CommRing S₀]
  [Algebra R₀ S₀]

theorem exists_finset_lTensor_eq_zero [IsNoetherianRing R₀] [Flat baseAlgebra (baseAlgebra ⊗[R₀] S₀)] (basePrime : Ideal R₀)
    (ξ : S₀ ⊗[R₀] basePrime) (hξ : TensorProduct.rid R₀ S₀ (basePrime.subtype.lTensor S₀ ξ) = 0) :
    ∃ multiplicativeSet : Finset baseAlgebra, ∀ R₁ : Subalgebra R₀ baseAlgebra, (multiplicativeSet : Set baseAlgebra) ⊆ R₁ →
      (((Algebra.linearMap R₀ R₁) ∘ₗ basePrime.subtype).codRestrict
        ((basePrime.map (algebraMap R₀ R₁)).restrictScalars R₀)
        (fun factor ↦ Ideal.mem_map_of_mem _ factor.2)).lTensor S₀ ξ = 0 := by
  classical
  set baseIdeal := basePrime.map (algebraMap R₀ baseAlgebra)
  let τ : basePrime →ₗ[R₀] baseIdeal :=
    { toFun := fun factor ↦ ⟨algebraMap R₀ baseAlgebra factor, Ideal.mem_map_of_mem _ factor.2⟩
      map_add' := fun factor otherFactor ↦ Subtype.ext (by simp)
      map_smul' := fun coefficient factor ↦ Subtype.ext (by simp [Algebra.smul_def]) }

  have hinj : Function.Injective (AlgebraTensorModule.rTensor R₀ S₀ baseIdeal.subtype) := by
    have hflat := Flat.rTensor_preserves_injective_linearMap (M := baseAlgebra ⊗[R₀] S₀) baseIdeal.subtype
      Subtype.val_injective
    have hcomm : ∀ value, AlgebraTensorModule.rTensor R₀ S₀ baseIdeal.subtype
        (AlgebraTensorModule.cancelBaseChange R₀ baseAlgebra baseAlgebra baseIdeal S₀ value) =
          AlgebraTensorModule.cancelBaseChange R₀ baseAlgebra baseAlgebra baseAlgebra S₀ (baseIdeal.subtype.rTensor _ value) := by
      intro value
      induction value using TensorProduct.inductionOn with
      | add value otherValue hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
      | tmul otherIndex otherValue =>
        induction otherValue using TensorProduct.inductionOn with
        | add otherValue thirdValue hy hz => simp only [tmul_add, map_add, hy, hz]
        | tmul factor scalar => simp
    intro value otherValue hxy
    obtain ⟨value, rfl⟩ := (AlgebraTensorModule.cancelBaseChange R₀ baseAlgebra baseAlgebra baseIdeal S₀).surjective value
    obtain ⟨otherValue, rfl⟩ := (AlgebraTensorModule.cancelBaseChange R₀ baseAlgebra baseAlgebra baseIdeal S₀).surjective otherValue
    rw [hcomm, hcomm] at hxy
    rw [hflat ((AlgebraTensorModule.cancelBaseChange R₀ baseAlgebra baseAlgebra baseAlgebra S₀).injective hxy)]
  have himage : ∀ value : S₀ ⊗[R₀] basePrime, AlgebraTensorModule.rTensor R₀ S₀ baseIdeal.subtype
      (τ.rTensor S₀ (TensorProduct.comm R₀ S₀ basePrime value)) =
        (1 : baseAlgebra) ⊗ₜ TensorProduct.rid R₀ S₀ (basePrime.subtype.lTensor S₀ value) := by
    intro value
    induction value using TensorProduct.inductionOn with
    | add value otherValue hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add, tmul_add]
    | tmul scalar factor =>
      simp [τ, Algebra.algebraMap_eq_smul_one, smul_tmul]
  set primeIdeal := LinearMap.range τ
  have hPfg : primeIdeal.FG := by
    change (LinearMap.range τ).FG
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map τ
  set parameter := τ.rangeRestrict.rTensor S₀ (TensorProduct.comm R₀ S₀ basePrime ξ)
  have ht : primeIdeal.subtype.rTensor S₀ parameter = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply (primeIdeal.subtype.rTensor S₀), ← LinearMap.rTensor_comp]
    change AlgebraTensorModule.rTensor R₀ S₀ baseIdeal.subtype
      (τ.rTensor S₀ (TensorProduct.comm R₀ S₀ basePrime ξ)) = 0
    rw [himage, hξ, tmul_zero]
  obtain ⟨otherPrime, hPQ, ⟨generators, hG⟩, hQ⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hPfg ht
  have hrep : ∀ localizer : baseIdeal, ∃ (degree : ℕ) (multiplier : Fin degree → baseAlgebra) (auxiliaryFactor : Fin degree → basePrime),
      ∑ index, multiplier index * algebraMap R₀ baseAlgebra (auxiliaryFactor index) = localizer := by
    intro localizer
    obtain ⟨degree, multiplier, auxiliaryFactor, hcd⟩ := Submodule.mem_span_set'.mp localizer.2
    choose factor ha had using fun index ↦ (auxiliaryFactor index).2
    exact ⟨degree, multiplier, fun index ↦ ⟨factor index, ha index⟩, by rw [← hcd]; simp [had, smul_eq_mul]⟩
  choose degree multiplier auxiliaryFactor hcd using hrep
  refine ⟨generators.biUnion fun localizer ↦ Finset.univ.image (multiplier localizer), fun R₁ hT ↦ ?_⟩
  set I₁ := (basePrime.map (algebraMap R₀ R₁)).restrictScalars R₀
  have hmem : ∀ value ∈ I₁, ((value : R₁) : baseAlgebra) ∈ baseIdeal := by
    intro value hx
    have := Ideal.mem_map_of_mem R₁.val.toRingHom hx
    rwa [Ideal.map_map, show R₁.val.toRingHom.comp (algebraMap R₀ R₁) = algebraMap R₀ baseAlgebra from
      RingHom.ext fun coefficient ↦ by simp] at this
  let κ : I₁ →ₗ[R₀] baseIdeal :=
    { toFun := fun value ↦ ⟨((value : R₁) : baseAlgebra), hmem value value.2⟩
      map_add' := fun value otherValue ↦ rfl
      map_smul' := fun coefficient value ↦ Subtype.ext (by simp [Algebra.smul_def]) }
  have hκ : Function.Injective κ := fun value otherValue condition ↦
    Subtype.ext (Subtype.ext congr(($condition : baseAlgebra)))
  have hQκ : otherPrime ≤ LinearMap.range κ := by
    rw [← hG, Submodule.span_le]
    intro localizer hg
    have hc : ∀ index, multiplier localizer index ∈ R₁ := fun index ↦
      hT (Finset.mem_biUnion.mpr ⟨localizer, hg, Finset.mem_image_of_mem _ (Finset.mem_univ index)⟩)
    refine ⟨⟨∑ index, ⟨multiplier localizer index, hc index⟩ * algebraMap R₀ R₁ (auxiliaryFactor localizer index), ?_⟩, Subtype.ext ?_⟩
    · exact Submodule.sum_mem _ fun index _ ↦
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (auxiliaryFactor localizer index).2)
    · simp [κ, ← hcd localizer]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : otherPrime →ₗ[R₀] I₁, ψ ∘ₗ Submodule.inclusion hPQ ∘ₗ τ.rangeRestrict =
      ((Algebra.linearMap R₀ R₁) ∘ₗ basePrime.subtype).codRestrict I₁
        (fun factor ↦ Ideal.mem_map_of_mem _ factor.2) := by
    refine ⟨(LinearEquiv.ofInjective κ hκ).symm.toLinearMap ∘ₗ Submodule.inclusion hQκ,
      LinearMap.ext fun factor ↦ hκ ?_⟩
    change κ ((LinearEquiv.ofInjective κ hκ).symm _) = _
    rw [LinearEquiv.ofInjective_symm_apply]
    rfl
  have key : (ψ ∘ₗ Submodule.inclusion hPQ ∘ₗ τ.rangeRestrict).rTensor S₀
      (TensorProduct.comm R₀ S₀ basePrime ξ) = ψ.rTensor S₀ ((Submodule.inclusion hPQ).rTensor S₀ parameter) := by
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply, LinearMap.rTensor_comp, LinearMap.comp_apply]
  rw [← hψ, ← (TensorProduct.comm R₀ basePrime S₀).apply_symm_apply ξ, TensorProduct.comm_symm,
    LinearMap.lTensor_comm, key, hQ, map_zero, map_zero]

end Module

namespace Module

universe universeLevel

variable {R₀ R₁ S₀ : Type universeLevel} [CommRing R₀] [CommRing R₁] [CommRing S₀] [Algebra R₀ R₁]
  [Algebra R₀ S₀]

theorem flat_localization_tensor_of_forall [IsNoetherianRing R₀] [IsNoetherianRing R₁]
    [Algebra.FiniteType R₀ S₀] (q₁ : Ideal (R₁ ⊗[R₀] S₀)) [q₁.IsPrime]
    (condition : ∀ ξ : S₀ ⊗[R₀] ((q₁.comap Algebra.TensorProduct.includeRight.toRingHom).comap
        (algebraMap R₀ S₀)),
      TensorProduct.rid R₀ S₀ (Submodule.subtype _ |>.lTensor S₀ ξ) = 0 →
      (((Algebra.linearMap R₀ R₁) ∘ₗ Submodule.subtype _).codRestrict
        ((((q₁.comap Algebra.TensorProduct.includeRight.toRingHom).comap
          (algebraMap R₀ S₀)).map (algebraMap R₀ R₁)).restrictScalars R₀)
        (fun factor ↦ Ideal.mem_map_of_mem _ factor.2)).lTensor S₀ ξ = 0) :
    Flat R₁ (Localization.AtPrime q₁) := by
  classical
  set q₀ := q₁.comap (Algebra.TensorProduct.includeRight.toRingHom : S₀ →+* R₁ ⊗[R₀] S₀)
  set p₀ := q₀.comap (algebraMap R₀ S₀)
  set I₁ : Ideal R₁ := p₀.map (algebraMap R₀ R₁)
  set localizedModule := I₁.restrictScalars R₀
  set σ : p₀ →ₗ[R₀] localizedModule := ((Algebra.linearMap R₀ R₁) ∘ₗ p₀.subtype).codRestrict localizedModule
    (fun factor ↦ Ideal.mem_map_of_mem _ factor.2)
  set M₀ := Localization.AtPrime q₀
  set M₁ := Localization.AtPrime q₁
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing R₀ S₀
  have : IsNoetherianRing (R₁ ⊗[R₀] S₀) := Algebra.FiniteType.isNoetherianRing R₁ _

  have hbij : ∀ coefficient ∉ p₀, Function.Bijective (fun moduleElement : M₀ ↦ coefficient • moduleElement) := by
    intro coefficient hr
    have hu : IsUnit (algebraMap R₀ M₀ coefficient) := by
      rw [IsScalarTower.algebraMap_apply R₀ S₀ M₀]
      exact IsLocalization.map_units M₀ (⟨algebraMap R₀ S₀ coefficient, hr⟩ : q₀.primeCompl)
    simp_rw [Algebra.smul_def]
    exact ⟨fun value otherValue hxy ↦ hu.mul_left_cancel hxy, fun otherValue ↦ ⟨hu.unit⁻¹ * otherValue, by
      simp only
      rw [← mul_assoc, hu.mul_val_inv, one_mul]⟩⟩
  have hQ₀ : ∀ (auxiliaryModule : Type universeLevel) [AddCommGroup auxiliaryModule] [Module R₀ auxiliaryModule], (∀ index ∈ p₀, ∀ degree : auxiliaryModule, index • degree = 0) →
      ∀ N' : Submodule R₀ auxiliaryModule, Function.Injective (N'.subtype.lTensor M₀) :=
    fun auxiliaryModule _ _ hN N' ↦ Flat.lTensor_subtype_injective_of_bijective_smul p₀ hbij hN N'

  have hloc : ∀ exponent : M₀ ⊗[R₀] p₀, TensorProduct.rid R₀ M₀ (p₀.subtype.lTensor M₀ exponent) = 0 →
      σ.lTensor M₀ exponent = 0 := by
    intro exponent hk
    let ℓ : S₀ →ₗ[S₀] M₀ := Algebra.linearMap S₀ M₀
    let g' : S₀ ⊗[R₀] p₀ →ₗ[S₀] M₀ ⊗[R₀] p₀ := AlgebraTensorModule.rTensor R₀ p₀ ℓ
    let gL : S₀ ⊗[R₀] localizedModule →ₗ[S₀] M₀ ⊗[R₀] localizedModule := AlgebraTensorModule.rTensor R₀ localizedModule ℓ
    have : IsLocalizedModule q₀.primeCompl g' := IsLocalizedModule.rTensor (A := S₀) _ ℓ
    have : IsLocalizedModule q₀.primeCompl gL := IsLocalizedModule.rTensor (A := S₀) _ ℓ
    let μ₀ : M₀ ⊗[R₀] p₀ →ₗ[S₀] M₀ := (AlgebraTensorModule.rid R₀ S₀ M₀).toLinearMap ∘ₗ
      AlgebraTensorModule.lTensor S₀ M₀ p₀.subtype
    let μ' : S₀ ⊗[R₀] p₀ →ₗ[S₀] S₀ := (AlgebraTensorModule.rid R₀ S₀ S₀).toLinearMap ∘ₗ
      AlgebraTensorModule.lTensor S₀ S₀ p₀.subtype
    have hnat1 (value : S₀ ⊗[R₀] p₀) : μ₀ (g' value) = ℓ (μ' value) := by
      induction value using TensorProduct.inductionOn with
      | add value otherValue hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
      | tmul scalar factor =>
        simp [μ₀, μ', g', ℓ, Algebra.smul_def, IsScalarTower.algebraMap_apply R₀ S₀ M₀]
    have hnat2 (value : S₀ ⊗[R₀] p₀) : AlgebraTensorModule.lTensor S₀ M₀ σ (g' value) =
        gL (AlgebraTensorModule.lTensor S₀ S₀ σ value) := by
      induction value using TensorProduct.inductionOn with
      | add value otherValue hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
      | tmul scalar factor => rfl
    obtain ⟨⟨k', scalar⟩, hs⟩ := IsLocalizedModule.surj q₀.primeCompl g' exponent
    simp only [Submonoid.smul_def] at hs
    have h1 : ℓ (μ' k') = 0 := by
      rw [← hnat1, ← hs, map_smul]
      change (scalar : S₀) • (TensorProduct.rid R₀ M₀ (p₀.subtype.lTensor M₀ exponent)) = 0
      rw [hk, smul_zero]
    obtain ⟨parameter, ht⟩ := (IsLocalizedModule.eq_zero_iff q₀.primeCompl (f := ℓ)).mp h1
    rw [Submonoid.smul_def, ← map_smul] at ht
    have h3 : AlgebraTensorModule.lTensor S₀ S₀ σ ((parameter : S₀) • k') = 0 := condition _ ht
    have h4 : ((parameter : S₀) * scalar) • AlgebraTensorModule.lTensor S₀ M₀ σ exponent = 0 := by
      rw [mul_smul, ← map_smul, hs, ← map_smul, ← map_smul g', hnat2, h3, map_zero]
    have hu := IsLocalizedModule.map_units gL ⟨parameter * scalar, mul_mem parameter.2 scalar.2⟩
    refine (Module.End.isUnit_iff _).mp hu |>.1 ?_
    rw [map_zero, Module.algebraMap_end_apply]
    exact h4
  have hI₀ : Function.Injective (localizedModule.subtype.lTensor M₀) := by
    have hL : p₀ • (⊤ : Submodule R₀ R₁) ≤ localizedModule := by
      rw [Submodule.smul_le]
      intro factor ha degree _
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    refine Flat.lTensor_subtype_injective_of_forall_ker p₀ hQ₀ localizedModule hL fun exponent hk degree ↦ ?_
    let mn : localizedModule →ₗ[R₀] localizedModule := (DistribSMul.toLinearMap R₁ I₁ degree).restrictScalars R₀
    have : ((LinearMap.toSpanSingleton R₀ R₁ degree) ∘ₗ p₀.subtype).codRestrict localizedModule
        (fun index ↦ hL (Submodule.smul_mem_smul index.2 trivial)) = mn ∘ₗ σ := by
      ext factor
      simp [σ, Algebra.smul_def, mul_comm]
      rfl
    rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply, hloc exponent hk, map_zero]

  have hIS : I₁.map (algebraMap R₁ M₁) ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.map_le_iff_le_comap,
      Ideal.map_le_iff_le_comap]
    intro factor ha
    rw [Ideal.mem_comap, Ideal.mem_comap,
      IsScalarTower.algebraMap_apply R₁ (R₁ ⊗[R₀] S₀) M₁,
      IsLocalization.AtPrime.to_map_mem_maximal_iff M₁ q₁,
      ← IsScalarTower.algebraMap_apply R₀ R₁ (R₁ ⊗[R₀] S₀),
      ← (Algebra.TensorProduct.includeRight : S₀ →ₐ[R₀] R₁ ⊗[R₀] S₀).commutes factor]
    exact ha
  refine Flat.of_lTensor_injective_of_forall
    (algebraRing := M₁) (moduleType := M₁) I₁ hIS ?_ ?_
  · intro auxiliaryModule _ _ hN N'
    let : Module R₀ auxiliaryModule := Module.compHom auxiliaryModule (algebraMap R₀ R₁)
    have : IsScalarTower R₀ R₁ auxiliaryModule := ⟨fun coefficient scalar degree ↦ by
      change (coefficient • scalar) • degree = algebraMap R₀ R₁ coefficient • scalar • degree
      rw [Algebra.smul_def, mul_smul]⟩
    apply lTensor_injective_localization_tensor q₁ N'.subtype
    exact hQ₀ auxiliaryModule (fun index hi degree ↦ hN _ (Ideal.mem_map_of_mem _ hi) degree) (N'.restrictScalars R₀)
  · exact lTensor_injective_localization_tensor q₁ I₁.subtype hI₀

theorem exists_fg_flat_localization_tensor {baseAlgebra : Type universeLevel} [CommRing baseAlgebra] [Algebra R₀ baseAlgebra]
    [IsNoetherianRing R₀] [Algebra.FiniteType R₀ S₀] [Flat baseAlgebra (baseAlgebra ⊗[R₀] S₀)]
    (prime : Ideal (baseAlgebra ⊗[R₀] S₀)) [prime.IsPrime] :
    ∃ R₁ : Subalgebra R₀ baseAlgebra, R₁.FG ∧ IsNoetherianRing R₁ ∧
      Flat R₁ (Localization.AtPrime
        (prime.comap (Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ S₀)).toRingHom)) := by
  classical
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing R₀ S₀
  set q₀ : Ideal S₀ := prime.comap (Algebra.TensorProduct.includeRight.toRingHom)
  set p₀ : Ideal R₀ := q₀.comap (algebraMap R₀ S₀)
  let μ' : S₀ ⊗[R₀] p₀ →ₗ[S₀] S₀ := (AlgebraTensorModule.rid R₀ S₀ S₀).toLinearMap ∘ₗ
    AlgebraTensorModule.lTensor S₀ S₀ p₀.subtype
  obtain ⟨Ξ, hΞ⟩ : (LinearMap.ker μ').FG := IsNoetherian.noetherian _
  have hV : ∀ ξ ∈ Ξ, ∃ multiplicativeSet : Finset baseAlgebra, ∀ R₁ : Subalgebra R₀ baseAlgebra, (multiplicativeSet : Set baseAlgebra) ⊆ R₁ →
      (((Algebra.linearMap R₀ R₁) ∘ₗ p₀.subtype).codRestrict
        ((p₀.map (algebraMap R₀ R₁)).restrictScalars R₀)
        (fun factor ↦ Ideal.mem_map_of_mem _ factor.2)).lTensor S₀ ξ = 0 := fun ξ hξ ↦
    exists_finset_lTensor_eq_zero p₀ ξ (by
      have condition : ξ ∈ LinearMap.ker μ' := hΞ ▸ Submodule.subset_span hξ
      exact condition)
  choose! multiplicativeSet hT using hV
  set R₁ := Algebra.adjoin R₀ ((Ξ.biUnion multiplicativeSet : Finset baseAlgebra) : Set baseAlgebra)
  have : Algebra.FiniteType R₀ R₁ := Algebra.FiniteType.adjoin_of_finite (Finset.finite_toSet _)
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R₀ R₁
  refine ⟨R₁, Subalgebra.fg_adjoin_finset _, this, ?_⟩
  set q₁ := prime.comap (Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ S₀)).toRingHom
  have hq : q₁.comap (Algebra.TensorProduct.includeRight.toRingHom) = q₀ := by
    rw [Ideal.comap_comap]
    congr 1
  apply flat_localization_tensor_of_forall q₁
  rw [hq]
  intro ξ hξ
  have hξ' : ξ ∈ Submodule.span S₀ (Ξ : Set (S₀ ⊗[R₀] p₀)) := hΞ ▸ LinearMap.mem_ker.mpr hξ
  set σ := ((Algebra.linearMap R₀ R₁) ∘ₗ p₀.subtype).codRestrict
    ((p₀.map (algebraMap R₀ R₁)).restrictScalars R₀) (fun factor ↦ Ideal.mem_map_of_mem _ factor.2)
  change AlgebraTensorModule.lTensor S₀ S₀ σ ξ = 0
  clear hξ
  induction hξ' using Submodule.span_induction with
  | mem value hx =>
    exact hT value hx R₁ (subset_trans (Finset.subset_biUnion_of_mem multiplicativeSet hx) Algebra.subset_adjoin)
  | zero => exact map_zero _
  | add value otherValue _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul factor value _ hx => rw [map_smul, hx, smul_zero]

end Module

namespace Algebra

universe universeLevel

lemma mem_map_of_mul_mem_map_of_tensor {baseRing algebraRing residueRing : Type*} [CommRing baseRing] [CommRing algebraRing] [CommRing residueRing]
    [Algebra baseRing algebraRing] [Algebra baseRing residueRing] (prime : Ideal algebraRing) [prime.IsPrime]
    (hflat : Module.Flat baseRing (Localization.AtPrime prime))
    (hker : ∀ coefficient : baseRing, algebraMap baseRing residueRing coefficient = 0 ↔ coefficient ∈ prime.comap (algebraMap baseRing algebraRing)) (function parameter : algebraRing) (ht : parameter ∉ prime)
    (auxiliaryProperty : ∀ otherValue : algebraRing ⊗[baseRing] residueRing, function • otherValue = 0 → parameter • otherValue = 0) :
    ∀ moduleElement : Localization.AtPrime prime, algebraMap algebraRing _ function * moduleElement ∈
        (prime.comap (algebraMap baseRing algebraRing)).map (algebraMap baseRing (Localization.AtPrime prime)) →
      moduleElement ∈ (prime.comap (algebraMap baseRing algebraRing)).map (algebraMap baseRing (Localization.AtPrime prime)) := by
  set basePrime := prime.comap (algebraMap baseRing algebraRing)
  set M₁ := Localization.AtPrime prime
  have Hloc : ∀ thirdValue : M₁ ⊗[baseRing] residueRing, (algebraMap algebraRing M₁ function) • thirdValue = 0 → thirdValue = 0 := by
    intro thirdValue hz
    let ℓ := AlgebraTensorModule.rTensor baseRing residueRing (Algebra.linearMap algebraRing M₁)
    have : IsLocalizedModule prime.primeCompl ℓ := IsLocalizedModule.rTensor (A := algebraRing) _ _
    obtain ⟨⟨z', multiplierValue⟩, hu⟩ := IsLocalizedModule.surj prime.primeCompl ℓ thirdValue
    simp only [Submonoid.smul_def] at hu
    have h1 : ℓ (function • z') = 0 := by
      rw [map_smul, ← hu, smul_comm, ← algebraMap_smul M₁ function thirdValue, hz, smul_zero]
    obtain ⟨u', hu'⟩ := (IsLocalizedModule.eq_zero_iff prime.primeCompl (f := ℓ)).mp h1
    rw [Submonoid.smul_def] at hu'
    have h2 : parameter • ((u' : algebraRing) • z') = 0 := auxiliaryProperty _ (by rw [smul_comm, hu'])
    have h3 : (parameter * u' * multiplierValue : algebraRing) • thirdValue = 0 := by
      rw [mul_smul (parameter * u'), hu, ← map_smul, mul_smul, h2, LinearMap.map_zero]
    refine (Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units ℓ (⟨parameter, ht⟩ * u' * multiplierValue)) |>.1 ?_
    rw [LinearMap.map_zero, Module.algebraMap_end_apply]
    exact h3
  intro moduleElement hm
  have : Module.Flat baseRing M₁ := hflat
  let ε : M₁ →ₗ[baseRing] M₁ ⊗[baseRing] residueRing :=
    (Algebra.linearMap baseRing residueRing).lTensor M₁ ∘ₗ (_root_.TensorProduct.rid baseRing M₁).symm.toLinearMap
  have hε1 (value : M₁) : ε value = value ⊗ₜ 1 := by simp [ε]
  have hε : ∀ value ∈ basePrime.map (algebraMap baseRing M₁), ε value = 0 := by
    intro value hx
    have hx' : value ∈ basePrime • (⊤ : Submodule baseRing M₁) := by
      rw [Ideal.smul_top_eq_map]
      exact hx
    clear hx
    induction hx' using Submodule.smul_induction_on' with
    | smul coefficient hr m' _ =>
      rw [LinearMap.map_smul, hε1, ← tmul_smul, ← Algebra.algebraMap_eq_smul_one,
        (hker coefficient).mpr hr, tmul_zero]
    | add value _ otherValue _ hx hy => rw [LinearMap.map_add, hx, hy, add_zero]
  have h1 : algebraMap algebraRing M₁ function • ε moduleElement = 0 := by
    rw [hε1, smul_tmul', smul_eq_mul, ← hε1]
    exact hε _ hm
  have h2 : ε moduleElement = 0 := Hloc _ h1
  let ψ : (baseRing ⧸ basePrime) →ₗ[baseRing] residueRing :=
    (Ideal.Quotient.liftₐ basePrime (Algebra.ofId baseRing residueRing) fun coefficient hr ↦ (hker coefficient).mpr hr).toLinearMap
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro value hx
    obtain ⟨coefficient, rfl⟩ := Ideal.Quotient.mk_surjective value
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hker coefficient]
    exact hx
  have h3 : moduleElement ⊗ₜ[baseRing] (1 : baseRing ⧸ basePrime) = 0 := by
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := M₁) ψ hψ
    rw [LinearMap.lTensor_tmul, LinearMap.map_zero, ← h2, hε1]
    simp [ψ]
  have h4 := congr(TensorProduct.tensorQuotEquivQuotSMul M₁ basePrime $h3)
  rw [← map_one (Ideal.Quotient.mk basePrime), TensorProduct.tensorQuotEquivQuotSMul_tmul_mk,
    one_smul, LinearEquiv.map_zero, Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map] at h4
  exact h4

theorem exists_notMem_forall_mul_mem_map_of_tensor {R₀ baseAlgebra S₀ : Type universeLevel} [CommRing R₀]
    [CommRing baseAlgebra] [CommRing S₀] [Algebra R₀ baseAlgebra] [Algebra R₀ S₀] [IsNoetherianRing R₀]
    [Algebra.FiniteType R₀ S₀] [Module.Flat baseAlgebra (baseAlgebra ⊗[R₀] S₀)] (prime : Ideal (baseAlgebra ⊗[R₀] S₀))
    [prime.IsPrime] (function parameter : S₀) (ht : (1 ⊗ₜ parameter : baseAlgebra ⊗[R₀] S₀) ∉ prime) {residueRing : Type*} [CommRing residueRing]
    [Algebra baseAlgebra residueRing] (hK : RingHom.ker (algebraMap baseAlgebra residueRing) = prime.comap (algebraMap baseAlgebra (baseAlgebra ⊗[R₀] S₀)))
    (hfib : ∀ value : (baseAlgebra ⊗[R₀] S₀) ⊗[baseAlgebra] residueRing,
      (1 ⊗ₜ function : baseAlgebra ⊗[R₀] S₀) • value = 0 → (1 ⊗ₜ parameter : baseAlgebra ⊗[R₀] S₀) • value = 0) :
    ∃ localizer ∉ prime, ∀ (baseIdeal : Ideal baseAlgebra) (value : baseAlgebra ⊗[R₀] S₀), (1 ⊗ₜ function) * value ∈ baseIdeal.map (algebraMap baseAlgebra _) →
      ∃ degree : ℕ, localizer ^ degree * value ∈ baseIdeal.map (algebraMap baseAlgebra _) := by
  classical
  obtain ⟨R₁, -, hR₁, hflat⟩ := Module.exists_fg_flat_localization_tensor (S₀ := S₀) prime
  set targetAlgebra := baseAlgebra ⊗[R₀] S₀
  set S₁ := R₁ ⊗[R₀] S₀
  let ι : S₁ →ₐ[R₀] targetAlgebra :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ R₁ baseAlgebra) (AlgHom.id R₀ S₀)
  have hι : Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ S₀) = ι := rfl
  rw [hι] at hflat
  set q₁ := prime.comap ι.toRingHom
  set f₁ : S₁ := 1 ⊗ₜ function
  set t₁ : S₁ := 1 ⊗ₜ parameter
  have hι1 (scalar : S₀) : ι (1 ⊗ₜ scalar) = 1 ⊗ₜ scalar := by
    refine (Algebra.TensorProduct.map_tmul _ _ _ _).trans ?_
    rw [map_one]
    rfl
  have hιf : ι f₁ = 1 ⊗ₜ function := hι1 function
  have hιt : ι t₁ = 1 ⊗ₜ parameter := hι1 parameter
  have ht₁ : t₁ ∉ q₁ := by
    change ι.toRingHom t₁ ∉ prime
    exact hιt ▸ ht

  have : IsScalarTower R₁ baseAlgebra residueRing := inferInstance
  let : Algebra R₀ residueRing := ((algebraMap baseAlgebra residueRing).comp (algebraMap R₀ baseAlgebra)).toAlgebra
  have : IsScalarTower R₀ baseAlgebra residueRing := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R₀ R₁ residueRing := ⟨fun coefficient scalar exponent ↦ by
    change (coefficient • (scalar : baseAlgebra)) • exponent = coefficient • ((scalar : baseAlgebra) • exponent)
    exact smul_assoc coefficient (scalar : baseAlgebra) exponent⟩

  have H₁ : ∀ otherValue : S₁ ⊗[R₁] residueRing, f₁ • otherValue = 0 → t₁ • otherValue = 0 := by
    intro otherValue hy
    apply (Algebra.TensorProduct.baseChangeTensorEquiv (baseAlgebra := baseAlgebra) residueRing).injective
    rw [Algebra.TensorProduct.baseChangeTensorEquiv_smul, LinearEquiv.map_zero]
    change ι t₁ • _ = 0
    rw [hιt]
    apply hfib
    rw [← hιf]
    change ι f₁ • _ = 0
    rw [← Algebra.TensorProduct.baseChangeTensorEquiv_smul, hy, LinearEquiv.map_zero]

  set p₁ := q₁.comap (algebraMap R₁ S₁)
  set M₁ := Localization.AtPrime q₁
  have hker : ∀ coefficient : R₁, algebraMap R₁ residueRing coefficient = 0 ↔ coefficient ∈ p₁ := by
    intro coefficient
    have h1 : ι (algebraMap R₁ S₁ coefficient) = algebraMap baseAlgebra targetAlgebra coefficient := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
      refine (Algebra.TensorProduct.map_tmul _ _ _ _).trans ?_
      rw [map_one]
      rfl
    change algebraMap baseAlgebra residueRing coefficient = 0 ↔ ι.toRingHom (algebraMap R₁ S₁ coefficient) ∈ prime
    rw [← RingHom.mem_ker, hK, Ideal.mem_comap]
    change _ ↔ ι (algebraMap R₁ S₁ coefficient) ∈ prime
    rw [h1]
  have hfib₁ := mem_map_of_mul_mem_map_of_tensor q₁ hflat hker f₁ t₁ ht₁ H₁
  obtain ⟨localizer, hg, hP⟩ := Algebra.exists_notMem_forall_pow_smul_eq_zero q₁ f₁ hfib₁
  have hz (baseIdeal : Ideal baseAlgebra) (otherFactor : targetAlgebra) : otherFactor ⊗ₜ[baseAlgebra] (1 : baseAlgebra ⧸ baseIdeal) = 0 ↔ otherFactor ∈ baseIdeal.map (algebraMap baseAlgebra targetAlgebra) := by
    rw [← (TensorProduct.tensorQuotEquivQuotSMul targetAlgebra baseIdeal).map_eq_zero_iff,
      ← map_one (Ideal.Quotient.mk baseIdeal), TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul,
      Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
  refine ⟨ι localizer, hg, fun baseIdeal value hx ↦ ?_⟩
  let equivalence := Algebra.TensorProduct.baseChangeTensorEquiv
    (R₀ := R₀) (baseAlgebra := baseAlgebra) (S₀ := S₀) (R₁ := R₁)
    (baseAlgebra ⧸ baseIdeal)
  set otherValue := equivalence.symm (value ⊗ₜ[baseAlgebra] (1 : baseAlgebra ⧸ baseIdeal))
  have hy : f₁ • otherValue = 0 := by
    apply equivalence.injective
    rw [Algebra.TensorProduct.baseChangeTensorEquiv_smul, LinearEquiv.apply_symm_apply,
      LinearEquiv.map_zero, hιf, smul_tmul', smul_eq_mul, hz]
    exact hx
  obtain ⟨degree, hn⟩ := hP (baseAlgebra ⧸ baseIdeal) otherValue hy
  refine ⟨degree, (hz baseIdeal _).mp ?_⟩
  have := congr(equivalence $hn)
  rw [Algebra.TensorProduct.baseChangeTensorEquiv_smul, LinearEquiv.apply_symm_apply,
    LinearEquiv.map_zero, map_pow, smul_tmul', smul_eq_mul] at this
  exact this

lemma _root_.Algebra.TensorProduct.smul_eq_tmul_one_mul {baseRing targetAlgebra residueRing : Type*} [CommRing baseRing] [CommRing targetAlgebra]
    [CommRing residueRing] [Algebra baseRing targetAlgebra] [Algebra baseRing residueRing] (otherFactor : targetAlgebra) (value : targetAlgebra ⊗[baseRing] residueRing) :
    otherFactor • value = (otherFactor ⊗ₜ[baseRing] (1 : residueRing)) * value := by
  induction value using TensorProduct.inductionOn with
  | add value otherValue hx hy => rw [smul_add, hx, hy, mul_add]
  | tmul multiplier exponent => rw [smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul]

/-- A finitely presented algebra with two specified elements descends to a noetherian model. -/
theorem exists_noetherian_model {baseAlgebra : Type universeLevel} {targetAlgebra : Type*} [CommRing baseAlgebra] [CommRing targetAlgebra] [Algebra baseAlgebra targetAlgebra]
    [Algebra.FinitePresentation baseAlgebra targetAlgebra] (function parameter : targetAlgebra) :
    ∃ (R₀ : Type universeLevel) (_ : CommRing R₀) (_ : IsNoetherianRing R₀) (_ : Algebra R₀ baseAlgebra) (S₀ : Type universeLevel)
      (_ : CommRing S₀) (_ : Algebra R₀ S₀) (_ : Algebra.FiniteType R₀ S₀)
      (equivalence : baseAlgebra ⊗[R₀] S₀ ≃ₐ[baseAlgebra] targetAlgebra) (f₀ t₀ : S₀), equivalence (1 ⊗ₜ f₀) = function ∧ equivalence (1 ⊗ₜ t₀) = parameter := by
  classical
  let primeIdeal := Algebra.Presentation.ofFinitePresentation baseAlgebra targetAlgebra
  obtain ⟨submodule, rfl⟩ := primeIdeal.aeval_val_surjective function
  obtain ⟨multiplicativeSet, rfl⟩ := primeIdeal.aeval_val_surjective parameter
  let R₀ := Algebra.adjoin primeIdeal.Core ((submodule.coeffs ∪ multiplicativeSet.coeffs : Finset baseAlgebra) : Set baseAlgebra)
  have : Algebra.FiniteType ℤ R₀ :=
    Algebra.FiniteType.trans (S := primeIdeal.Core) inferInstance
      (Algebra.FiniteType.adjoin_of_finite (Finset.finite_toSet _))
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  let equivalence : baseAlgebra ⊗[R₀] primeIdeal.ModelOfHasCoeffs R₀ ≃ₐ[baseAlgebra] targetAlgebra := primeIdeal.tensorModelOfHasCoeffsEquiv R₀
  have hlift (ambientScheme : MvPolynomial (Fin (Algebra.Presentation.ofFinitePresentationVars baseAlgebra targetAlgebra)) baseAlgebra)
      (hX : (ambientScheme.coeffs : Set baseAlgebra) ⊆ R₀) :
      ∃ x₀ : primeIdeal.ModelOfHasCoeffs R₀, equivalence (1 ⊗ₜ x₀) = MvPolynomial.aeval primeIdeal.val ambientScheme := by
    obtain ⟨X₀, rfl⟩ : ambientScheme ∈ Set.range (MvPolynomial.map (algebraMap R₀ baseAlgebra)) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro factor ha
      exact ⟨⟨factor, hX ha⟩, rfl⟩
    refine ⟨Ideal.Quotient.mk _ X₀, ?_⟩
    rw [MvPolynomial.aeval_map_algebraMap, ← primeIdeal.tensorModelOfHasCoeffsEquiv_symm_tmul R₀]
    exact equivalence.apply_symm_apply _
  obtain ⟨f₀, hf₀⟩ := hlift submodule (subset_trans (by simp) Algebra.subset_adjoin)
  obtain ⟨t₀, ht₀⟩ := hlift multiplicativeSet (subset_trans (by simp) Algebra.subset_adjoin)
  exact ⟨R₀, inferInstance, inferInstance, inferInstance, primeIdeal.ModelOfHasCoeffs R₀, inferInstance,
    inferInstance, inferInstance, equivalence, f₀, t₀, hf₀, ht₀⟩

/-- Fibrewise injectivity of multiplication spreads to all ideal quotients near the given prime. -/
theorem exists_notMem_forall_mul_mem_map {baseAlgebra : Type universeLevel} {targetAlgebra : Type*} [CommRing baseAlgebra] [CommRing targetAlgebra]
    [Algebra baseAlgebra targetAlgebra] [Module.Flat baseAlgebra targetAlgebra] [Algebra.FinitePresentation baseAlgebra targetAlgebra] (prime : Ideal targetAlgebra) [prime.IsPrime]
    (function parameter : targetAlgebra) (ht : parameter ∉ prime) {residueRing : Type*} [CommRing residueRing] [Algebra baseAlgebra residueRing]
    (hK : RingHom.ker (algebraMap baseAlgebra residueRing) = prime.comap (algebraMap baseAlgebra targetAlgebra))
    (hfib : ∀ value : targetAlgebra ⊗[baseAlgebra] residueRing, function • value = 0 → parameter • value = 0) :
    ∃ localizer ∉ prime, ∀ (baseIdeal : Ideal baseAlgebra) (value : targetAlgebra), function * value ∈ baseIdeal.map (algebraMap baseAlgebra targetAlgebra) →
      ∃ degree : ℕ, localizer ^ degree * value ∈ baseIdeal.map (algebraMap baseAlgebra targetAlgebra) := by
  obtain ⟨R₀, _, _, _, S₀, _, _, _, equivalence, f₀, t₀, hf₀, ht₀⟩ :=
    exists_noetherian_model (baseAlgebra := baseAlgebra) function parameter
  have : Module.Flat baseAlgebra (baseAlgebra ⊗[R₀] S₀) := Module.Flat.of_linearEquiv equivalence.toLinearEquiv
  have he : (equivalence : baseAlgebra ⊗[R₀] S₀ →+* targetAlgebra).comp (algebraMap baseAlgebra _) = algebraMap baseAlgebra targetAlgebra :=
    RingHom.ext fun factor ↦ equivalence.commutes factor
  set q' := prime.comap (equivalence : baseAlgebra ⊗[R₀] S₀ →+* targetAlgebra)
  let fiberAlgebra : (baseAlgebra ⊗[R₀] S₀) ⊗[baseAlgebra] residueRing ≃ₐ[baseAlgebra] targetAlgebra ⊗[baseAlgebra] residueRing := Algebra.TensorProduct.congr equivalence AlgEquiv.refl
  have hE (otherFactor : baseAlgebra ⊗[R₀] S₀) (value : (baseAlgebra ⊗[R₀] S₀) ⊗[baseAlgebra] residueRing) : fiberAlgebra (otherFactor • value) = equivalence otherFactor • fiberAlgebra value := by
    rw [Algebra.TensorProduct.smul_eq_tmul_one_mul, Algebra.TensorProduct.smul_eq_tmul_one_mul,
      map_mul]
    rfl
  obtain ⟨localizer, hg, hP⟩ := exists_notMem_forall_mul_mem_map_of_tensor q' f₀ t₀
    (by change equivalence (1 ⊗ₜ t₀) ∉ prime; rwa [ht₀])
    (by rw [hK, Ideal.comap_comap, he])
    (fun value hx ↦ by
      apply fiberAlgebra.injective
      rw [hE, map_zero, ht₀]
      apply hfib
      rw [← hf₀, ← hE, hx, map_zero])
  have hmap (baseIdeal : Ideal baseAlgebra) (otherValue : baseAlgebra ⊗[R₀] S₀) : equivalence otherValue ∈ baseIdeal.map (algebraMap baseAlgebra targetAlgebra) ↔
      otherValue ∈ baseIdeal.map (algebraMap baseAlgebra (baseAlgebra ⊗[R₀] S₀)) := by
    have he' : (equivalence.toRingEquiv : baseAlgebra ⊗[R₀] S₀ →+* targetAlgebra).comp (algebraMap baseAlgebra _) = algebraMap baseAlgebra targetAlgebra := he
    rw [← he', ← Ideal.map_map, Ideal.map_comap_of_equiv, Ideal.mem_comap]
    simp
  refine ⟨equivalence localizer, hg, fun baseIdeal value hx ↦ ?_⟩
  obtain ⟨value, rfl⟩ := equivalence.surjective value
  obtain ⟨degree, hn⟩ := hP baseIdeal value (by
    rw [← hmap, map_mul, hf₀]
    exact hx)
  exact ⟨degree, by rw [← map_pow, ← map_mul, hmap]; exact hn⟩

lemma mem_map_of_mul_mem_map_of_forall {baseAlgebra targetAlgebra : Type*} [CommRing baseAlgebra] [CommRing targetAlgebra] [Algebra baseAlgebra targetAlgebra]
    {function localizer : targetAlgebra} (hP : ∀ (baseIdeal : Ideal baseAlgebra) (value : targetAlgebra), function * value ∈ baseIdeal.map (algebraMap baseAlgebra targetAlgebra) →
      ∃ degree : ℕ, localizer ^ degree * value ∈ baseIdeal.map (algebraMap baseAlgebra targetAlgebra))
    (Bg : Type*) [CommRing Bg] [Algebra targetAlgebra Bg] [IsLocalization.Away localizer Bg] (baseIdeal : Ideal baseAlgebra)
    (moduleElement : Bg) (hm : algebraMap targetAlgebra Bg function * moduleElement ∈ (baseIdeal.map (algebraMap baseAlgebra targetAlgebra)).map (algebraMap targetAlgebra Bg)) :
    moduleElement ∈ (baseIdeal.map (algebraMap baseAlgebra targetAlgebra)).map (algebraMap targetAlgebra Bg) := by
  obtain ⟨otherFactor, otherValue, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers localizer) moduleElement
  rw [show algebraMap targetAlgebra Bg function = IsLocalization.mk' Bg function (1 : Submonoid.powers localizer) from
    (IsLocalization.mk'_one Bg function).symm, ← IsLocalization.mk'_mul, one_mul,
    IsLocalization.mk'_mem_map_algebraMap_iff] at hm
  obtain ⟨_, ⟨moduleElement, rfl⟩, hm⟩ := hm
  obtain ⟨degree, hn⟩ := hP baseIdeal (localizer ^ moduleElement * otherFactor) (by rw [mul_left_comm]; exact hm)
  rw [IsLocalization.mk'_mem_map_algebraMap_iff]
  exact ⟨localizer ^ degree * localizer ^ moduleElement, Submonoid.mul_mem _ ⟨degree, rfl⟩ ⟨moduleElement, rfl⟩, by rw [mul_assoc]; exact hn⟩

lemma algebraMap_mem_nonZeroDivisors_of_forall {baseAlgebra targetAlgebra : Type*} [CommRing baseAlgebra] [CommRing targetAlgebra]
    [Algebra baseAlgebra targetAlgebra] {function localizer : targetAlgebra} (hP : ∀ (baseIdeal : Ideal baseAlgebra) (value : targetAlgebra), function * value ∈ baseIdeal.map (algebraMap baseAlgebra targetAlgebra) →
      ∃ degree : ℕ, localizer ^ degree * value ∈ baseIdeal.map (algebraMap baseAlgebra targetAlgebra))
    (Bg : Type*) [CommRing Bg] [Algebra targetAlgebra Bg] [IsLocalization.Away localizer Bg] :
    algebraMap targetAlgebra Bg function ∈ nonZeroDivisors Bg := by
  have hs0 : ∀ moduleElement : Bg, algebraMap targetAlgebra Bg function * moduleElement = 0 → moduleElement = 0 := fun moduleElement hm ↦ by
    simpa [Ideal.map_bot] using
      mem_map_of_mul_mem_map_of_forall hP Bg ⊥ moduleElement (by simp [Ideal.map_bot, hm])
  exact mem_nonZeroDivisors_iff.mpr ⟨hs0, fun value hx ↦ hs0 value (by rwa [mul_comm])⟩

lemma exists_isPrime_comap_includeLeft_eq {baseAlgebra targetAlgebra residueRing : Type*} [CommRing baseAlgebra] [CommRing targetAlgebra]
    [CommRing residueRing] [Algebra baseAlgebra targetAlgebra] [Algebra baseAlgebra residueRing] (hK : IsField residueRing) (prime : Ideal targetAlgebra) [prime.IsPrime]
    (hKq : RingHom.ker (algebraMap baseAlgebra residueRing) = prime.comap (algebraMap baseAlgebra targetAlgebra)) :
    ∃ primeIdeal : Ideal (targetAlgebra ⊗[baseAlgebra] residueRing), primeIdeal.IsPrime ∧
      primeIdeal.comap (Algebra.TensorProduct.includeLeftRingHom : targetAlgebra →+* targetAlgebra ⊗[baseAlgebra] residueRing) = prime := by
  classical
  let := hK.toField
  set basePrime := prime.comap (algebraMap baseAlgebra targetAlgebra)
  let κ := prime.ResidueField
  let φ₁ : baseAlgebra ⧸ basePrime →+* κ := Ideal.Quotient.lift basePrime ((algebraMap targetAlgebra κ).comp (algebraMap baseAlgebra targetAlgebra))
    fun factor ha ↦ (Ideal.algebraMap_residueField_eq_zero (I := prime)).mpr ha
  let φ₂ : baseAlgebra ⧸ basePrime →+* residueRing := Ideal.Quotient.lift basePrime (algebraMap baseAlgebra residueRing)
    fun factor ha ↦ by rw [← RingHom.mem_ker, hKq]; exact ha
  have h₁ : Function.Injective φ₁ := by
    rw [injective_iff_map_eq_zero]
    intro value hx
    obtain ⟨factor, rfl⟩ := Ideal.Quotient.mk_surjective value
    change algebraMap targetAlgebra κ (algebraMap baseAlgebra targetAlgebra factor) = 0 at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((Ideal.algebraMap_residueField_eq_zero (I := prime)).mp hx)
  have h₂ : Function.Injective φ₂ := by
    rw [injective_iff_map_eq_zero]
    intro value hx
    obtain ⟨factor, rfl⟩ := Ideal.Quotient.mk_surjective value
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [← hKq]
    exact hx
  let := φ₁.toAlgebra
  let := φ₂.toAlgebra
  have : Nontrivial (κ ⊗[baseAlgebra ⧸ basePrime] residueRing) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain (baseAlgebra ⧸ basePrime) κ residueRing h₁ h₂
  let multiplicativeSet := κ ⊗[baseAlgebra ⧸ basePrime] residueRing
  let : Algebra baseAlgebra multiplicativeSet := ((algebraMap (baseAlgebra ⧸ basePrime) multiplicativeSet).comp (Ideal.Quotient.mk basePrime)).toAlgebra
  let ψ₁ : targetAlgebra →ₐ[baseAlgebra] multiplicativeSet :=
    { (Algebra.TensorProduct.includeLeftRingHom : κ →+* multiplicativeSet).comp (algebraMap targetAlgebra κ) with
      commutes' := fun factor ↦ by
        change algebraMap targetAlgebra κ (algebraMap baseAlgebra targetAlgebra factor) ⊗ₜ (1 : residueRing) = algebraMap (baseAlgebra ⧸ basePrime) multiplicativeSet _
        rw [Algebra.TensorProduct.algebraMap_apply]
        rfl }
  let ψ₂ : residueRing →ₐ[baseAlgebra] multiplicativeSet :=
    { (Algebra.TensorProduct.includeRight : residueRing →ₐ[baseAlgebra ⧸ basePrime] multiplicativeSet).toRingHom with
      commutes' := fun factor ↦ by
        change (1 : κ) ⊗ₜ algebraMap baseAlgebra residueRing factor = algebraMap (baseAlgebra ⧸ basePrime) multiplicativeSet _
        rw [Algebra.TensorProduct.algebraMap_apply']
        rfl }
  let ψ : targetAlgebra ⊗[baseAlgebra] residueRing →ₐ[baseAlgebra] multiplicativeSet := Algebra.TensorProduct.productMap ψ₁ ψ₂
  obtain ⟨moduleType, hM⟩ := Ideal.exists_maximal multiplicativeSet
  refine ⟨moduleType.comap ψ.toRingHom, Ideal.comap_isPrime _ _, ?_⟩
  have hbot : moduleType.comap (Algebra.TensorProduct.includeLeftRingHom : κ →+* multiplicativeSet) = ⊥ :=
    Ideal.eq_bot_of_prime _
  ext otherFactor
  rw [Ideal.mem_comap, Ideal.mem_comap]
  change ψ (otherFactor ⊗ₜ 1) ∈ moduleType ↔ otherFactor ∈ prime
  simp only [ψ, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
  change (Algebra.TensorProduct.includeLeftRingHom : κ →+* multiplicativeSet) (algebraMap targetAlgebra κ otherFactor) ∈ moduleType ↔ otherFactor ∈ prime
  rw [← Ideal.mem_comap, hbot, Ideal.mem_bot, Ideal.algebraMap_residueField_eq_zero]

lemma _root_.IsLocalRing.exists_mem_span_singleton_eq {baseRing : Type*} [CommRing baseRing] [IsLocalRing baseRing]
    {scalar : baseRing} (hs : scalar ∈ nonZeroDivisors baseRing) {algebraRing : Set baseRing} (hS : Ideal.span algebraRing = Ideal.span {scalar}) :
    ∃ value ∈ algebraRing, Ideal.span {value} = Ideal.span {scalar} := by
  classical
  have hs0 : ∀ otherValue : baseRing, scalar * otherValue = 0 → otherValue = 0 := fun otherValue hy ↦ (mem_nonZeroDivisors_iff.mp hs).1 otherValue hy
  have hsS : scalar ∈ Submodule.span baseRing algebraRing := by
    have := Ideal.mem_span_singleton_self scalar
    rw [← hS] at this
    exact this
  obtain ⟨degree, multiplier, value, hcx⟩ := Submodule.mem_span_set'.mp hsS
  have hd : ∀ index, ∃ auxiliaryFactor : baseRing, auxiliaryFactor * scalar = value index := fun index ↦
    Ideal.mem_span_singleton'.mp (hS ▸ Ideal.subset_span (value index).2)
  choose auxiliaryFactor hd using hd
  have h1 : ∑ index, multiplier index * auxiliaryFactor index = 1 := by
    have condition : scalar * ∑ index, multiplier index * auxiliaryFactor index = scalar := by
      calc scalar * ∑ index, multiplier index * auxiliaryFactor index = ∑ index, multiplier index * (auxiliaryFactor index * scalar) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun index _ ↦ by ring
        _ = ∑ index, multiplier index • (value index : baseRing) := Finset.sum_congr rfl fun index _ ↦ by rw [hd index, smul_eq_mul]
        _ = scalar := hcx
    exact sub_eq_zero.mp (hs0 _ (by rw [mul_sub, condition, mul_one, sub_self]))
  obtain ⟨index, hi⟩ : ∃ index, IsUnit (auxiliaryFactor index) := by
    by_contra condition
    push Not at condition
    have : ∑ index, multiplier index * auxiliaryFactor index ∈ IsLocalRing.maximalIdeal baseRing := Ideal.sum_mem _ fun index _ ↦
      Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).mpr (condition index))
    rw [h1] at this
    exact (IsLocalRing.maximalIdeal.isMaximal baseRing).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  refine ⟨value index, (value index).2, ?_⟩
  rw [← hd index, Ideal.span_singleton_mul_left_unit hi]

lemma _root_.Module.exists_notMem_forall_smul_eq_zero_of_tensor {targetAlgebra fiberAlgebra otherPrime : Type*} [CommRing targetAlgebra]
    [CommRing fiberAlgebra] [Algebra targetAlgebra fiberAlgebra] [AddCommGroup otherPrime] [Module targetAlgebra otherPrime] [Module.Finite targetAlgebra otherPrime]
    (primeIdeal : Ideal fiberAlgebra) [primeIdeal.IsPrime] (condition : ∀ otherValue : fiberAlgebra ⊗[targetAlgebra] otherPrime, ∃ multiplierValue ∉ primeIdeal, multiplierValue • otherValue = 0) :
    ∃ parameter ∉ primeIdeal.comap (algebraMap targetAlgebra fiberAlgebra), ∀ thirdValue : otherPrime, parameter • thirdValue = 0 := by
  classical
  set prime := primeIdeal.comap (algebraMap targetAlgebra fiberAlgebra)
  by_contra hcon
  push Not at hcon
  have hq : (⟨prime, inferInstance⟩ : PrimeSpectrum targetAlgebra) ∈ Module.support targetAlgebra otherPrime := by
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    intro parameter ht
    by_contra htq
    obtain ⟨thirdValue, hz⟩ := hcon parameter htq
    exact hz (Module.mem_annihilator.mp ht thirdValue)
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hq
  let κq := prime.ResidueField
  let κP := primeIdeal.ResidueField
  let : Algebra κq κP := (Ideal.ResidueField.map prime primeIdeal (algebraMap targetAlgebra fiberAlgebra) rfl).toAlgebra
  have : IsScalarTower targetAlgebra κq κP := .of_algebraMap_eq fun otherFactor ↦ by
    change _ = Ideal.ResidueField.map prime primeIdeal (algebraMap targetAlgebra fiberAlgebra) rfl (algebraMap targetAlgebra κq otherFactor)
    rw [Ideal.ResidueField.map_algebraMap, IsScalarTower.algebraMap_apply targetAlgebra fiberAlgebra κP]
  have hnt : Nontrivial (κP ⊗[κq] (κq ⊗[targetAlgebra] otherPrime)) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_right κq κP (κq ⊗[targetAlgebra] otherPrime)
      (Algebra.linearMap κq κP) (RingHom.injective _)
  let e₁ := AlgebraTensorModule.cancelBaseChange targetAlgebra κq κP κP otherPrime
  let e₂ := AlgebraTensorModule.cancelBaseChange targetAlgebra fiberAlgebra κP κP otherPrime
  have hsub : Subsingleton (κP ⊗[fiberAlgebra] (fiberAlgebra ⊗[targetAlgebra] otherPrime)) := by
    refine subsingleton_of_forall_eq 0 fun value ↦ ?_
    induction value using TensorProduct.inductionOn with
    | add value otherValue hx hy => rw [hx, hy, add_zero]
    | tmul multiplier otherValue =>
      obtain ⟨multiplierValue, hu, huy⟩ := condition otherValue
      have hv : algebraMap fiberAlgebra κP multiplierValue ≠ 0 := fun h0 ↦
        hu ((Ideal.algebraMap_residueField_eq_zero (I := primeIdeal)).mp h0)
      rw [show multiplier = multiplierValue • (multiplier * (algebraMap fiberAlgebra κP multiplierValue)⁻¹) by
        rw [Algebra.smul_def, mul_left_comm, mul_inv_cancel₀ hv, mul_one],
        TensorProduct.smul_tmul, huy, TensorProduct.tmul_zero]
  have := (e₁.trans e₂.symm).toEquiv.nontrivial_congr.mp hnt
  exact not_subsingleton _ hsub

lemma _root_.Ideal.IsRegularPrincipal.map_atPrime_of_away {baseRing : Type*} [CommRing baseRing] (baseIdeal : Ideal baseRing)
    (primeIdeal : Ideal baseRing) [primeIdeal.IsPrime] {localizer : baseRing} (hg : localizer ∉ primeIdeal)
    (condition : (baseIdeal.map (algebraMap baseRing (Localization.Away localizer))).IsRegularPrincipal) :
    (baseIdeal.map (algebraMap baseRing (Localization.AtPrime primeIdeal))).IsRegularPrincipal := by
  let Lg := Localization.Away localizer
  let LP := Localization.AtPrime primeIdeal
  have hu : IsUnit (algebraMap baseRing LP localizer) := IsLocalization.map_units LP (⟨localizer, hg⟩ : primeIdeal.primeCompl)
  let φ : Lg →+* LP := IsLocalization.Away.lift localizer hu
  have hφ : φ.comp (algebraMap baseRing Lg) = algebraMap baseRing LP := IsLocalization.lift_comp _
  obtain ⟨scalar, hs, hJ⟩ := condition
  obtain ⟨σ, otherValue, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers localizer) scalar
  have hyP : (otherValue : baseRing) ∉ primeIdeal := by
    obtain ⟨exponent, hk⟩ := otherValue.2
    rw [← hk]
    exact fun condition ↦ hg (‹primeIdeal.IsPrime›.mem_of_pow_mem exponent condition)
  have hσs : algebraMap baseRing Lg σ = IsLocalization.mk' Lg σ otherValue * algebraMap baseRing Lg otherValue :=
    (IsLocalization.mk'_spec _ _ _).symm
  have hgk : IsUnit (algebraMap baseRing Lg otherValue) := IsLocalization.map_units Lg otherValue
  have hσ : ∀ thirdValue : Lg, algebraMap baseRing Lg σ * thirdValue = 0 → thirdValue = 0 := fun thirdValue hz ↦ by
    rw [hσs, mul_assoc] at hz
    have := (mem_nonZeroDivisors_iff.mp hs).1 _ hz
    exact (hgk.mul_right_eq_zero).mp this
  refine ⟨algebraMap baseRing LP σ, ?_, ?_⟩
  · have h0 : ∀ thirdValue : LP, algebraMap baseRing LP σ * thirdValue = 0 → thirdValue = 0 := by
      intro thirdValue hz
      obtain ⟨equivalence, multiplierValue, rfl⟩ := IsLocalization.exists_mk'_eq primeIdeal.primeCompl thirdValue
      rw [← IsLocalization.mk'_one (M := primeIdeal.primeCompl) LP σ, ← IsLocalization.mk'_mul, one_mul,
        IsLocalization.mk'_eq_zero_iff] at hz
      obtain ⟨witness, hw⟩ := hz
      have : algebraMap baseRing Lg ((witness : baseRing) * equivalence) = 0 := hσ _ (by
        rw [← map_mul, show σ * ((witness : baseRing) * equivalence) = witness * (σ * equivalence) by ring, hw, map_zero])
      obtain ⟨⟨_, degree, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers localizer) _ _).mp this
      rw [IsLocalization.mk'_eq_zero_iff]
      refine ⟨⟨localizer ^ degree * witness, primeIdeal.primeCompl.mul_mem (primeIdeal.primeCompl.pow_mem hg degree) witness.2⟩, ?_⟩
      rw [mul_assoc]
      exact hn
    exact mem_nonZeroDivisors_iff.mpr ⟨h0, fun value hx ↦ h0 value (by rwa [mul_comm])⟩
  · have hφa (value : baseRing) : φ (algebraMap baseRing Lg value) = algebraMap baseRing LP value := congr($hφ value)
    have hmap : baseIdeal.map (algebraMap baseRing LP) = (baseIdeal.map (algebraMap baseRing Lg)).map φ := by
      rw [Ideal.map_map, hφ]
    have : algebraMap baseRing LP σ = φ (IsLocalization.mk' Lg σ otherValue) * algebraMap baseRing LP otherValue := by
      rw [← hφa, ← hφa, ← map_mul, ← hσs]
    rw [hmap, hJ, Ideal.map_span, Set.image_singleton, this,
      Ideal.span_singleton_mul_right_unit (IsLocalization.map_units LP
        (⟨otherValue, hyP⟩ : primeIdeal.primeCompl))]

end Algebra

/-- An ideal with flat finitely presented quotient is locally regular principal if its fibre is
locally regular principal. -/
theorem Algebra.exists_notMem_isRegularPrincipal_of_flat_of_fiber {baseAlgebra targetAlgebra quotientAlgebra residueRing : Type*}
    [CommRing baseAlgebra] [CommRing targetAlgebra] [CommRing quotientAlgebra] [CommRing residueRing] [Algebra baseAlgebra targetAlgebra] [Algebra baseAlgebra residueRing]
    [Module.Flat baseAlgebra targetAlgebra] [Algebra.FinitePresentation baseAlgebra targetAlgebra] (hK : IsField residueRing) (coefficient : targetAlgebra →+* quotientAlgebra)
    (hr : Function.Surjective coefficient) (hflat : (coefficient.comp (algebraMap baseAlgebra targetAlgebra)).Flat)
    (hfp : (coefficient.comp (algebraMap baseAlgebra targetAlgebra)).FinitePresentation) (prime : Ideal targetAlgebra) [prime.IsPrime]
    (hKq : RingHom.ker (algebraMap baseAlgebra residueRing) = prime.comap (algebraMap baseAlgebra targetAlgebra))
    (hfib : ∀ primeIdeal : Ideal (targetAlgebra ⊗[baseAlgebra] residueRing), primeIdeal.IsPrime → ∃ localizer ∉ primeIdeal,
      (((RingHom.ker coefficient).map Algebra.TensorProduct.includeLeftRingHom).map
        (algebraMap (targetAlgebra ⊗[baseAlgebra] residueRing) (Localization.Away localizer))).IsRegularPrincipal) :
    ∃ localizer ∉ prime, ∀ (Bg : Type*) [CommRing Bg] [Algebra targetAlgebra Bg] [IsLocalization.Away localizer Bg],
      ((RingHom.ker coefficient).map (algebraMap targetAlgebra Bg)).IsRegularPrincipal := by
  classical
  set ideal := RingHom.ker coefficient
  let := (coefficient.comp (algebraMap baseAlgebra targetAlgebra)).toAlgebra
  have : Algebra.FinitePresentation baseAlgebra quotientAlgebra := hfp
  have : Module.Flat baseAlgebra quotientAlgebra := hflat
  let rA : targetAlgebra →ₐ[baseAlgebra] quotientAlgebra := { coefficient with commutes' := fun _ ↦ rfl }
  have hIfg : ideal.FG := Algebra.FinitePresentation.ker_fG_of_surjective rA hr
  by_cases hIq : ¬ ideal ≤ prime
  · obtain ⟨factor, haI, haq⟩ := Set.not_subset.mp hIq
    refine ⟨factor, haq, fun Bg _ _ _ ↦ ?_⟩
    have : ideal.map (algebraMap targetAlgebra Bg) = ⊤ := Ideal.eq_top_of_isUnit_mem _
      (Ideal.mem_map_of_mem _ haI) (IsLocalization.Away.algebraMap_isUnit factor)
    rw [this, ← Ideal.span_singleton_one]
    exact Ideal.isRegularPrincipal_span_singleton (one_mem _)
  push Not at hIq
  set fiberAlgebra := targetAlgebra ⊗[baseAlgebra] residueRing
  set ι : targetAlgebra →+* fiberAlgebra := Algebra.TensorProduct.includeLeftRingHom
  set baseIdeal := ideal.map ι
  obtain ⟨primeIdeal, hP, hPq⟩ := exists_isPrime_comap_includeLeft_eq hK prime hKq
  have hJP : ∀ (P' : Ideal fiberAlgebra) [P'.IsPrime],
      (baseIdeal.map (algebraMap fiberAlgebra (Localization.AtPrime P'))).IsRegularPrincipal := fun P' _ ↦ by
    obtain ⟨localizer, hg, condition⟩ := hfib P' ‹_›
    exact Ideal.IsRegularPrincipal.map_atPrime_of_away baseIdeal P' hg condition

  obtain ⟨scalar, hs, hsJ⟩ := hJP primeIdeal
  have hspanI : baseIdeal.map (algebraMap fiberAlgebra (Localization.AtPrime primeIdeal)) =
      Ideal.span (((algebraMap fiberAlgebra (Localization.AtPrime primeIdeal)).comp ι) '' ideal) := by
    rw [Ideal.map_map]
    rfl
  obtain ⟨_, ⟨function, hfI, rfl⟩, hfx⟩ :=
    IsLocalRing.exists_mem_span_singleton_eq hs (hspanI.symm.trans hsJ)

  have hinj : Function.Injective (ideal.subtype.lTensor fiberAlgebra) := by
    rw [LinearMap.lTensor_inj_iff_rTensor_inj]
    have hA : Function.Injective ((ideal.subtype.restrictScalars baseAlgebra).rTensor residueRing) := by
      rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
      refine LinearMap.lTensor_injective_of_exact_of_flat rA.toLinearMap hr _
        Subtype.val_injective ?_ residueRing
      rw [LinearMap.exact_iff]
      ext value
      simp [rA, ideal]
    have hcomm : ∀ value, AlgebraTensorModule.cancelBaseChange baseAlgebra targetAlgebra targetAlgebra targetAlgebra residueRing (ideal.subtype.rTensor fiberAlgebra value) =
        (ideal.subtype.restrictScalars baseAlgebra).rTensor residueRing
          (AlgebraTensorModule.cancelBaseChange baseAlgebra targetAlgebra targetAlgebra ideal residueRing value) := by
      intro value
      induction value using TensorProduct.inductionOn with
      | add value otherValue hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
      | tmul index equivalence =>
        induction equivalence using TensorProduct.induction_on with
        | zero =>
          simp only [tmul_zero,
            (AlgebraTensorModule.cancelBaseChange baseAlgebra targetAlgebra targetAlgebra targetAlgebra residueRing).map_zero,
            (AlgebraTensorModule.cancelBaseChange baseAlgebra targetAlgebra targetAlgebra ideal residueRing).map_zero, LinearMap.map_zero]
        | add equivalence e' he he' => simp only [tmul_add, map_add, he, he']
        | tmul otherFactor exponent =>
          rw [LinearMap.rTensor_tmul, AlgebraTensorModule.cancelBaseChange_tmul,
            AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.rTensor_tmul]
          rfl
    intro value otherValue hxy
    apply (AlgebraTensorModule.cancelBaseChange baseAlgebra targetAlgebra targetAlgebra ideal residueRing).injective
    apply hA
    rw [← hcomm, ← hcomm, hxy]

  let submodule : Submodule targetAlgebra ↥ideal := (Submodule.span targetAlgebra {function}).comap (Submodule.subtype ideal)
  have : Module.Finite targetAlgebra ideal := _root_.Module.Finite.iff_fg.mpr hIfg
  have hkey : ∀ index : ideal, ∃ multiplierValue ∉ primeIdeal, multiplierValue ⊗ₜ[targetAlgebra] (Submodule.Quotient.mk index : ideal ⧸ submodule) = 0 := by
    intro index
    set LP := Localization.AtPrime primeIdeal
    have hmem : algebraMap fiberAlgebra LP (ι index) ∈ Ideal.span {algebraMap fiberAlgebra LP (ι function)} := by
      change _ ∈ Ideal.span {((algebraMap fiberAlgebra LP).comp ι) function}
      rw [hfx, ← hsJ]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ index.2)
    obtain ⟨linearMap, hl⟩ := Ideal.mem_span_singleton'.mp hmem
    obtain ⟨μ, u₀, rfl⟩ := IsLocalization.exists_mk'_eq primeIdeal.primeCompl linearMap
    have h2 : algebraMap fiberAlgebra LP (μ * ι function) = algebraMap fiberAlgebra LP (u₀ * ι index) := by
      rw [map_mul, map_mul, ← hl, ← mul_assoc, mul_comm (algebraMap fiberAlgebra LP (u₀ : fiberAlgebra)),
        IsLocalization.mk'_spec_mk]
    obtain ⟨multiplier, hc⟩ := (IsLocalization.eq_iff_exists primeIdeal.primeCompl LP).mp h2
    have h3 : ((multiplier : fiberAlgebra) * u₀) ⊗ₜ[targetAlgebra] index = ((multiplier : fiberAlgebra) * μ) ⊗ₜ[targetAlgebra] (⟨function, hfI⟩ : ideal) := by
      apply hinj
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
      apply (_root_.TensorProduct.rid targetAlgebra fiberAlgebra).injective
      rw [_root_.TensorProduct.rid_tmul, _root_.TensorProduct.rid_tmul, Algebra.smul_def,
        Algebra.smul_def]
      change ι index * _ = ι function * _
      linear_combination hc.symm
    refine ⟨(multiplier : fiberAlgebra) * u₀, primeIdeal.primeCompl.mul_mem multiplier.2 u₀.2, ?_⟩
    have h4 := congr((submodule.mkQ).lTensor fiberAlgebra $h3)
    have hfF : (⟨function, hfI⟩ : ideal) ∈ submodule := by
      change function ∈ Submodule.span targetAlgebra {function}
      exact Submodule.mem_span_singleton_self function
    rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, Submodule.mkQ_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero submodule).mpr hfF, tmul_zero] at h4
    exact h4
  have hQ : ∀ otherValue : fiberAlgebra ⊗[targetAlgebra] (ideal ⧸ submodule), ∃ multiplierValue ∉ primeIdeal, multiplierValue • otherValue = 0 := by
    intro otherValue
    induction otherValue using TensorProduct.induction_on with
    | zero => exact ⟨1, fun condition ↦ hP.ne_top ((Ideal.eq_top_iff_one _).mpr condition), smul_zero _⟩
    | tmul equivalence thirdValue =>
      obtain ⟨index, rfl⟩ := Submodule.mkQ_surjective submodule thirdValue
      obtain ⟨multiplierValue, hu, condition⟩ := hkey index
      refine ⟨multiplierValue, hu, ?_⟩
      rw [smul_tmul', smul_eq_mul, mul_comm, ← smul_eq_mul, ← smul_tmul']
      change equivalence • (multiplierValue ⊗ₜ[targetAlgebra] (Submodule.Quotient.mk index : ideal ⧸ submodule)) = 0
      rw [condition, smul_zero]
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨u₁, hu₁, e₁⟩ := h₁
      obtain ⟨u₂, hu₂, e₂⟩ := h₂
      refine ⟨u₁ * u₂, fun condition ↦ (hP.mem_or_mem condition).elim hu₁ hu₂, ?_⟩
      rw [smul_add, mul_smul, mul_smul, e₂, smul_zero, add_zero, smul_comm, e₁, smul_zero]
  obtain ⟨t₁, ht₁, ht₁Q⟩ := Module.exists_notMem_forall_smul_eq_zero_of_tensor primeIdeal hQ
  have ht₁q : t₁ ∉ prime := by
    rw [← hPq]
    exact ht₁
  have ht₁I : ∀ index ∈ ideal, t₁ * index ∈ Ideal.span {function} := fun index hi ↦ by
    have := ht₁Q (Submodule.Quotient.mk ⟨index, hi⟩)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    exact Submodule.mem_comap.mp this

  have hnzdP : ∀ (P' : Ideal fiberAlgebra) [P'.IsPrime], ι t₁ ∉ P' → ∀ value : fiberAlgebra, ι function * value = 0 →
      ∃ auxiliaryValue ∉ P', auxiliaryValue * value = 0 := by
    intro P' _ ht value hx
    set L' := Localization.AtPrime P'
    obtain ⟨s', hs', hsJ'⟩ := hJP P'
    have hu : IsUnit (algebraMap fiberAlgebra L' (ι t₁)) :=
      IsLocalization.map_units L' (⟨_, ht⟩ : P'.primeCompl)
    have hspan : Ideal.span {algebraMap fiberAlgebra L' (ι function)} = Ideal.span {s'} := by
      rw [← hsJ']
      apply le_antisymm
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hfI)
      · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
        intro index hi
        rw [Ideal.mem_comap, Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ hu, ← map_mul,
          ← map_mul]
        obtain ⟨multiplier, hc⟩ := Ideal.mem_span_singleton'.mp (ht₁I index hi)
        rw [← hc, map_mul, map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have hf' := mem_nonZeroDivisors_of_span_singleton_eq hs' hspan
    have : algebraMap fiberAlgebra L' value = 0 :=
      (mem_nonZeroDivisors_iff.mp hf').1 _ (by rw [← map_mul, hx, map_zero])
    obtain ⟨auxiliaryValue, hv⟩ := (IsLocalization.map_eq_zero_iff P'.primeCompl _ _).mp this
    exact ⟨auxiliaryValue, auxiliaryValue.2, hv⟩

  let := hK.toField
  have : IsNoetherianRing fiberAlgebra := by
    have : IsNoetherianRing (residueRing ⊗[baseAlgebra] targetAlgebra) := Algebra.FiniteType.isNoetherianRing residueRing (residueRing ⊗[baseAlgebra] targetAlgebra)
    exact isNoetherianRing_of_ringEquiv (residueRing ⊗[baseAlgebra] targetAlgebra) (Algebra.TensorProduct.comm baseAlgebra residueRing targetAlgebra).toRingEquiv
  have hrad : ∀ value : fiberAlgebra, ι function * value = 0 → ∃ degree : ℕ, ι t₁ ^ degree * value = 0 := by
    intro value hx
    have : ι t₁ ∈ (Submodule.span fiberAlgebra {value}).annihilator.radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro P' ⟨hle, hP'⟩
      by_contra ht
      obtain ⟨auxiliaryValue, hv, hvx⟩ := hnzdP P' ht value hx
      exact hv (hle ((Submodule.mem_annihilator_span_singleton _ _).mpr hvx))
    obtain ⟨degree, hn⟩ := this
    exact ⟨degree, (Submodule.mem_annihilator_span_singleton _ _).mp hn⟩
  obtain ⟨generators, hG⟩ : (LinearMap.ker (LinearMap.mulLeft fiberAlgebra (ι function))).FG := IsNoetherian.noetherian _
  have hG' : ∀ otherValue ∈ generators, ∃ degree : ℕ, ι t₁ ^ degree * otherValue = 0 := fun otherValue hy ↦ by
    have condition : otherValue ∈ LinearMap.ker (LinearMap.mulLeft fiberAlgebra (ι function)) := hG ▸ Submodule.subset_span hy
    exact hrad otherValue condition
  choose! degree hn using hG'
  set auxiliaryModule := generators.sum degree
  have hN : ∀ value : fiberAlgebra, ι function * value = 0 → ι t₁ ^ auxiliaryModule * value = 0 := by
    intro value hx
    have hx' : value ∈ Submodule.span fiberAlgebra (generators : Set fiberAlgebra) := hG ▸ LinearMap.mem_ker.mpr hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem otherValue hy =>
      obtain ⟨exponent, hk⟩ : ∃ exponent, auxiliaryModule = exponent + degree otherValue :=
        ⟨auxiliaryModule - degree otherValue, (Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hy)).symm⟩
      rw [hk, pow_add, mul_assoc, hn otherValue hy, mul_zero]
    | zero => exact mul_zero _
    | add value otherValue _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul factor value _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]

  have hnotq : t₁ ^ auxiliaryModule ∉ prime := fun condition ↦ ht₁q (‹prime.IsPrime›.mem_of_pow_mem auxiliaryModule condition)
  obtain ⟨g₂, hg₂, hP₂⟩ := exists_notMem_forall_mul_mem_map prime function (t₁ ^ auxiliaryModule) hnotq hKq
    (fun value hx ↦ by
      rw [Algebra.TensorProduct.smul_eq_tmul_one_mul] at hx ⊢
      change ι (t₁ ^ auxiliaryModule) * value = 0
      rw [map_pow]
      exact hN value hx)
  refine ⟨t₁ * g₂, fun condition ↦ (‹prime.IsPrime›.mem_or_mem condition).elim ht₁q hg₂, fun Bg _ _ _ ↦ ?_⟩
  have hPg : ∀ (baseIdeal : Ideal baseAlgebra) (value : targetAlgebra), function * value ∈ baseIdeal.map (algebraMap baseAlgebra targetAlgebra) →
      ∃ degree : ℕ, (t₁ * g₂) ^ degree * value ∈ baseIdeal.map (algebraMap baseAlgebra targetAlgebra) := fun baseIdeal value hx ↦ by
    obtain ⟨degree, hn⟩ := hP₂ baseIdeal value hx
    exact ⟨degree, by rw [mul_pow, mul_assoc]; exact Ideal.mul_mem_left _ _ hn⟩
  have ht₁u : IsUnit (algebraMap targetAlgebra Bg t₁) := isUnit_of_mul_isUnit_left
    (y := algebraMap targetAlgebra Bg g₂) (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit _)
  refine ⟨algebraMap targetAlgebra Bg function, algebraMap_mem_nonZeroDivisors_of_forall hPg Bg, ?_⟩
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro index hi
    rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ ht₁u, ← map_mul]
    obtain ⟨multiplier, hc⟩ := Ideal.mem_span_singleton'.mp (ht₁I index hi)
    rw [← hc, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hfI
