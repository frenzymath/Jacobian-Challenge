import Jacobian.RingTheory.Flat.Filtration
import Jacobian.RingTheory.Flat.Generic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Local flatness and regular elements

Flatness of a finite module over a finite type algebra over a noetherian ring
holds on an open neighborhood of each flat point. An element regular on a fibre
is universally regular after restricting to a suitable principal neighborhood.
-/

/-- A generalization-stable property with relative principal neighborhoods is open on a noetherian
spectrum. -/
theorem Ideal.exists_notMem_forall_of_isNoetherianRing {algebraRing : Type*} [CommRing algebraRing]
    [IsNoetherianRing algebraRing] (affineOpen : Ideal algebraRing → Prop)
    (hgen : ∀ primeIdeal otherPrime : Ideal algebraRing, primeIdeal.IsPrime → otherPrime.IsPrime → otherPrime ≤ primeIdeal → affineOpen primeIdeal → affineOpen otherPrime)
    (hloc : ∀ primeIdeal : Ideal algebraRing, primeIdeal.IsPrime → affineOpen primeIdeal →
      ∃ localizer ∉ primeIdeal, ∀ otherPrime : Ideal algebraRing, otherPrime.IsPrime → primeIdeal ≤ otherPrime → localizer ∉ otherPrime → affineOpen otherPrime)
    (primeIdeal : Ideal algebraRing) [primeIdeal.IsPrime] (hP : affineOpen primeIdeal) :
    ∃ localizer ∉ primeIdeal, ∀ otherPrime : Ideal algebraRing, otherPrime.IsPrime → localizer ∉ otherPrime → affineOpen otherPrime := by
  classical

  set baseIdeal : Ideal algebraRing := sInf {Q | Q.IsPrime ∧ ¬ affineOpen Q}
  have hJ (otherPrime : Ideal algebraRing) (hQ : otherPrime.IsPrime) (hUQ : ¬ affineOpen otherPrime) : baseIdeal ≤ otherPrime := sInf_le ⟨hQ, hUQ⟩

  have hmin : ∀ Q₀ ∈ baseIdeal.minimalPrimes, ¬ affineOpen Q₀ := by
    intro Q₀ hQ₀ hU
    have hQ₀p : Q₀.IsPrime := hQ₀.1.1
    obtain ⟨g₀, hg₀, hg₀U⟩ := hloc Q₀ hQ₀p hU
    have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing algebraRing baseIdeal
    set others := hfin.toFinset.erase Q₀
    have hnot : ¬ others.inf id ≤ Q₀ := by
      intro hle
      obtain ⟨Q₁, hQ₁, hQ₁le⟩ := (Ideal.IsPrime.inf_le' (s := others) (f := id) hQ₀p).mp hle
      obtain ⟨hne, hQ₁m⟩ := Finset.mem_erase.mp hQ₁
      rw [Set.Finite.mem_toFinset] at hQ₁m
      exact hne (le_antisymm hQ₁le (hQ₀.2 hQ₁m.1 hQ₁le))
    obtain ⟨condition, hh, hhQ₀⟩ := SetLike.not_le_iff_exists.mp hnot
    have hgh : g₀ * condition ∉ baseIdeal := fun hmem ↦
      (hQ₀p.mul_mem_iff_mem_or_mem.mp (hQ₀.1.2 hmem)).elim hg₀ hhQ₀
    have : ¬ ∀ otherPrime ∈ {Q : Ideal algebraRing | Q.IsPrime ∧ ¬ affineOpen Q}, g₀ * condition ∈ otherPrime := fun auxiliaryProperty ↦
      hgh (Submodule.mem_sInf.mpr auxiliaryProperty)
    push Not at this
    obtain ⟨Q', ⟨hQ'p, hQ'U⟩, hQ'⟩ := this
    obtain ⟨Q₁, hQ₁, hQ₁le⟩ := Ideal.exists_minimalPrimes_le (hJ Q' hQ'p hQ'U)
    have hhQ' : condition ∉ Q' := fun hm ↦ hQ' (Q'.mul_mem_left _ hm)
    have hQ₁eq : Q₁ = Q₀ := by
      by_contra hne
      have : Q₁ ∈ others := Finset.mem_erase.mpr ⟨hne, (Set.Finite.mem_toFinset _).mpr hQ₁⟩
      exact hhQ' (hQ₁le (Finset.inf_le (f := id) this hh))
    subst hQ₁eq
    exact hQ'U (hg₀U Q' hQ'p hQ₁le fun hm ↦ hQ' (Q'.mul_mem_right _ hm))

  have hV : ∀ otherPrime : Ideal algebraRing, otherPrime.IsPrime → baseIdeal ≤ otherPrime → ¬ affineOpen otherPrime := by
    intro otherPrime hQ hJQ hUQ
    obtain ⟨Q₀, hQ₀, hQ₀le⟩ := Ideal.exists_minimalPrimes_le hJQ
    exact hmin Q₀ hQ₀ (hgen otherPrime Q₀ hQ hQ₀.1.1 hQ₀le hUQ)
  obtain ⟨localizer, hgJ, hgP⟩ := SetLike.not_le_iff_exists.mp fun hle ↦ hV primeIdeal ‹_› hle hP
  refine ⟨localizer, hgP, fun otherPrime hQ hgQ ↦ ?_⟩
  by_contra hUQ
  exact hgQ (hJ otherPrime hQ hUQ hgJ)

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

namespace Module.Flat

theorem of_bijective_smul {baseRing moduleType : Type*} [CommRing baseRing] [IsDomain baseRing] [AddCommGroup moduleType] [Module baseRing moduleType]
    (condition : ∀ coefficient : baseRing, coefficient ≠ 0 → Function.Bijective (fun moduleElement : moduleType ↦ coefficient • moduleElement)) : Flat baseRing moduleType := by
  let algebraRing := nonZeroDivisors baseRing
  have : IsLocalizedModule algebraRing (LinearMap.id : moduleType →ₗ[baseRing] moduleType) :=
    { map_units := fun scalar ↦ (Module.End.isUnit_iff _).mpr (condition scalar (nonZeroDivisors.ne_zero scalar.2))
      surj := fun otherValue ↦ ⟨(otherValue, 1), by simp⟩
      exists_of_eq := fun {value otherValue} hxy ↦ ⟨1, by simpa using hxy⟩ }
  have : Flat baseRing (LocalizedModule algebraRing moduleType) :=
    (Module.flat_iff_of_isLocalization (Localization algebraRing) algebraRing _).mp inferInstance
  exact Flat.of_linearEquiv (IsLocalizedModule.iso algebraRing (LinearMap.id : moduleType →ₗ[baseRing] moduleType)).symm

variable {baseRing : Type*} {moduleType : Type*} [CommRing baseRing] [AddCommGroup moduleType] [Module baseRing moduleType]

theorem lTensor_subtype_injective_of_bijective_smul (basePrime : Ideal baseRing) [basePrime.IsPrime]
    (hM : ∀ coefficient ∉ basePrime, Function.Bijective (fun moduleElement : moduleType ↦ coefficient • moduleElement)) {auxiliaryModule : Type*} [AddCommGroup auxiliaryModule]
    [Module baseRing auxiliaryModule] (hN : ∀ index ∈ basePrime, ∀ degree : auxiliaryModule, index • degree = 0) (N' : Submodule baseRing auxiliaryModule) :
    Function.Injective (N'.subtype.lTensor moduleType) := by
  have : Flat (baseRing ⧸ basePrime) (moduleType ⧸ basePrime • (⊤ : Submodule baseRing moduleType)) := by
    refine of_bijective_smul fun coefficient hr ↦ ?_
    obtain ⟨coefficient, rfl⟩ := Ideal.Quotient.mk_surjective coefficient
    have hrp : coefficient ∉ basePrime := fun condition ↦ hr (Ideal.Quotient.eq_zero_iff_mem.mpr condition)
    let equivalence := LinearEquiv.ofBijective (DistribSMul.toLinearMap baseRing moduleType coefficient) (hM coefficient hrp)
    have hsmul (moduleElement : moduleType) : (Ideal.Quotient.mk basePrime coefficient) •
        (Submodule.Quotient.mk moduleElement : moduleType ⧸ basePrime • (⊤ : Submodule baseRing moduleType)) =
          Submodule.Quotient.mk (coefficient • moduleElement) := rfl
    constructor
    · intro value otherValue hxy
      induction value using Submodule.Quotient.induction_on with | H value =>
      induction otherValue using Submodule.Quotient.induction_on with | H otherValue =>
      simp only [hsmul, Submodule.Quotient.eq] at hxy ⊢
      have := Submodule.smul_top_le_comap_smul_top basePrime equivalence.symm.toLinearMap hxy
      rw [Submodule.mem_comap, ← smul_sub] at this
      convert this using 1
      exact (equivalence.symm_apply_apply (value - otherValue)).symm
    · intro value
      induction value using Submodule.Quotient.induction_on with | H value =>
      refine ⟨Submodule.Quotient.mk (equivalence.symm value), ?_⟩
      change _ • _ = _
      rw [hsmul]
      congr 1
      exact equivalence.apply_symm_apply value
  exact lTensor_subtype_injective_of_smul_eq_zero basePrime hN N'

end Module.Flat

namespace Module

variable {baseRing algebraRing moduleType : Type*} [CommRing baseRing] [CommRing algebraRing] [Algebra baseRing algebraRing] [AddCommGroup moduleType] [Module baseRing moduleType]
  [Module algebraRing moduleType] [IsScalarTower baseRing algebraRing moduleType]

lemma lTensor_injective_iff_of_isLocalizedModule (multiplicativeSet : Submonoid algebraRing) {localizedModule : Type*} [AddCommGroup localizedModule]
    [Module baseRing localizedModule] [Module algebraRing localizedModule] [IsScalarTower baseRing algebraRing localizedModule] (ℓ : moduleType →ₗ[algebraRing] localizedModule) [IsLocalizedModule multiplicativeSet ℓ]
    {auxiliaryModule N' : Type*} [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule] [AddCommGroup N'] [Module baseRing N']
    (function : N' →ₗ[baseRing] auxiliaryModule) :
    Function.Injective (function.lTensor localizedModule) ↔
      ∀ otherValue : moduleType ⊗[baseRing] N', function.lTensor moduleType otherValue = 0 → ∃ parameter ∈ multiplicativeSet, parameter • otherValue = 0 := by
  let g' := AlgebraTensorModule.rTensor baseRing N' ℓ
  let localizer := AlgebraTensorModule.rTensor baseRing auxiliaryModule ℓ
  have : IsLocalizedModule multiplicativeSet g' := IsLocalizedModule.rTensor (A := algebraRing) multiplicativeSet ℓ
  have : IsLocalizedModule multiplicativeSet localizer := IsLocalizedModule.rTensor (A := algebraRing) multiplicativeSet ℓ
  let fM := AlgebraTensorModule.lTensor algebraRing moduleType function
  let fL := AlgebraTensorModule.lTensor algebraRing localizedModule function
  have hsq (otherValue : moduleType ⊗[baseRing] N') : fL (g' otherValue) = localizer (fM otherValue) := by
    induction otherValue with
    | zero => simp
    | add otherValue thirdValue hy hz => rw [map_add, map_add, map_add, map_add, hy, hz]
    | tmul moduleElement degree => rfl
  constructor
  · intro condition otherValue hy
    have h1 : g' otherValue = 0 := by
      apply condition
      rw [map_zero]
      change fL (g' otherValue) = 0
      rw [hsq]
      change localizer (function.lTensor moduleType otherValue) = 0
      rw [hy, map_zero]
    obtain ⟨parameter, ht⟩ := (IsLocalizedModule.eq_zero_iff multiplicativeSet (f := g')).mp h1
    exact ⟨parameter, parameter.2, ht⟩
  · intro condition
    rw [injective_iff_map_eq_zero]
    intro witness hw
    obtain ⟨⟨otherValue, scalar⟩, hs⟩ := IsLocalizedModule.surj multiplicativeSet g' witness
    simp only at hs
    have h1 : localizer (fM otherValue) = 0 := by
      rw [← hsq, ← hs, Submonoid.smul_def, map_smul]
      change (scalar : algebraRing) • function.lTensor localizedModule witness = 0
      rw [hw, smul_zero]
    obtain ⟨parameter, ht⟩ := (IsLocalizedModule.eq_zero_iff multiplicativeSet (f := localizer)).mp h1
    rw [Submonoid.smul_def, ← map_smul] at ht
    obtain ⟨t', ht', ht'y⟩ := condition _ ht
    have h2 : g' otherValue = 0 := by
      rw [IsLocalizedModule.eq_zero_iff multiplicativeSet]
      exact ⟨⟨t' * parameter, mul_mem ht' parameter.2⟩, by rw [Submonoid.smul_def, mul_smul]; exact ht'y⟩
    rw [h2, Submonoid.smul_def] at hs
    have hu := IsLocalizedModule.map_units g' scalar
    have : (algebraMap algebraRing (Module.End algebraRing _) scalar) witness = (algebraMap algebraRing (Module.End algebraRing _) scalar) 0 := by
      rw [map_zero, Module.algebraMap_end_apply, hs]
    exact (Module.End.isUnit_iff _).mp hu |>.1 this

lemma lTensor_localizedModule_injective_iff (multiplicativeSet : Submonoid algebraRing) {auxiliaryModule N' : Type*} [AddCommGroup auxiliaryModule]
    [Module baseRing auxiliaryModule] [AddCommGroup N'] [Module baseRing N'] (function : N' →ₗ[baseRing] auxiliaryModule) :
    Function.Injective (function.lTensor (LocalizedModule multiplicativeSet moduleType)) ↔
      ∀ otherValue : moduleType ⊗[baseRing] N', function.lTensor moduleType otherValue = 0 → ∃ parameter ∈ multiplicativeSet, parameter • otherValue = 0 :=
  lTensor_injective_iff_of_isLocalizedModule multiplicativeSet (LocalizedModule.mkLinearMap multiplicativeSet moduleType) function

lemma flat_localizedModule_iff (multiplicativeSet : Submonoid algebraRing) :
    Flat baseRing (LocalizedModule multiplicativeSet moduleType) ↔ ∀ (baseIdeal : Ideal baseRing) (otherValue : moduleType ⊗[baseRing] baseIdeal),
      baseIdeal.subtype.lTensor moduleType otherValue = 0 → ∃ parameter ∈ multiplicativeSet, parameter • otherValue = 0 := by
  rw [Flat.iff_lTensor_injective']
  exact forall_congr' fun baseIdeal ↦ lTensor_localizedModule_injective_iff multiplicativeSet baseIdeal.subtype

universe auxiliaryValue in

theorem exists_notMem_pow_smul_eq_zero [IsNoetherianRing baseRing] (basePrime : Ideal baseRing) [basePrime.IsPrime]
    [Algebra.FiniteType baseRing algebraRing] [Module.Finite algebraRing moduleType] (hM : ∀ coefficient ∈ basePrime, ∀ moduleElement : moduleType, coefficient • moduleElement = 0) :
    ∃ factor ∉ basePrime, ∀ (auxiliaryModule N' : Type auxiliaryValue) [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule] [AddCommGroup N'] [Module baseRing N'],
      (∀ coefficient ∈ basePrime, ∀ degree : auxiliaryModule, coefficient • degree = 0) → (∀ coefficient ∈ basePrime, ∀ degree : N', coefficient • degree = 0) →
      ∀ function : N' →ₗ[baseRing] auxiliaryModule, Function.Injective function →
      ∀ otherValue : moduleType ⊗[baseRing] N', function.lTensor moduleType otherValue = 0 → ∃ exponent : ℕ, factor ^ exponent • otherValue = 0 := by
  have hMt : IsTorsionBySet baseRing moduleType basePrime := fun moduleElement coefficient ↦ hM coefficient coefficient.2 moduleElement
  have hMS : IsTorsionBySet algebraRing moduleType (basePrime.map (algebraMap baseRing algebraRing)) := by
    intro moduleElement ⟨scalar, hs⟩
    change scalar • moduleElement = 0
    induction hs using Submodule.span_induction with
    | mem scalar hs =>
      obtain ⟨coefficient, hr, rfl⟩ := hs
      rw [algebraMap_smul]
      exact hM coefficient hr moduleElement
    | zero => exact zero_smul _ _
    | add scalar parameter _ _ hs ht => rw [add_smul, hs, ht, add_zero]
    | smul scalar parameter _ ht => rw [smul_eq_mul, mul_smul, ht, smul_zero]
  let := hMt.module
  let := hMS.module
  let : Algebra (baseRing ⧸ basePrime) (algebraRing ⧸ basePrime.map (algebraMap baseRing algebraRing)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower (baseRing ⧸ basePrime) (algebraRing ⧸ basePrime.map (algebraMap baseRing algebraRing)) moduleType := by
    refine ⟨fun factor scalar moduleElement ↦ ?_⟩
    obtain ⟨factor, rfl⟩ := Ideal.Quotient.mk_surjective factor
    obtain ⟨scalar, rfl⟩ := Ideal.Quotient.mk_surjective scalar
    have h1 : Ideal.Quotient.mk basePrime factor • Ideal.Quotient.mk (basePrime.map (algebraMap baseRing algebraRing)) scalar =
        Ideal.Quotient.mk (basePrime.map (algebraMap baseRing algebraRing)) (algebraMap baseRing algebraRing factor * scalar) := by
      rw [Algebra.smul_def]
      rfl
    rw [h1]
    erw [Module.IsTorsionBySet.mk_smul]
    change (algebraMap baseRing algebraRing factor * scalar) • moduleElement = factor • (scalar • moduleElement)
    rw [mul_smul, algebraMap_smul]
  have : Algebra.FiniteType baseRing (algebraRing ⧸ basePrime.map (algebraMap baseRing algebraRing)) :=
    Algebra.FiniteType.trans (S := algebraRing) ‹_› inferInstance
  have : IsScalarTower baseRing (baseRing ⧸ basePrime) (algebraRing ⧸ basePrime.map (algebraMap baseRing algebraRing)) :=
    IsScalarTower.of_algebraMap_eq fun coefficient ↦ rfl
  have : Algebra.FiniteType (baseRing ⧸ basePrime) (algebraRing ⧸ basePrime.map (algebraMap baseRing algebraRing)) :=
    Algebra.FiniteType.of_restrictScalars_finiteType baseRing _ _
  have : Module.Finite (algebraRing ⧸ basePrime.map (algebraMap baseRing algebraRing)) moduleType := by
    obtain ⟨σ, hσ⟩ := Module.Finite.fg_top (R := algebraRing) (M := moduleType)
    refine ⟨⟨σ, eq_top_iff.mpr fun moduleElement hm' ↦ ?_⟩⟩
    clear hm'
    have hm : moduleElement ∈ Submodule.span algebraRing (σ : Set moduleType) := hσ ▸ trivial
    induction hm using Submodule.span_induction with
    | mem moduleElement hm => exact Submodule.subset_span hm
    | zero => exact zero_mem _
    | add value otherValue _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul scalar moduleElement _ hm => exact Submodule.smul_mem _ (Ideal.Quotient.mk _ scalar) hm
  obtain ⟨ā, hā, hflat⟩ := exists_flat_localizedModule_powers (baseRing := baseRing ⧸ basePrime)
    (algebraRing := algebraRing ⧸ basePrime.map (algebraMap baseRing algebraRing)) moduleType
  obtain ⟨factor, rfl⟩ := Ideal.Quotient.mk_surjective ā
  refine ⟨factor, fun ha ↦ hā (Ideal.Quotient.eq_zero_iff_mem.mpr ha), ?_⟩
  intro auxiliaryModule N' _ _ _ _ hN hN' function hf otherValue hy
  let := (show IsTorsionBySet baseRing auxiliaryModule basePrime from fun degree coefficient ↦ hN coefficient coefficient.2 degree).module
  let := (show IsTorsionBySet baseRing N' basePrime from fun degree coefficient ↦ hN' coefficient coefficient.2 degree).module
  let f' : N' →ₗ[baseRing ⧸ basePrime] auxiliaryModule :=
    { toFun := function
      map_add' := function.map_add
      map_smul' := by
        rintro ⟨coefficient⟩ degree
        exact function.map_smul coefficient degree }
  have hinj : Function.Injective
      (f'.lTensor (LocalizedModule (Submonoid.powers (Ideal.Quotient.mk basePrime factor)) moduleType)) :=
    Flat.lTensor_preserves_injective_linearMap f' hf
  rw [lTensor_localizedModule_injective_iff
    (baseRing := baseRing ⧸ basePrime) (algebraRing := baseRing ⧸ basePrime)] at hinj
  have hsurj : Function.Surjective (algebraMap baseRing (baseRing ⧸ basePrime)) := Ideal.Quotient.mk_surjective
  have : CompatibleSMul baseRing (baseRing ⧸ basePrime) moduleType auxiliaryModule := CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  have : CompatibleSMul baseRing (baseRing ⧸ basePrime) moduleType N' := CompatibleSMul.of_algebraMap_surjective _ _ hsurj
  let e' := equivOfCompatibleSMul baseRing (baseRing ⧸ basePrime) baseRing moduleType N'
  let equivalence := equivOfCompatibleSMul baseRing (baseRing ⧸ basePrime) baseRing moduleType auxiliaryModule
  have hcomm (thirdValue : moduleType ⊗[baseRing ⧸ basePrime] N') : equivalence (f'.lTensor moduleType thirdValue) = function.lTensor moduleType (e' thirdValue) := by
    induction thirdValue with
    | zero => simp
    | add thirdValue witness hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]
    | tmul moduleElement degree => rfl
  obtain ⟨_, ⟨exponent, rfl⟩, ht⟩ := hinj (e'.symm otherValue) (by
    apply equivalence.injective
    rw [hcomm, LinearEquiv.apply_symm_apply, hy, map_zero])
  refine ⟨exponent, ?_⟩
  have hsmul (thirdValue : moduleType ⊗[baseRing ⧸ basePrime] N') : factor ^ exponent • thirdValue = (Ideal.Quotient.mk basePrime factor) ^ exponent • thirdValue := by
    induction thirdValue with
    | zero => simp
    | add thirdValue witness hz hw => rw [smul_add, smul_add, hz, hw]
    | tmul moduleElement degree =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← map_pow]
      rfl
  apply e'.symm.injective
  rw [map_zero, map_smul, hsmul, ht]

omit [Module baseRing moduleType] [IsScalarTower baseRing algebraRing moduleType] in
lemma _root_.Submodule.restrictScalars_map_smul_top [Module baseRing moduleType] [IsScalarTower baseRing algebraRing moduleType]
    (ideal : Ideal baseRing) :
    (ideal.map (algebraMap baseRing algebraRing) • (⊤ : Submodule algebraRing moduleType)).restrictScalars baseRing =
      ideal • (⊤ : Submodule baseRing moduleType) := by
  apply le_antisymm
  · intro value hx
    rw [Submodule.restrictScalars_mem] at hx
    induction hx using Submodule.smul_induction_on' with
    | smul factor ha moduleElement _ =>
      induction ha using Submodule.span_induction generalizing moduleElement with
      | mem factor ha =>
        obtain ⟨coefficient, hr, rfl⟩ := ha
        rw [algebraMap_smul]
        exact Submodule.smul_mem_smul hr trivial
      | zero => rw [zero_smul]; exact zero_mem _
      | add factor otherFactor _ _ ha hb =>
        rw [add_smul]; exact Submodule.add_mem _ (ha moduleElement trivial) (hb moduleElement trivial)
      | smul scalar factor _ ha => rw [smul_eq_mul, mul_comm, mul_smul]; exact ha _ trivial
    | add value _ otherValue _ hx hy => exact Submodule.add_mem _ hx hy
  · rw [Submodule.smul_le]
    intro coefficient hr moduleElement _
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul algebraRing coefficient moduleElement]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial

/-- Flatness over a noetherian base spreads from a prime to a principal neighborhood. -/
theorem Flat.exists_notMem_forall_flat_localizedModule [IsNoetherianRing baseRing]
    [Algebra.FiniteType baseRing algebraRing] [Module.Finite algebraRing moduleType] (primeIdeal : Ideal algebraRing) [primeIdeal.IsPrime]
    (hP : Flat baseRing (LocalizedModule primeIdeal.primeCompl moduleType)) :
    ∃ localizer ∉ primeIdeal, ∀ (otherPrime : Ideal algebraRing) [otherPrime.IsPrime], localizer ∉ otherPrime → Flat baseRing (LocalizedModule otherPrime.primeCompl moduleType) := by
  classical
  have : IsNoetherianRing algebraRing := Algebra.FiniteType.isNoetherianRing baseRing algebraRing
  suffices auxiliaryProperty : ∃ localizer ∉ primeIdeal, ∀ otherPrime : Ideal algebraRing, otherPrime.IsPrime → localizer ∉ otherPrime →
      ∀ [otherPrime.IsPrime], Flat baseRing (LocalizedModule otherPrime.primeCompl moduleType) by
    obtain ⟨localizer, hg, auxiliaryProperty⟩ := auxiliaryProperty
    exact ⟨localizer, hg, fun otherPrime _ hgQ ↦ auxiliaryProperty otherPrime ‹_› hgQ⟩
  refine Ideal.exists_notMem_forall_of_isNoetherianRing
    (fun otherPrime ↦ ∀ [otherPrime.IsPrime], Flat baseRing (LocalizedModule otherPrime.primeCompl moduleType)) ?_ ?_ primeIdeal (by exact hP)
  · intro otherPrime Q' hQp _ hle hQ _
    have hQ := @hQ hQp
    rw [flat_localizedModule_iff] at hQ ⊢
    intro baseIdeal otherValue hy
    obtain ⟨parameter, ht, hty⟩ := hQ baseIdeal otherValue hy
    exact ⟨parameter, fun condition ↦ ht (hle condition), hty⟩
  intro Q₀ hQ₀ hU
  have := hQ₀
  have hU := @hU hQ₀
  set p₀ := Q₀.comap (algebraMap baseRing algebraRing)

  set residueRing := LinearMap.ker (AlgebraTensorModule.lTensor algebraRing moduleType p₀.subtype)
  have : Module.Finite baseRing p₀ := IsNoetherian.finite baseRing p₀
  have : Module.Finite algebraRing (moduleType ⊗[baseRing] p₀) :=
    Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange baseRing algebraRing algebraRing moduleType p₀)
  obtain ⟨σ, hσ⟩ := (IsNoetherian.noetherian residueRing : residueRing.FG)
  have hσK : ∀ otherValue ∈ σ, ∃ parameter ∉ Q₀, parameter • otherValue = 0 := by
    intro otherValue hy
    have hyK : otherValue ∈ residueRing := hσ ▸ Submodule.subset_span hy
    obtain ⟨parameter, ht, hty⟩ := (flat_localizedModule_iff _).mp hU p₀ otherValue hyK
    exact ⟨parameter, ht, hty⟩
  choose! parameter ht hty using hσK
  set otherFactor := ∏ otherValue ∈ σ, parameter otherValue
  have hb : otherFactor ∉ Q₀ := by
    rw [Ideal.IsPrime.prod_mem_iff]
    push Not
    exact fun otherValue hy ↦ ht otherValue hy
  have hbK : ∀ otherValue ∈ residueRing, otherFactor • otherValue = 0 := by
    intro otherValue hy
    rw [← hσ] at hy
    induction hy using Submodule.span_induction with
    | mem otherValue hy =>
      change (∏ otherValue ∈ σ, parameter otherValue) • otherValue = 0
      rw [← Finset.prod_erase_mul σ parameter hy, mul_smul, hty otherValue hy, smul_zero]
    | zero => exact smul_zero _
    | add otherValue thirdValue _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul scalar otherValue _ hy => rw [smul_comm, hy, smul_zero]

  set P₀ := p₀.map (algebraMap baseRing algebraRing) • (⊤ : Submodule algebraRing moduleType)
  have hkill : ∀ coefficient ∈ p₀, ∀ moduleElement : moduleType ⧸ P₀, coefficient • moduleElement = 0 := by
    intro coefficient hr moduleElement
    induction moduleElement using Submodule.Quotient.induction_on with
    | H moduleElement =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← algebraMap_smul algebraRing coefficient moduleElement]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
  obtain ⟨factor, ha, hGF⟩ := exists_notMem_pow_smul_eq_zero.{_, _, _, _}
    (algebraRing := algebraRing) p₀ (moduleType := moduleType ⧸ P₀) hkill
  have ha' : algebraMap baseRing algebraRing factor ∉ Q₀ := ha
  refine ⟨otherFactor * algebraMap baseRing algebraRing factor, fun condition ↦ (hQ₀.mul_mem_iff_mem_or_mem.mp condition).elim hb ha', ?_⟩
  intro otherPrime hQ hle hg _
  have hbQ : otherFactor ∉ otherPrime := fun condition ↦ hg (otherPrime.mul_mem_right _ condition)
  have haQ : algebraMap baseRing algebraRing factor ∉ otherPrime := fun condition ↦ hg (otherPrime.mul_mem_left _ condition)

  have hπ : (Submodule.restrictScalars baseRing P₀) = p₀ • (⊤ : Submodule baseRing moduleType) :=
    Submodule.restrictScalars_map_smul_top p₀
  let φ : (moduleType ⧸ p₀ • (⊤ : Submodule baseRing moduleType)) ≃ₗ[baseRing] moduleType ⧸ P₀ :=
    (Submodule.quotEquivOfEq _ _ hπ.symm).trans (Submodule.Quotient.restrictScalarsEquiv baseRing P₀)
  have hbij (auxiliaryModule : Type u_1) [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule] (hN : ∀ coefficient ∈ p₀, ∀ degree : auxiliaryModule, coefficient • degree = 0) :
      Function.Bijective ((P₀.mkQ.restrictScalars baseRing).rTensor auxiliaryModule) := by
    have : (P₀.mkQ.restrictScalars baseRing).rTensor auxiliaryModule =
        φ.toLinearMap.rTensor auxiliaryModule ∘ₗ (p₀ • (⊤ : Submodule baseRing moduleType)).mkQ.rTensor auxiliaryModule := by
      rw [← LinearMap.rTensor_comp]
      rfl
    rw [this, LinearMap.coe_comp]
    exact (LinearEquiv.bijective (φ.rTensor auxiliaryModule)).comp
      (Flat.bijective_rTensor_mkQ_of_smul_eq_zero p₀ hN)
  have hjac : p₀.map (algebraMap baseRing (Localization.AtPrime otherPrime)) ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.map_le_iff_le_comap]
    intro coefficient hr
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply baseRing algebraRing (Localization.AtPrime otherPrime),
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime otherPrime) otherPrime]
    exact hle hr
  refine Flat.of_lTensor_injective_of_forall
    (algebraRing := Localization.AtPrime otherPrime) p₀ hjac ?_ ?_
  · intro auxiliaryModule _ _ hN N'
    rw [lTensor_localizedModule_injective_iff]
    intro otherValue hy
    have hN' : ∀ coefficient ∈ p₀, ∀ degree : N', coefficient • degree = 0 := fun coefficient hr degree ↦ Subtype.ext (hN coefficient hr degree)
    set π := P₀.mkQ.restrictScalars baseRing
    have h1 : N'.subtype.lTensor (moduleType ⧸ P₀) (π.rTensor N' otherValue) = 0 := by
      rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
        LinearMap.comp_apply, hy, map_zero]
    obtain ⟨exponent, hk⟩ := hGF auxiliaryModule N' hN hN' N'.subtype Subtype.val_injective _ h1
    refine ⟨algebraMap baseRing algebraRing factor ^ exponent, fun condition ↦ haQ (hQ.mem_of_pow_mem exponent condition), ?_⟩
    apply (hbij (↥N') hN').1
    rw [map_zero, ← map_pow, algebraMap_smul, map_smul, hk]
  · rw [lTensor_localizedModule_injective_iff]
    intro otherValue hy
    exact ⟨otherFactor, hbQ, hbK otherValue hy⟩

omit [AddCommGroup moduleType] [Module baseRing moduleType] [Module algebraRing moduleType] [IsScalarTower baseRing algebraRing moduleType] in

lemma _root_.Ideal.mem_map_smul_top_iff {baseAlgebra : Type*} [CommRing baseAlgebra] [Algebra baseRing baseAlgebra] [Algebra baseAlgebra algebraRing]
    [IsScalarTower baseRing baseAlgebra algebraRing] (ideal : Ideal baseRing) (otherValue : algebraRing) :
    otherValue ∈ (ideal.map (algebraMap baseRing baseAlgebra) • (⊤ : Submodule baseAlgebra algebraRing)) ↔ otherValue ∈ ideal.map (algebraMap baseRing algebraRing) := by
  constructor
  · intro hy
    induction hy using Submodule.smul_induction_on' with
    | smul factor ha otherFactor _ =>
      rw [Algebra.smul_def]
      refine Ideal.mul_mem_right _ _ ?_
      have : (ideal.map (algebraMap baseRing baseAlgebra)).map (algebraMap baseAlgebra algebraRing) = ideal.map (algebraMap baseRing algebraRing) := by
        rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      exact this ▸ Ideal.mem_map_of_mem _ ha
    | add value _ otherValue _ hx hy => exact Ideal.add_mem _ hx hy
  · intro hy
    have hmul : ∀ otherFactor : algebraRing, ∀ thirdValue ∈ (ideal.map (algebraMap baseRing baseAlgebra) • (⊤ : Submodule baseAlgebra algebraRing)),
        otherFactor * thirdValue ∈ (ideal.map (algebraMap baseRing baseAlgebra) • (⊤ : Submodule baseAlgebra algebraRing)) := by
      intro otherFactor thirdValue hz
      induction hz using Submodule.smul_induction_on' with
      | smul factor ha multiplier _ =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem_smul ha trivial
      | add value _ otherValue _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    induction hy using Submodule.span_induction with
    | mem otherValue hy =>
      obtain ⟨coefficient, hr, rfl⟩ := hy
      rw [IsScalarTower.algebraMap_apply baseRing baseAlgebra algebraRing, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) trivial
    | zero => exact zero_mem _
    | add value otherValue _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul otherFactor otherValue _ hy => exact hmul otherFactor otherValue hy

omit [AddCommGroup moduleType] [Module baseRing moduleType] [Module algebraRing moduleType] [IsScalarTower baseRing algebraRing moduleType] in

/-- A fibrewise regular element gives a flat quotient on a principal neighborhood. -/
theorem _root_.Algebra.exists_notMem_flat_localizedModule_quotient [IsNoetherianRing baseRing]
    [Algebra.FiniteType baseRing algebraRing] (prime : Ideal algebraRing) [prime.IsPrime] [Flat baseRing (Localization.AtPrime prime)] (function : algebraRing)
    (hfib : ∀ moduleElement : Localization.AtPrime prime,
      algebraMap algebraRing _ function * moduleElement ∈ (prime.comap (algebraMap baseRing algebraRing)).map (algebraMap baseRing _) →
        moduleElement ∈ (prime.comap (algebraMap baseRing algebraRing)).map (algebraMap baseRing (Localization.AtPrime prime))) :
    ∃ localizer ∉ prime, (∀ value : algebraRing, function * value = 0 → localizer * value = 0) ∧
      Flat baseRing (LocalizedModule (Submonoid.powers localizer) (algebraRing ⧸ Ideal.span {function})) := by
  classical
  have : IsNoetherianRing algebraRing := Algebra.FiniteType.isNoetherianRing baseRing algebraRing
  set basePrime := prime.comap (algebraMap baseRing algebraRing)
  set Sq := Localization.AtPrime prime
  let φR : Localization.AtPrime basePrime →+* Sq := Localization.localRingHom basePrime prime (algebraMap baseRing algebraRing) rfl
  let : Algebra (Localization.AtPrime basePrime) Sq := φR.toAlgebra
  have : IsScalarTower baseRing (Localization.AtPrime basePrime) Sq := IsScalarTower.of_algebraMap_eq fun coefficient ↦ by
    rw [IsScalarTower.algebraMap_apply baseRing algebraRing Sq]
    exact (Localization.localRingHom_to_map basePrime prime (algebraMap baseRing algebraRing) rfl coefficient).symm
  have : IsLocalHom (algebraMap (Localization.AtPrime basePrime) Sq) :=
    Localization.isLocalHom_localRingHom basePrime prime (algebraMap baseRing algebraRing) rfl
  have : Flat (Localization.AtPrime basePrime) Sq :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime basePrime) basePrime.primeCompl Sq).mpr
      inferInstance
  set scalar := algebraMap algebraRing Sq function
  set mR := IsLocalRing.maximalIdeal (Localization.AtPrime basePrime)
  have hmax : mR.map (algebraMap _ Sq) ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.map_le_iff_le_comap]
    intro value hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun condition ↦ (IsLocalRing.mem_maximalIdeal _).mp hx (isUnit_of_map_unit _ _ condition)
  have hmR : mR = basePrime.map (algebraMap baseRing (Localization.AtPrime basePrime)) :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hs : ∀ moduleElement : Sq, scalar • moduleElement ∈ mR • (⊤ : Submodule (Localization.AtPrime basePrime) Sq) →
      moduleElement ∈ mR • (⊤ : Submodule (Localization.AtPrime basePrime) Sq) := by
    intro moduleElement
    rw [hmR, Ideal.mem_map_smul_top_iff, Ideal.mem_map_smul_top_iff, smul_eq_mul]
    exact hfib moduleElement
  have key :=
    Flat.rTensor_toLinearMap_injective
      (baseRing := Localization.AtPrime basePrime) (moduleType := Sq) mR hmax scalar hs
  set φ := DistribSMul.toLinearMap (Localization.AtPrime basePrime) Sq scalar

  have hreg : ∀ moduleElement : Sq, scalar * moduleElement = 0 → moduleElement = 0 := by
    intro moduleElement hm
    have condition := key (Localization.AtPrime basePrime) (a₁ := moduleElement ⊗ₜ 1) (a₂ := 0) (by
      rw [map_zero, LinearMap.rTensor_tmul]
      simp [φ, smul_eq_mul, hm])
    simpa using congr(TensorProduct.rid _ Sq $condition)

  have hq : Flat (Localization.AtPrime basePrime) (Sq ⧸ LinearMap.range φ) := by
    refine Flat.quotient_range φ fun baseIdeal moduleElement hm ↦ ?_
    let equivalence := TensorProduct.tensorQuotEquivQuotSMul Sq baseIdeal
    have he (value : Sq ⊗[Localization.AtPrime basePrime] (Localization.AtPrime basePrime ⧸ baseIdeal)) :
        equivalence (φ.rTensor _ value) = (baseIdeal • (⊤ : Submodule (Localization.AtPrime basePrime) Sq)).mapQ (baseIdeal • ⊤) φ
          (fun otherValue hy ↦ by
            rw [Submodule.mem_comap]
            change scalar • otherValue ∈ baseIdeal • (⊤ : Submodule (Localization.AtPrime basePrime) Sq)
            induction hy using Submodule.smul_induction_on' with
            | smul coefficient hr otherValue _ => rw [smul_comm]; exact Submodule.smul_mem_smul hr trivial
            | add otherValue _ thirdValue _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz) (equivalence value) := by
      induction value with
      | zero => simp
      | add value otherValue hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
      | tmul otherValue coefficient =>
        obtain ⟨coefficient, rfl⟩ := Ideal.Quotient.mk_surjective coefficient
        simp [equivalence, φ, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]
    have h0 : φ.rTensor _ (equivalence.symm (Submodule.Quotient.mk moduleElement)) = 0 := by
      apply equivalence.injective
      rw [he, LinearEquiv.apply_symm_apply, Submodule.mapQ_apply, map_zero,
        Submodule.Quotient.mk_eq_zero]
      exact hm
    have := key (Localization.AtPrime basePrime ⧸ baseIdeal) (h0.trans (map_zero _).symm)
    rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at this
    exact this
  have hqR : Flat baseRing (Sq ⧸ LinearMap.range φ) := Flat.trans baseRing (Localization.AtPrime basePrime) _

  set quotientAlgebra := algebraRing ⧸ Ideal.span {function}
  let ψ := (Ideal.span {function} : Submodule algebraRing algebraRing).toLocalizedQuotient' Sq prime.primeCompl
    (Algebra.linearMap algebraRing Sq)
  let e₁ : LocalizedModule prime.primeCompl quotientAlgebra ≃ₗ[algebraRing] Sq ⧸ (Ideal.span {function} : Submodule algebraRing algebraRing).localized'
      Sq prime.primeCompl (Algebra.linearMap algebraRing Sq) := IsLocalizedModule.iso prime.primeCompl ψ
  have hloc : (Ideal.span {function} : Submodule algebraRing algebraRing).localized' Sq prime.primeCompl
      (Algebra.linearMap algebraRing Sq) = Submodule.span Sq {scalar} := by
    rw [Submodule.localized'_span, Set.image_singleton]
    rfl
  have hrange : (Submodule.span Sq {scalar}).restrictScalars (Localization.AtPrime basePrime) =
      LinearMap.range φ := by
    ext value
    rw [Submodule.restrictScalars_mem, ← Ideal.span, Ideal.mem_span_singleton', LinearMap.mem_range]
    exact ⟨fun ⟨factor, ha⟩ ↦ ⟨factor, by rw [← ha, mul_comm]; rfl⟩,
      fun ⟨factor, ha⟩ ↦ ⟨factor, by rw [← ha, mul_comm]; rfl⟩⟩
  let e₂ : (Sq ⧸ Submodule.span Sq {scalar}) ≃ₗ[Localization.AtPrime basePrime] Sq ⧸ LinearMap.range φ :=
    (Submodule.Quotient.restrictScalarsEquiv _ _).symm.trans (Submodule.quotEquivOfEq _ _ hrange)
  have hflatq : Flat baseRing (LocalizedModule prime.primeCompl quotientAlgebra) :=
    Flat.of_linearEquiv ((e₁.restrictScalars baseRing).trans
      (((Submodule.quotEquivOfEq _ _ hloc).restrictScalars baseRing).trans (e₂.restrictScalars baseRing)))

  obtain ⟨g₁, hg₁, hopen⟩ := Flat.exists_notMem_forall_flat_localizedModule
    (moduleType := quotientAlgebra) prime hflatq
  have hC : ∀ (baseIdeal : Ideal baseRing) (otherValue : quotientAlgebra ⊗[baseRing] baseIdeal), baseIdeal.subtype.lTensor quotientAlgebra otherValue = 0 →
      ∃ degree : ℕ, g₁ ^ degree • otherValue = 0 := by
    intro baseIdeal otherValue hy
    have : g₁ ∈ (Submodule.span algebraRing {otherValue}).annihilator.radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro otherPrime ⟨haQ, hQ⟩
      by_contra hg
      obtain ⟨parameter, ht, hty⟩ := (flat_localizedModule_iff _).mp (hopen otherPrime hg) baseIdeal otherValue hy
      exact ht (haQ ((Submodule.mem_annihilator_span_singleton _ _).mpr hty))
    obtain ⟨degree, hn⟩ := this
    exact ⟨degree, (Submodule.mem_annihilator_span_singleton _ _).mp hn⟩

  set residueRing := LinearMap.ker (LinearMap.mulLeft algebraRing function)
  obtain ⟨σ, hσ⟩ := (IsNoetherian.noetherian residueRing : residueRing.FG)
  have hσK : ∀ value ∈ σ, ∃ parameter ∉ prime, parameter * value = 0 := by
    intro value hx
    have hxK : function * value = 0 := LinearMap.mem_ker.mp (hσ ▸ Submodule.subset_span hx)
    have : algebraMap algebraRing Sq value = 0 := hreg _ (by rw [← map_mul, hxK, map_zero])
    obtain ⟨⟨parameter, ht⟩, htx⟩ := (IsLocalization.map_eq_zero_iff prime.primeCompl Sq value).mp this
    exact ⟨parameter, ht, htx⟩
  choose! parameter ht hty using hσK
  set g₂ := ∏ value ∈ σ, parameter value
  have hg₂ : g₂ ∉ prime := by
    rw [Ideal.IsPrime.prod_mem_iff]
    push Not
    exact fun value hx ↦ ht value hx
  have hg₂K : ∀ value ∈ residueRing, g₂ * value = 0 := by
    intro value hx
    rw [← hσ] at hx
    induction hx using Submodule.span_induction with
    | mem value hx =>
      change (∏ value ∈ σ, parameter value) * value = 0
      rw [← Finset.prod_erase_mul σ parameter hx, mul_assoc, hty value hx, mul_zero]
    | zero => exact mul_zero _
    | add value otherValue _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul factor value _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  refine ⟨g₁ * g₂, fun condition ↦ (Ideal.IsPrime.mul_mem_iff_mem_or_mem ‹_›).mp condition |>.elim hg₁ hg₂,
    fun value hx ↦ ?_, ?_⟩
  · rw [mul_assoc, hg₂K value (LinearMap.mem_ker.mpr hx), mul_zero]
  · rw [flat_localizedModule_iff]
    intro baseIdeal otherValue hy
    obtain ⟨degree, hn⟩ := hC baseIdeal otherValue hy
    exact ⟨(g₁ * g₂) ^ degree, ⟨degree, rfl⟩, by rw [mul_pow, mul_comm, mul_smul, hn, smul_zero]⟩

omit [AddCommGroup moduleType] [Module baseRing moduleType] [Module algebraRing moduleType] [IsScalarTower baseRing algebraRing moduleType] in

/-- Multiplication by a fibrewise regular element is universally injective after restricting to a
principal neighborhood. -/
theorem _root_.Algebra.exists_notMem_forall_pow_smul_eq_zero [IsNoetherianRing baseRing]
    [Algebra.FiniteType baseRing algebraRing] (prime : Ideal algebraRing) [prime.IsPrime] [Flat baseRing (Localization.AtPrime prime)] (function : algebraRing)
    (hfib : ∀ moduleElement : Localization.AtPrime prime,
      algebraMap algebraRing _ function * moduleElement ∈ (prime.comap (algebraMap baseRing algebraRing)).map (algebraMap baseRing _) →
        moduleElement ∈ (prime.comap (algebraMap baseRing algebraRing)).map (algebraMap baseRing (Localization.AtPrime prime))) :
    ∃ localizer ∉ prime, ∀ (auxiliaryModule : Type*) [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule] (otherValue : algebraRing ⊗[baseRing] auxiliaryModule), function • otherValue = 0 →
      ∃ degree : ℕ, localizer ^ degree • otherValue = 0 := by
  classical
  obtain ⟨g₁, hg₁, hreg, hC⟩ := Algebra.exists_notMem_flat_localizedModule_quotient prime function hfib
  have hP : Flat baseRing (LocalizedModule prime.primeCompl algebraRing) := Flat.of_linearEquiv
    ((IsLocalizedModule.iso prime.primeCompl
      (Algebra.linearMap algebraRing (Localization.AtPrime prime))).restrictScalars baseRing)
  obtain ⟨g₂, hg₂, hopen⟩ := Flat.exists_notMem_forall_flat_localizedModule
    (moduleType := algebraRing) prime hP
  have hS : ∀ (baseIdeal : Ideal baseRing) (otherValue : algebraRing ⊗[baseRing] baseIdeal), baseIdeal.subtype.lTensor algebraRing otherValue = 0 →
      ∃ degree : ℕ, g₂ ^ degree • otherValue = 0 := by
    intro baseIdeal otherValue hy
    have : g₂ ∈ (Submodule.span algebraRing {otherValue}).annihilator.radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro otherPrime ⟨haQ, hQ⟩
      by_contra hg
      obtain ⟨parameter, ht, hty⟩ := (flat_localizedModule_iff _).mp (hopen otherPrime hg) baseIdeal otherValue hy
      exact ht (haQ ((Submodule.mem_annihilator_span_singleton _ _).mpr hty))
    obtain ⟨degree, hn⟩ := this
    exact ⟨degree, (Submodule.mem_annihilator_span_singleton _ _).mp hn⟩
  set localizer := g₁ * g₂
  refine ⟨localizer, fun condition ↦ (Ideal.IsPrime.mul_mem_iff_mem_or_mem ‹_›).mp condition |>.elim hg₁ hg₂, ?_⟩
  set ambientScheme := Localization.Away localizer
  have hX : Flat baseRing ambientScheme := by
    have : Flat baseRing (LocalizedModule (Submonoid.powers localizer) algebraRing) := by
      rw [flat_localizedModule_iff]
      intro baseIdeal otherValue hy
      obtain ⟨degree, hn⟩ := hS baseIdeal otherValue hy
      exact ⟨localizer ^ degree, ⟨degree, rfl⟩, by rw [mul_pow, mul_smul, hn, smul_zero]⟩
    exact Flat.of_linearEquiv ((IsLocalizedModule.iso (Submonoid.powers localizer)
      (Algebra.linearMap algebraRing ambientScheme)).restrictScalars baseRing).symm
  set scalar := algebraMap algebraRing ambientScheme function
  let φ : ambientScheme →ₗ[baseRing] ambientScheme := (LinearMap.mulLeft algebraRing scalar).restrictScalars baseRing

  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro value hx
    obtain ⟨factor, otherFactor, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers localizer) value
    change scalar * IsLocalization.mk' ambientScheme factor otherFactor = 0 at hx
    rw [show scalar = IsLocalization.mk' ambientScheme function (1 : Submonoid.powers localizer) from
      (IsLocalization.mk'_one ambientScheme function).symm, ← IsLocalization.mk'_mul, one_mul,
      IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨_, moduleElement, rfl⟩, hm⟩ := hx
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨localizer ^ (moduleElement + 1), moduleElement + 1, rfl⟩, ?_⟩
    have := hreg (localizer ^ moduleElement * factor) (by rw [← hm]; ring)
    change localizer ^ (moduleElement + 1) * factor = 0
    rw [pow_succ, show localizer ^ moduleElement * localizer * factor = g₂ * (g₁ * (localizer ^ moduleElement * factor)) by ring, this, mul_zero]

  have hflat : Flat baseRing (ambientScheme ⧸ LinearMap.range φ) := by
    have : Flat baseRing (LocalizedModule (Submonoid.powers localizer) (algebraRing ⧸ Ideal.span {function})) := by
      rw [flat_localizedModule_iff] at hC ⊢
      intro baseIdeal otherValue hy
      obtain ⟨_, ⟨degree, rfl⟩, hn⟩ := hC baseIdeal otherValue hy
      simp only at hn
      exact ⟨localizer ^ degree, ⟨degree, rfl⟩, by rw [mul_pow, mul_comm (g₁ ^ degree), mul_smul, hn, smul_zero]⟩
    let ψ := (Ideal.span {function} : Submodule algebraRing algebraRing).toLocalizedQuotient' ambientScheme (Submonoid.powers localizer)
      (Algebra.linearMap algebraRing ambientScheme)
    let e₁ : LocalizedModule (Submonoid.powers localizer) (algebraRing ⧸ Ideal.span {function}) ≃ₗ[algebraRing]
        ambientScheme ⧸ (Ideal.span {function} : Submodule algebraRing algebraRing).localized' ambientScheme (Submonoid.powers localizer)
          (Algebra.linearMap algebraRing ambientScheme) := IsLocalizedModule.iso (Submonoid.powers localizer) ψ
    have hloc : (Ideal.span {function} : Submodule algebraRing algebraRing).localized' ambientScheme (Submonoid.powers localizer)
        (Algebra.linearMap algebraRing ambientScheme) = Submodule.span ambientScheme {scalar} := by
      rw [Submodule.localized'_span, Set.image_singleton]
      rfl
    have hrange : (Submodule.span ambientScheme {scalar}).restrictScalars baseRing = LinearMap.range φ := by
      ext value
      rw [Submodule.restrictScalars_mem, ← Ideal.span, Ideal.mem_span_singleton',
        LinearMap.mem_range]
      exact ⟨fun ⟨factor, ha⟩ ↦ ⟨factor, by rw [← ha, mul_comm]; rfl⟩,
        fun ⟨factor, ha⟩ ↦ ⟨factor, by rw [← ha, mul_comm]; rfl⟩⟩
    let e₂ : (ambientScheme ⧸ Submodule.span ambientScheme {scalar}) ≃ₗ[baseRing] ambientScheme ⧸ LinearMap.range φ :=
      (Submodule.Quotient.restrictScalarsEquiv _ _).symm.trans
        (Submodule.quotEquivOfEq _ _ hrange)
    exact Flat.of_linearEquiv (((e₁.restrictScalars baseRing).trans
      ((Submodule.quotEquivOfEq _ _ hloc).restrictScalars baseRing)).trans e₂).symm
  intro auxiliaryModule _ _ otherValue hy
  have hinj : Function.Injective (φ.rTensor auxiliaryModule) := by
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
    exact LinearMap.lTensor_injective_of_exact_of_flat _ (Submodule.mkQ_surjective _) φ hφ
      (LinearMap.exact_map_mkQ_range φ) auxiliaryModule
  let ℓ := AlgebraTensorModule.rTensor baseRing auxiliaryModule (Algebra.linearMap algebraRing ambientScheme)
  have : IsLocalizedModule (Submonoid.powers localizer) ℓ :=
    IsLocalizedModule.rTensor (A := algebraRing) _ (Algebra.linearMap algebraRing ambientScheme)
  have hnat (thirdValue : algebraRing ⊗[baseRing] auxiliaryModule) : φ.rTensor auxiliaryModule (ℓ thirdValue) = ℓ (function • thirdValue) := by
    induction thirdValue with
    | zero => simp
    | add thirdValue witness hz hw => rw [map_add, map_add, hz, hw, smul_add, map_add]
    | tmul factor degree => simp [φ, ℓ, scalar, smul_tmul']
  have h0 : ℓ otherValue = 0 := hinj (by rw [hnat, hy, map_zero, map_zero])
  obtain ⟨⟨_, degree, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers localizer) (f := ℓ)).mp h0
  exact ⟨degree, hn⟩

end Module
