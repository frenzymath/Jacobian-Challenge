import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.TensorProduct.DirectLimitFG

/-!
# Generic freeness and generic flatness

A finite module over a domain becomes free on a nonempty principal open. More
generally, a finite module over a finite type algebra over a noetherian domain
becomes flat after inverting a nonzero element of the base.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Module

section IsDomain

variable {baseAlgebra moduleType : Type*} [CommRing baseAlgebra] [IsDomain baseAlgebra] [AddCommGroup moduleType] [Module baseAlgebra moduleType]

/-- A finite module over a domain becomes free after inverting a nonzero element. -/
theorem Finite.exists_free_localizedModule_powers_of_isDomain [Module.Finite baseAlgebra moduleType] :
    ∃ coefficient : baseAlgebra, coefficient ≠ 0 ∧ Module.Free (Localization (.powers coefficient)) (LocalizedModule.Away coefficient moduleType) ∧
      Module.finrank (Localization (.powers coefficient)) (LocalizedModule.Away coefficient moduleType) =
        Module.rankAtStalk (R := baseAlgebra) moduleType ⟨⊥, Ideal.isPrime_bot⟩ := by
  classical
  let residueRing := FractionRing baseAlgebra
  let function := LocalizedModule.mkLinearMap (nonZeroDivisors baseAlgebra) moduleType
  have : Module.Finite residueRing (LocalizedModule (nonZeroDivisors baseAlgebra) moduleType) :=
    Module.Finite.of_isLocalizedModule (nonZeroDivisors baseAlgebra) (Rₚ := residueRing) function
  obtain ⟨otherFactor, hb, hspan, hli⟩ := exists_linearIndependent residueRing (Set.range function)
  have : Finite otherFactor := hli.finite
  have hm (index : otherFactor) : ∃ value, function value = index := hb index.2
  choose moduleElement hm using hm
  let linearMap := Finsupp.linearCombination baseAlgebra moduleElement
  have hl : Function.Injective linearMap := by
    refine LinearIndependent.of_comp function ?_
    have : function ∘ moduleElement = ((↑) : otherFactor → _) := funext hm
    rw [this]
    exact hli.restrict_scalars' baseAlgebra

  have hrange (value : moduleType) : ∃ scalar ∈ nonZeroDivisors baseAlgebra, scalar • value ∈ LinearMap.range linearMap := by
    have hx : function value ∈ (Submodule.span baseAlgebra (Set.range moduleElement)).localized' residueRing (nonZeroDivisors baseAlgebra) function := by
      rw [Submodule.localized'_span, ← Set.range_comp]
      have : function ∘ moduleElement = ((↑) : otherFactor → _) := funext hm
      rw [this, Subtype.range_coe, hspan]
      exact Submodule.subset_span ⟨value, rfl⟩
    obtain ⟨otherValue, hy, scalar, hys⟩ := (Submodule.mem_localized' _ _ _ _ _).mp hx
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hys
    obtain ⟨multiplierValue, hu⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors baseAlgebra) hys
    refine ⟨multiplierValue * scalar, mul_mem multiplierValue.2 scalar.2, ?_⟩
    rw [Finsupp.range_linearCombination, mul_smul, ← Submonoid.smul_def, ← hu]
    exact Submodule.smul_of_tower_mem _ _ hy

  choose scalar hs hsl using hrange
  obtain ⟨σ, hσ⟩ := Module.Finite.fg_top (R := baseAlgebra) (M := moduleType)
  let coefficient := ∏ value ∈ σ, scalar value
  have hr : coefficient ∈ nonZeroDivisors baseAlgebra := prod_mem fun value _ ↦ hs value
  have hrl (value : moduleType) : coefficient • value ∈ LinearMap.range linearMap := by
    have : (σ : Set moduleType) ⊆ (LinearMap.range linearMap).comap (coefficient • LinearMap.id) := by
      intro value hx
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_coe,
        id_eq, coefficient, ← Finset.prod_erase_mul σ scalar hx, mul_smul]
      exact Submodule.smul_mem _ _ (hsl value)
    have := Submodule.span_le.mpr this
    rw [hσ] at this
    exact this trivial
  have key (multiplicativeSet : Submonoid baseAlgebra) (hrT : coefficient ∈ multiplicativeSet) (hT : multiplicativeSet ≤ nonZeroDivisors baseAlgebra) :
      Module.Free (Localization multiplicativeSet) (LocalizedModule multiplicativeSet moduleType) ∧
        Module.finrank (Localization multiplicativeSet) (LocalizedModule multiplicativeSet moduleType) = Nat.card otherFactor := by
    have : IsDomain (Localization multiplicativeSet) := IsLocalization.isDomain_localization hT
    have hbij : Function.Bijective (LocalizedModule.map multiplicativeSet linearMap) := by
      refine ⟨LocalizedModule.map_injective multiplicativeSet linearMap hl, fun otherValue ↦ ?_⟩
      induction otherValue using LocalizedModule.induction_on with
      | h value parameter =>
        obtain ⟨thirdValue, hz⟩ := hrl value
        refine ⟨LocalizedModule.mk thirdValue (⟨coefficient, hrT⟩ * parameter), ?_⟩
        rw [LocalizedModule.map_mk, hz, LocalizedModule.mk_eq]
        exact ⟨1, by simp [mul_smul, Submonoid.smul_def, smul_comm (parameter : baseAlgebra) coefficient value]⟩
    let targetAlgebra := (Finsupp.basisSingleOne.ofIsLocalizedModule (Localization multiplicativeSet) multiplicativeSet
      (LocalizedModule.mkLinearMap multiplicativeSet (otherFactor →₀ baseAlgebra))).map (LinearEquiv.ofBijective _ hbij)
    exact ⟨.of_basis targetAlgebra, Module.finrank_eq_nat_card_basis targetAlgebra⟩
  refine ⟨coefficient, nonZeroDivisors.ne_zero hr, (key _ (Submonoid.mem_powers coefficient) ?_).1, ?_⟩
  · exact (powers_le_nonZeroDivisors_of_noZeroDivisors (nonZeroDivisors.ne_zero hr))
  · rw [(key _ (Submonoid.mem_powers coefficient)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (nonZeroDivisors.ne_zero hr))).2,
      Module.rankAtStalk, (key (Ideal.primeCompl ⊥) (nonZeroDivisors.ne_zero hr)
        fun value hx ↦ mem_nonZeroDivisors_of_ne_zero hx).2]

end IsDomain

section GenericFlatness

open TensorProduct

variable {baseRing : Type*} [CommRing baseRing]

/-- Every kernel element in an ideal tensor product is killed by a power of the specified element. -/
def FlatAway (factor : baseRing) (moduleType : Type*) [AddCommGroup moduleType] [Module baseRing moduleType] : Prop :=
  ∀ (baseIdeal : Ideal baseRing) (value : moduleType ⊗[baseRing] baseIdeal), baseIdeal.subtype.lTensor moduleType value = 0 → ∃ degree : ℕ, factor ^ degree • value = 0

variable {moduleType : Type*} [AddCommGroup moduleType] [Module baseRing moduleType]

lemma flatAway_iff (factor : baseRing) :
    FlatAway factor moduleType ↔ Flat baseRing (LocalizedModule (Submonoid.powers factor) moduleType) := by
  set localizedModule := LocalizedModule (Submonoid.powers factor) moduleType
  set ℓ := LocalizedModule.mkLinearMap (Submonoid.powers factor) moduleType
  have hloc (baseIdeal : Ideal baseRing) : IsLocalizedModule (Submonoid.powers factor) (ℓ.rTensor baseIdeal) :=
    IsLocalizedModule.rTensor (A := baseRing) (Submonoid.powers factor) ℓ
  have hlocR : IsLocalizedModule (Submonoid.powers factor) (ℓ.rTensor baseRing) :=
    IsLocalizedModule.rTensor (A := baseRing) (Submonoid.powers factor) ℓ
  have hsq (baseIdeal : Ideal baseRing) : (baseIdeal.subtype.lTensor localizedModule) ∘ₗ (ℓ.rTensor baseIdeal) =
      (ℓ.rTensor baseRing) ∘ₗ (baseIdeal.subtype.lTensor moduleType) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  constructor
  · intro condition
    rw [Flat.iff_lTensor_injective']
    intro baseIdeal
    have := hloc baseIdeal
    rw [injective_iff_map_eq_zero]
    intro witness hw
    obtain ⟨⟨value, multiplier⟩, hc⟩ := IsLocalizedModule.surj (Submonoid.powers factor) (ℓ.rTensor baseIdeal) witness
    simp only at hc
    have h1 : (ℓ.rTensor baseRing) (baseIdeal.subtype.lTensor moduleType value) = 0 := by
      rw [← LinearMap.comp_apply, ← hsq, LinearMap.comp_apply, ← hc, Submonoid.smul_def,
        map_smul, hw, smul_zero]
    obtain ⟨c', hc'⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers factor)
      (f := ℓ.rTensor baseRing)).mp h1
    rw [Submonoid.smul_def, ← map_smul] at hc'
    obtain ⟨degree, hn⟩ := condition baseIdeal _ hc'
    have h2 : (ℓ.rTensor baseIdeal) value = 0 := by
      rw [IsLocalizedModule.eq_zero_iff (Submonoid.powers factor)]
      refine ⟨⟨factor ^ degree * c', mul_mem (pow_mem (Submonoid.mem_powers factor) degree) c'.2⟩, ?_⟩
      rw [Submonoid.smul_def, mul_smul, hn]
    rw [h2, Submonoid.smul_def] at hc
    have hu := IsLocalizedModule.map_units (ℓ.rTensor baseIdeal) multiplier
    have : (algebraMap baseRing (Module.End baseRing _) multiplier) witness = (algebraMap baseRing (Module.End baseRing _) multiplier) 0 := by
      rw [map_zero, Module.algebraMap_end_apply, hc]
    exact (Module.End.isUnit_iff _).mp hu |>.1 this
  · intro condition baseIdeal value hx
    have := hloc baseIdeal
    have h1 : (ℓ.rTensor baseIdeal) value = 0 := by
      apply Flat.lTensor_preserves_injective_linearMap baseIdeal.subtype Subtype.val_injective
      rw [← LinearMap.comp_apply, hsq, LinearMap.comp_apply, hx, map_zero, map_zero]
    obtain ⟨⟨_, degree, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers factor)
      (f := ℓ.rTensor baseIdeal)).mp h1
    exact ⟨degree, hn⟩

lemma FlatAway.of_dvd {factor otherFactor : baseRing} (condition : FlatAway factor moduleType) (hab : factor ∣ otherFactor) : FlatAway otherFactor moduleType := by
  obtain ⟨multiplier, rfl⟩ := hab
  intro baseIdeal value hx
  obtain ⟨degree, hn⟩ := condition baseIdeal value hx
  exact ⟨degree, by rw [mul_pow, mul_comm, mul_smul, hn, smul_zero]⟩

lemma FlatAway.of_pow {factor : baseRing} {exponent : ℕ} (condition : FlatAway (factor ^ exponent) moduleType) : FlatAway factor moduleType := by
  intro baseIdeal value hx
  obtain ⟨degree, hn⟩ := condition baseIdeal value hx
  exact ⟨exponent * degree, by rwa [pow_mul]⟩

lemma FlatAway.of_linearEquiv {auxiliaryModule : Type*} [AddCommGroup auxiliaryModule] [Module baseRing auxiliaryModule] {factor : baseRing}
    (condition : FlatAway factor moduleType) (equivalence : moduleType ≃ₗ[baseRing] auxiliaryModule) : FlatAway factor auxiliaryModule := by
  intro baseIdeal value hx
  obtain ⟨otherValue, rfl⟩ := LinearMap.rTensor_surjective baseIdeal equivalence.surjective value
  have key : equivalence.toLinearMap.rTensor baseRing (baseIdeal.subtype.lTensor moduleType otherValue) =
      baseIdeal.subtype.lTensor auxiliaryModule (equivalence.toLinearMap.rTensor baseIdeal otherValue) := by
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply]
  have : baseIdeal.subtype.lTensor moduleType otherValue = 0 := by
    apply Flat.rTensor_preserves_injective_linearMap (M := baseRing) equivalence.toLinearMap equivalence.injective
    rw [key, hx, map_zero]
  obtain ⟨degree, hn⟩ := condition baseIdeal otherValue this
  exact ⟨degree, by rw [← map_smul, hn, map_zero]⟩

lemma FlatAway.of_exact {baseAlgebra targetAlgebra : Type*} [AddCommGroup baseAlgebra] [Module baseRing baseAlgebra] [AddCommGroup targetAlgebra]
    [Module baseRing targetAlgebra] {index : baseAlgebra →ₗ[baseRing] moduleType} {basePrime : moduleType →ₗ[baseRing] targetAlgebra} (hi : Function.Injective index)
    (hp : Function.Surjective basePrime) (hex : Function.Exact index basePrime) {factor otherFactor : baseRing} (hA : FlatAway factor baseAlgebra)
    (hB : FlatAway otherFactor targetAlgebra) : FlatAway (factor * otherFactor) moduleType := by
  intro baseIdeal value hx
  have h1 : baseIdeal.subtype.lTensor targetAlgebra (basePrime.rTensor baseIdeal value) = 0 := by
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
      LinearMap.comp_apply, hx, map_zero]
  obtain ⟨degree, hn⟩ := hB baseIdeal _ h1
  rw [← map_smul] at hn
  obtain ⟨otherValue, hy⟩ := ((_root_.rTensor_exact baseIdeal hex hp) _).1 hn
  have hinj : Function.Injective (index.rTensor baseRing) :=
    Flat.rTensor_preserves_injective_linearMap index hi
  have h2 : baseIdeal.subtype.lTensor baseAlgebra otherValue = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hy, map_smul, hx, smul_zero]
  obtain ⟨moduleElement, hm⟩ := hA baseIdeal otherValue h2
  refine ⟨moduleElement + degree, ?_⟩
  have : (factor * otherFactor) ^ (moduleElement + degree) = (factor ^ degree * otherFactor ^ moduleElement) * factor ^ moduleElement * otherFactor ^ degree := by ring
  rw [this, mul_smul, ← hy, ← map_smul, mul_smul, hm, smul_zero, map_zero]

lemma FlatAway.of_iSup {factor : baseRing} (auxiliaryModule : ℕ → Submodule baseRing moduleType) (hN : Monotone auxiliaryModule)
    (htop : ∀ moduleElement : moduleType, ∃ index, moduleElement ∈ auxiliaryModule index) (condition : ∀ index, FlatAway factor (auxiliaryModule index)) : FlatAway factor moduleType := by
  have hfin (σ : Finset moduleType) : ∃ index, Submodule.span baseRing (σ : Set moduleType) ≤ auxiliaryModule index := by
    classical
    induction σ using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert moduleElement σ _ ih =>
      obtain ⟨index, hi⟩ := ih
      obtain ⟨otherIndex, hj⟩ := htop moduleElement
      refine ⟨max index otherIndex, ?_⟩
      rw [Finset.coe_insert, Submodule.span_insert, sup_le_iff, Submodule.span_singleton_le_iff_mem]
      exact ⟨hN (le_max_right index otherIndex) hj, hi.trans (hN (le_max_left index otherIndex))⟩
  intro baseIdeal value hx
  obtain ⟨primeIdeal, ⟨σ, rfl⟩, otherValue, rfl⟩ := TensorProduct.exists_of_fg value
  have := hfin σ
  obtain ⟨index, hi⟩ := this
  set thirdValue := (Submodule.inclusion hi).rTensor baseIdeal otherValue
  have hz : (auxiliaryModule index).subtype.rTensor baseIdeal thirdValue = (Submodule.span baseRing (σ : Set moduleType)).subtype.rTensor baseIdeal otherValue := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    rfl
  have hinj : Function.Injective ((auxiliaryModule index).subtype.rTensor baseRing) :=
    Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  have h2 : baseIdeal.subtype.lTensor (auxiliaryModule index) thirdValue = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, hz, hx]
  obtain ⟨degree, hn⟩ := condition index baseIdeal thirdValue h2
  exact ⟨degree, by rw [← hz, ← map_smul, hn, map_zero]⟩

universe uA uM in

private lemma exists_flatAway_of_mvPolynomial [IsNoetherianRing baseRing] [IsDomain baseRing] (degree : ℕ) :
    ∀ (baseAlgebra : Type uA) [CommRing baseAlgebra] [Algebra baseRing baseAlgebra], Nonempty (MvPolynomial (Fin degree) baseRing ≃ₐ[baseRing] baseAlgebra) →
      ∀ (moduleType : Type uM) [AddCommGroup moduleType] [Module baseAlgebra moduleType] [Module baseRing moduleType] [IsScalarTower baseRing baseAlgebra moduleType]
        [Module.Finite baseAlgebra moduleType], ∃ factor : baseRing, factor ≠ 0 ∧ FlatAway factor moduleType := by
  induction degree with
  | zero =>
    intro baseAlgebra _ _ ⟨equivalence⟩ moduleType _ _ _ _ _
    have e' : baseRing ≃ₐ[baseRing] baseAlgebra := (MvPolynomial.isEmptyAlgEquiv baseRing (Fin 0)).symm.trans equivalence
    have : Module.Finite baseRing baseAlgebra := Module.Finite.equiv e'.toLinearEquiv
    have : Module.Finite baseRing moduleType := Module.Finite.trans baseAlgebra moduleType
    obtain ⟨factor, ha, hfree, -⟩ := Module.Finite.exists_free_localizedModule_powers_of_isDomain
      (baseAlgebra := baseRing) (moduleType := moduleType)
    refine ⟨factor, ha, (flatAway_iff factor).2 ?_⟩
    exact Flat.trans baseRing (Localization (Submonoid.powers factor)) _
  | succ degree ih =>
    intro baseAlgebra _ _ ⟨equivalence⟩ moduleType _ _ _ _ _
    have : IsNoetherianRing baseAlgebra := isNoetherianRing_of_ringEquiv _ equivalence.toRingEquiv

    let ι : MvPolynomial (Fin degree) baseRing →ₐ[baseRing] baseAlgebra :=
      equivalence.toAlgHom.comp (MvPolynomial.rename Fin.castSucc)
    have hι : Function.Injective ι :=
      equivalence.injective.comp (MvPolynomial.rename_injective _ (Fin.castSucc_injective degree))
    let multiplicativeSet : Subalgebra baseRing baseAlgebra := ι.range
    have eT : MvPolynomial (Fin degree) baseRing ≃ₐ[baseRing] multiplicativeSet := AlgEquiv.ofInjective ι hι
    have : IsNoetherianRing multiplicativeSet := isNoetherianRing_of_ringEquiv _ eT.toRingEquiv
    let value : baseAlgebra := equivalence (MvPolynomial.X (Fin.last degree))
    have hT (index : Fin degree) : equivalence (MvPolynomial.X index.castSucc) ∈ multiplicativeSet :=
      ⟨MvPolynomial.X index, by simp [ι]⟩
    have hgen : ∀ otherValue : baseAlgebra, otherValue ∈ Algebra.adjoin multiplicativeSet {value} := by
      intro otherValue
      obtain ⟨basePrime, rfl⟩ := equivalence.surjective otherValue
      induction basePrime using MvPolynomial.induction_on with
      | C coefficient =>
        rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, IsScalarTower.algebraMap_apply baseRing multiplicativeSet baseAlgebra]
        exact Subalgebra.algebraMap_mem _ _
      | add basePrime prime hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
      | mul_X basePrime index hp =>
        rw [map_mul]
        refine Subalgebra.mul_mem _ hp ?_
        induction index using Fin.lastCases with
        | last => exact Algebra.subset_adjoin rfl
        | cast index => exact Subalgebra.algebraMap_mem (Algebra.adjoin multiplicativeSet {value}) (⟨_, hT index⟩ : multiplicativeSet)

    obtain ⟨σ, hσ⟩ := Module.Finite.fg_top (R := baseAlgebra) (M := moduleType)
    classical
    let gens (index : ℕ) : Finset moduleType :=
      (Finset.range (index + 1) ×ˢ σ).image fun jm ↦ value ^ jm.1 • jm.2
    let auxiliaryModule (index : ℕ) : Submodule multiplicativeSet moduleType := Submodule.span multiplicativeSet (gens index)
    have hgens_mono : Monotone gens := by
      intro index otherIndex hij
      apply Finset.image_subset_image
      apply Finset.product_subset_product_left
      exact Finset.range_subset_range.mpr (by omega)
    have hN : Monotone auxiliaryModule := fun index otherIndex hij ↦ Submodule.span_mono (by exact_mod_cast hgens_mono hij)
    have hxN (index : ℕ) : ∀ otherValue ∈ auxiliaryModule index, value • otherValue ∈ auxiliaryModule (index + 1) := by
      intro otherValue hy
      induction hy using Submodule.span_induction with
      | mem otherValue hy =>
        obtain ⟨⟨otherIndex, moduleElement⟩, hjm, rfl⟩ := Finset.mem_image.mp hy
        simp only [Finset.mem_product, Finset.mem_range] at hjm
        apply Submodule.subset_span
        refine Finset.mem_image.mpr ⟨(otherIndex + 1, moduleElement), ?_, ?_⟩
        · simp only [Finset.mem_product, Finset.mem_range]
          exact ⟨by omega, hjm.2⟩
        · simp [pow_succ', mul_smul]
      | zero => simp
      | add otherValue thirdValue _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
      | smul parameter otherValue _ hy =>
        rw [smul_comm]
        exact Submodule.smul_mem _ parameter hy
    have htop : ∀ moduleElement : moduleType, ∃ index, moduleElement ∈ auxiliaryModule index := by
      have hU : ∀ otherValue : baseAlgebra, ∀ moduleElement : moduleType, (∃ index, moduleElement ∈ auxiliaryModule index) → ∃ index, otherValue • moduleElement ∈ auxiliaryModule index := by
        intro otherValue
        induction hgen otherValue using Algebra.adjoin_induction with
        | mem otherValue hy =>
          rw [Set.mem_singleton_iff] at hy
          subst hy
          rintro moduleElement ⟨index, hi⟩
          exact ⟨index + 1, hxN index moduleElement hi⟩
        | algebraMap parameter =>
          rintro moduleElement ⟨index, hi⟩
          exact ⟨index, by rw [algebraMap_smul]; exact Submodule.smul_mem _ parameter hi⟩
        | add otherValue thirdValue _ _ hy hz =>
          intro moduleElement hm
          obtain ⟨index, hi⟩ := hy moduleElement hm
          obtain ⟨otherIndex, hj⟩ := hz moduleElement hm
          exact ⟨max index otherIndex, by
            rw [add_smul]
            exact Submodule.add_mem _ (hN (le_max_left index otherIndex) hi) (hN (le_max_right index otherIndex) hj)⟩
        | mul otherValue thirdValue _ _ hy hz =>
          intro moduleElement hm
          obtain ⟨index, hi⟩ := hz moduleElement hm
          rw [mul_smul]
          exact hy _ ⟨index, hi⟩
      intro moduleElement
      have hm : moduleElement ∈ Submodule.span baseAlgebra (σ : Set moduleType) := hσ ▸ trivial
      induction hm using Submodule.span_induction with
      | mem moduleElement hm =>
        exact ⟨0, Submodule.subset_span (Finset.mem_image.mpr
          ⟨(0, moduleElement), Finset.mem_product.mpr ⟨by simp, hm⟩, by simp⟩)⟩
      | zero => exact ⟨0, zero_mem _⟩
      | add otherValue thirdValue _ _ hy hz =>
        obtain ⟨index, hi⟩ := hy
        obtain ⟨otherIndex, hj⟩ := hz
        exact ⟨max index otherIndex, Submodule.add_mem _ (hN (le_max_left index otherIndex) hi) (hN (le_max_right index otherIndex) hj)⟩
      | smul otherValue moduleElement _ hm => exact hU otherValue moduleElement hm

    let μ (exponent : ℕ) : moduleType →ₗ[multiplicativeSet] moduleType := (LinearMap.lsmul baseAlgebra moduleType (value ^ exponent)).restrictScalars multiplicativeSet
    have hμ (exponent : ℕ) : ∀ index, ∀ otherValue ∈ auxiliaryModule index, μ exponent otherValue ∈ auxiliaryModule (index + exponent) := by
      induction exponent with
      | zero => intro index otherValue hy; simpa [μ] using hy
      | succ exponent ih' =>
        intro index otherValue hy
        have := hxN _ _ (ih' index otherValue hy)
        simpa [μ, pow_succ', mul_smul, ← add_assoc] using this

    let otherPrime (index : ℕ) := ↥(auxiliaryModule (index + 1)) ⧸ (auxiliaryModule index).comap (auxiliaryModule (index + 1)).subtype
    let ψ (index : ℕ) : ↥(auxiliaryModule 1) →ₗ[multiplicativeSet] otherPrime index :=
      ((auxiliaryModule index).comap (auxiliaryModule (index + 1)).subtype).mkQ ∘ₗ
        (μ index).restrict (p := auxiliaryModule 1) (q := auxiliaryModule (index + 1)) fun otherValue hy ↦ by
          simpa [add_comm] using hμ index 1 otherValue hy
    have hψ (index : ℕ) : (auxiliaryModule 0).comap (auxiliaryModule 1).subtype ≤ LinearMap.ker (ψ index) := by
      intro otherValue hy
      rw [LinearMap.mem_ker]
      erw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simpa [Submodule.mem_comap] using hμ index 0 otherValue hy
    let Θ (index : ℕ) : otherPrime 0 →ₗ[multiplicativeSet] otherPrime index := ((auxiliaryModule 0).comap (auxiliaryModule 1).subtype).liftQ (ψ index) (hψ index)
    have hΘ (index : ℕ) : Function.Surjective (Θ index) := by
      intro thirdValue
      induction thirdValue using Submodule.Quotient.induction_on with
      | H thirdValue =>
        have hle : auxiliaryModule (index + 1) ≤ auxiliaryModule index ⊔ (auxiliaryModule 1).map (μ index) := by
          rw [Submodule.span_le]
          intro witness hw
          obtain ⟨⟨otherIndex, moduleElement⟩, hjm, rfl⟩ := Finset.mem_image.mp hw
          simp only [Finset.mem_product, Finset.mem_range] at hjm
          rcases Nat.lt_or_ge otherIndex (index + 1) with hj | hj
          · apply Submodule.mem_sup_left
            apply Submodule.subset_span
            exact Finset.mem_image.mpr ⟨(otherIndex, moduleElement), by simp [hjm.2, hj], rfl⟩
          · obtain rfl : otherIndex = index + 1 := by omega
            apply Submodule.mem_sup_right
            refine ⟨value • moduleElement, Submodule.subset_span (Finset.mem_image.mpr ⟨(1, moduleElement), ?_, ?_⟩), ?_⟩
            · simp [hjm.2]
            · simp
            · simp [μ, smul_smul, ← pow_succ']
        obtain ⟨multiplierValue, hu, _, ⟨otherValue, hy, rfl⟩, hz⟩ := Submodule.mem_sup.mp (hle thirdValue.2)
        refine ⟨Submodule.Quotient.mk ⟨otherValue, hy⟩, ?_⟩
        erw [Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.eq, Submodule.mem_comap]
        have h' : (μ index) otherValue - (thirdValue : moduleType) = -multiplierValue := by rw [← hz]; abel
        simpa [LinearMap.coe_restrict_apply, h'] using (auxiliaryModule index).neg_mem hu
    let localizedModule (index : ℕ) : Submodule multiplicativeSet (otherPrime 0) := LinearMap.ker (Θ index)
    have hL : Monotone localizedModule := by
      refine monotone_nat_of_le_succ fun index auxiliaryValue hv ↦ ?_
      induction auxiliaryValue using Submodule.Quotient.induction_on with
      | H otherValue =>
        change Θ index _ = 0 at hv
        change Θ (index + 1) _ = 0
        erw [Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero] at hv ⊢
        rw [Submodule.mem_comap] at hv ⊢
        have := hxN index _ hv
        simpa [μ, pow_succ', mul_smul] using this
    have : IsNoetherian multiplicativeSet (otherPrime 0) := inferInstance
    obtain ⟨i₀, hi₀⟩ := monotone_stabilizes_iff_noetherian.mpr this ⟨localizedModule, hL⟩
    have hker (index : ℕ) : LinearMap.ker (Θ index) = localizedModule (min index i₀) := by
      rcases le_total index i₀ with beforeStabilization | afterStabilization
      · rw [min_eq_left beforeStabilization]
      · rw [min_eq_right afterStabilization]
        exact (hi₀ index afterStabilization).symm

    obtain ⟨a₀, ha₀, h₀⟩ := ih multiplicativeSet ⟨eT⟩ (auxiliaryModule 0)
    have hQ (otherIndex : ℕ) : ∃ otherFactor : baseRing, otherFactor ≠ 0 ∧ FlatAway otherFactor (otherPrime 0 ⧸ localizedModule otherIndex) := ih multiplicativeSet ⟨eT⟩ _
    choose otherFactor hb₀ hb using hQ
    set factor := a₀ * ∏ otherIndex ∈ Finset.range (i₀ + 1), otherFactor otherIndex
    have ha : factor ≠ 0 := mul_ne_zero ha₀ (Finset.prod_ne_zero_iff.mpr fun otherIndex _ ↦ hb₀ otherIndex)
    have hQa (index : ℕ) : FlatAway factor (otherPrime index) := by
      have hj : min index i₀ ∈ Finset.range (i₀ + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_right _ _))
      have h1 : FlatAway factor (otherPrime 0 ⧸ localizedModule (min index i₀)) :=
        (hb _).of_dvd (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem otherFactor hj) _)
      have e₁ : (otherPrime 0 ⧸ localizedModule (min index i₀)) ≃ₗ[multiplicativeSet] otherPrime index :=
        (Submodule.quotEquivOfEq _ _ (hker index).symm).trans
          ((Θ index).quotKerEquivOfSurjective (hΘ index))
      exact h1.of_linearEquiv (e₁.restrictScalars baseRing)
    have hNa (index : ℕ) : FlatAway factor (auxiliaryModule index) := by
      induction index with
      | zero => exact h₀.of_dvd (Dvd.intro _ rfl)
      | succ index ih' =>
        have e₂ : ↥(auxiliaryModule index) ≃ₗ[multiplicativeSet] ↥((auxiliaryModule index).comap (auxiliaryModule (index + 1)).subtype) :=
          (Submodule.comapSubtypeEquivOfLe (hN (Nat.le_succ index))).symm
        have h1 : FlatAway factor ↥((auxiliaryModule index).comap (auxiliaryModule (index + 1)).subtype) :=
          ih'.of_linearEquiv (e₂.restrictScalars baseRing)
        set residueRing := (auxiliaryModule index).comap (auxiliaryModule (index + 1)).subtype
        have hex : Function.Exact (residueRing.subtype.restrictScalars baseRing) (residueRing.mkQ.restrictScalars baseRing) :=
          LinearMap.exact_subtype_mkQ residueRing
        have h2 := FlatAway.of_exact (moduleType := ↥(auxiliaryModule (index + 1)))
          (targetAlgebra := otherPrime index) (index := residueRing.subtype.restrictScalars baseRing)
          (basePrime := residueRing.mkQ.restrictScalars baseRing)
          (by rw [LinearMap.coe_restrictScalars]; exact residueRing.injective_subtype)
          (by rw [LinearMap.coe_restrictScalars]; exact residueRing.mkQ_surjective) hex h1 (hQa index)
        rw [← pow_two] at h2
        exact h2.of_pow
    exact ⟨factor, ha, FlatAway.of_iSup (fun index ↦ (auxiliaryModule index).restrictScalars baseRing)
      (fun index otherIndex hij ↦ hN hij) htop hNa⟩

/-- A finite module over a finite type algebra is generically flat over a noetherian domain. -/
theorem exists_flat_localizedModule_powers [IsNoetherianRing baseRing] [IsDomain baseRing] {algebraRing : Type*}
    [CommRing algebraRing] [Algebra baseRing algebraRing] [Algebra.FiniteType baseRing algebraRing] (moduleType : Type*) [AddCommGroup moduleType] [Module baseRing moduleType]
    [Module algebraRing moduleType] [IsScalarTower baseRing algebraRing moduleType] [Module.Finite algebraRing moduleType] :
    ∃ factor : baseRing, factor ≠ 0 ∧ Flat baseRing (LocalizedModule (Submonoid.powers factor) moduleType) := by
  obtain ⟨degree, function, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  let := Module.compHom moduleType function.toRingHom
  have : IsScalarTower baseRing (MvPolynomial (Fin degree) baseRing) moduleType := by
    refine ⟨fun coefficient basePrime moduleElement ↦ ?_⟩
    change function (coefficient • basePrime) • moduleElement = coefficient • function basePrime • moduleElement
    rw [map_smul, smul_assoc]
  have : Module.Finite (MvPolynomial (Fin degree) baseRing) moduleType := by
    obtain ⟨σ, hσ⟩ := Module.Finite.fg_top (R := algebraRing) (M := moduleType)
    refine ⟨⟨σ, eq_top_iff.mpr fun moduleElement hm' ↦ ?_⟩⟩
    clear hm'
    have hm : moduleElement ∈ Submodule.span algebraRing (σ : Set moduleType) := hσ ▸ trivial
    induction hm using Submodule.span_induction with
    | mem moduleElement hm => exact Submodule.subset_span hm
    | zero => exact zero_mem _
    | add value otherValue _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul scalar moduleElement _ hm =>
      obtain ⟨basePrime, rfl⟩ := hf scalar
      exact Submodule.smul_mem _ basePrime hm
  obtain ⟨factor, ha, condition⟩ := exists_flatAway_of_mvPolynomial degree (MvPolynomial (Fin degree) baseRing)
    ⟨AlgEquiv.refl⟩ moduleType
  exact ⟨factor, ha, (flatAway_iff factor).mp condition⟩

end GenericFlatness

end Module
