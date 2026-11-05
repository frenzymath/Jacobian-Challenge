import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor products with localizations of a polynomial ring

Over an algebraically closed field, units in a polynomial localization after extending a
domain are pure tensors. Localizing the coefficient ring also preserves unique factorization.
-/

noncomputable section

universe schemeUniverse

open Polynomial TensorProduct

namespace TensorProduct

variable {baseField : Type schemeUniverse} [Field baseField]

/-- The image `1 ⊗ h` of a nonzero `h ∈ k[X]` in `D ⊗_k k[X]` is nonzero for `D` nontrivial. -/
lemma one_tmul_ne_zero (coefficientRing : Type schemeUniverse) [CommRing coefficientRing] [Nontrivial coefficientRing] [Algebra baseField coefficientRing]
    {localizer : baseField[X]} (hh : localizer ≠ 0) : (1 : coefficientRing) ⊗ₜ[baseField] localizer ≠ 0 := by
  intro H
  have := congrArg (polyEquivTensor baseField coefficientRing).symm H
  rw [polyEquivTensor_symm_apply_tmul_eq_smul, one_smul, map_zero,
    Polynomial.map_eq_zero_iff (algebraMap baseField coefficientRing).injective] at this
  exact hh this

/-- `D ⊗_k k[X] ≅ D[X]` is a domain if `D` is. -/
instance isDomain_tensor_polynomial (coefficientRing : Type schemeUniverse) [CommRing coefficientRing] [IsDomain coefficientRing] [Algebra baseField coefficientRing] : IsDomain (coefficientRing ⊗[baseField] baseField[X]) :=
  (polyEquivTensor baseField coefficientRing).toMulEquiv.symm.isDomain _

/-- Over a domain `A`, a divisor of a product of linear polynomials `X - C (v i)` is a unit
constant times a sub-product. -/
lemma exists_eq_C_mul_prod_of_dvd_prod {baseAlgebra indexType : Type*} [CommRing baseAlgebra] [IsDomain baseAlgebra] (rootValue : indexType → baseAlgebra)
    (roots : Multiset indexType) (divisor : baseAlgebra[X]) (hp : divisor ∣ (roots.map fun index ↦ X - C (rootValue index)).prod) :
    ∃ unitCoefficient : baseAlgebraˣ, ∃ selectedRoots ≤ roots, divisor = C (unitCoefficient : baseAlgebra) * (selectedRoots.map fun index ↦ X - C (rootValue index)).prod := by
  induction roots using Multiset.induction_on generalizing divisor with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero] at hp
    obtain ⟨unitCoefficient, ha, rfl⟩ := Polynomial.isUnit_iff.mp (isUnit_of_dvd_one hp)
    exact ⟨ha.unit, 0, le_rfl, by simp⟩
  | cons index roots ih =>
    obtain ⟨cofactor, hq⟩ := hp
    rw [Multiset.map_cons, Multiset.prod_cons] at hq
    have hdvd : X - C (rootValue index) ∣ divisor * cofactor := Dvd.intro _ hq
    rcases (prime_X_sub_C (rootValue index)).dvd_or_dvd hdvd with ⟨p', rfl⟩ | ⟨q', rfl⟩
    · obtain ⟨unitCoefficient, selectedRoots, ht, rfl⟩ := ih p' ⟨cofactor, mul_left_cancel₀ (X_sub_C_ne_zero (rootValue index))
        (by linear_combination hq)⟩
      refine ⟨unitCoefficient, index ::ₘ selectedRoots, Multiset.cons_le_cons index ht, ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons]
      ring
    · obtain ⟨unitCoefficient, selectedRoots, ht, rfl⟩ := ih divisor ⟨q', mul_left_cancel₀ (X_sub_C_ne_zero (rootValue index))
        (by linear_combination hq)⟩
      exact ⟨unitCoefficient, selectedRoots, ht.trans (Multiset.le_cons_self roots index), rfl⟩

/-- Let `k` be algebraically closed and `A` a `k`-algebra which is a domain. A divisor in `A[X]`
of the image of a nonzero `f ∈ k[X]` is `C a * g` for a unit `a` of `A` and a divisor `g` of `f`
in `k[X]`. -/
lemma exists_eq_C_mul_map_of_dvd_map [IsAlgClosed baseField] {baseAlgebra : Type*} [CommRing baseAlgebra] [IsDomain baseAlgebra]
    [Algebra baseField baseAlgebra] {polynomial : baseField[X]} (hf : polynomial ≠ 0) {divisor : baseAlgebra[X]} (hp : divisor ∣ polynomial.map (algebraMap baseField baseAlgebra)) :
    ∃ unitCoefficient : baseAlgebraˣ, ∃ factor : baseField[X], factor ∣ polynomial ∧ divisor = C (unitCoefficient : baseAlgebra) * factor.map (algebraMap baseField baseAlgebra) := by
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree
    (p := polynomial))
  rw [← hfac, Polynomial.map_mul, map_C, Polynomial.map_multiset_prod, Multiset.map_map] at hp
  have hu : IsUnit (C (algebraMap baseField baseAlgebra polynomial.leadingCoeff)) :=
    (((leadingCoeff_ne_zero.mpr hf).isUnit).map (algebraMap baseField baseAlgebra)).map C
  rw [hu.dvd_mul_left] at hp
  obtain ⟨unitCoefficient, selectedRoots, ht, rfl⟩ := exists_eq_C_mul_prod_of_dvd_prod (algebraMap baseField baseAlgebra) polynomial.roots divisor
    (by simpa [Function.comp_def] using hp)
  refine ⟨unitCoefficient, (selectedRoots.map fun localizedUnit ↦ X - C localizedUnit).prod, ?_, ?_⟩
  · rw [← hfac]
    exact (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map ht)).mul_left _
  · simp [Polynomial.map_multiset_prod, Multiset.map_map]

/-- The isomorphism `D ⊗_k k[X]_h ≃ (D ⊗_k k[X])_h` of `D`-algebras. -/
noncomputable def tensorAwayEquiv (coefficientRing : Type schemeUniverse) [CommRing coefficientRing] [Algebra baseField coefficientRing] (localizer : baseField[X]) :
    coefficientRing ⊗[baseField] Localization.Away localizer ≃ₐ[coefficientRing] Localization.Away ((1 : coefficientRing) ⊗ₜ[baseField] localizer) :=
  IsLocalization.Away.tensorProductEquivTMulRight baseField coefficientRing localizer _

/-- `D ⊗_k k[X]_h` is a domain if `D` is a domain and `h ≠ 0`. -/
theorem isDomain_localizationAway (coefficientRing : Type schemeUniverse) [CommRing coefficientRing] [IsDomain coefficientRing] [Algebra baseField coefficientRing]
    {localizer : baseField[X]} (hh : localizer ≠ 0) : IsDomain (coefficientRing ⊗[baseField] Localization.Away localizer) :=
  haveI : IsDomain (Localization.Away ((1 : coefficientRing) ⊗ₜ[baseField] localizer)) :=
    IsLocalization.isDomain_localization
      (powers_le_nonZeroDivisors_of_noZeroDivisors (one_tmul_ne_zero coefficientRing hh))
  (tensorAwayEquiv coefficientRing localizer).toMulEquiv.isDomain _

/-- `D ⊗_k k[X]_h` is a unique factorization monoid if `D` is a unique factorization domain:
it is a localization of `D ⊗_k k[X] = D[X]`. -/
theorem uniqueFactorizationMonoid_localizationAway (coefficientRing : Type schemeUniverse) [CommRing coefficientRing] [IsDomain coefficientRing]
    [Algebra baseField coefficientRing] [UniqueFactorizationMonoid coefficientRing] (localizer : baseField[X]) :
    UniqueFactorizationMonoid (coefficientRing ⊗[baseField] Localization.Away localizer) :=
  haveI : UniqueFactorizationMonoid (coefficientRing ⊗[baseField] baseField[X]) :=
    (polyEquivTensor baseField coefficientRing).toMulEquiv.uniqueFactorizationMonoid inferInstance
  (tensorAwayEquiv coefficientRing localizer).toMulEquiv.symm.uniqueFactorizationMonoid inferInstance

/-- Let `A` be a `k`-algebra, `𝔭` a prime of `A` whose localization `A_𝔭` is a unique
factorization domain, and `B ≅ A ⊗_k k[X]_h` as `A`-algebras with `h ≠ 0`. Then the localization
of `B` at the image of `A \ 𝔭` is a unique factorization domain, being `A_𝔭 ⊗_k k[X]_h`. -/
theorem uniqueFactorizationMonoid_localization_atPrime {baseAlgebra coefficientRing targetAlgebra : Type schemeUniverse} [CommRing baseAlgebra]
    [Algebra baseField baseAlgebra] [CommRing coefficientRing] [Algebra baseAlgebra coefficientRing] [Algebra baseField coefficientRing] [IsScalarTower baseField baseAlgebra coefficientRing] (𝔭 : Ideal baseAlgebra)
    [𝔭.IsPrime] [IsLocalization.AtPrime coefficientRing 𝔭] [IsDomain coefficientRing] [UniqueFactorizationMonoid coefficientRing]
    [CommRing targetAlgebra] [Algebra baseAlgebra targetAlgebra] {localizer : baseField[X]} (hh : localizer ≠ 0)
    (tensorComparison : baseAlgebra ⊗[baseField] Localization.Away localizer ≃ₐ[baseAlgebra] targetAlgebra) :
    IsDomain (Localization (Algebra.algebraMapSubmonoid targetAlgebra 𝔭.primeCompl)) ∧
      UniqueFactorizationMonoid (Localization (Algebra.algebraMapSubmonoid targetAlgebra 𝔭.primeCompl)) := by
  let polynomial : Localization (Algebra.algebraMapSubmonoid targetAlgebra 𝔭.primeCompl) ≃+*
      coefficientRing ⊗[baseField] Localization.Away localizer :=
    (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid targetAlgebra 𝔭.primeCompl) _
      (targetAlgebra ⊗[baseAlgebra] coefficientRing)).toRingEquiv.trans <|
    (Algebra.TensorProduct.comm baseAlgebra targetAlgebra coefficientRing).toRingEquiv.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := baseAlgebra) (A₁ := coefficientRing)) tensorComparison.symm).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange baseField baseAlgebra coefficientRing coefficientRing _).toRingEquiv
  have := isDomain_localizationAway coefficientRing hh
  exact ⟨polynomial.toMulEquiv.isDomain _,
    polynomial.toMulEquiv.symm.uniqueFactorizationMonoid (uniqueFactorizationMonoid_localizationAway coefficientRing localizer)⟩

/-- **Units of `A ⊗_k k[X]_h`.** Let `k` be algebraically closed, `A` a `k`-algebra which is a
domain and `h ≠ 0`. Every unit of `A ⊗_k k[X]_h = A[X]_h` is of the form `a ⊗ r` with `a` a unit
of `A` and `r` a unit of `k[X]_h`: writing `h = c ∏ (X - αᵢ)`, a divisor of a power of `h` in
`A[X]` is a unit of `A` times a product of the primes `X - αᵢ`. -/
theorem exists_units_eq_tmul [IsAlgClosed baseField] (baseAlgebra : Type schemeUniverse) [CommRing baseAlgebra] [IsDomain baseAlgebra] [Algebra baseField baseAlgebra]
    {localizer : baseField[X]} (hh : localizer ≠ 0) (unitValue : (baseAlgebra ⊗[baseField] Localization.Away localizer)ˣ) :
    ∃ (unitCoefficient : baseAlgebraˣ) (localizedUnit : (Localization.Away localizer)ˣ),
      (unitValue : baseAlgebra ⊗[baseField] Localization.Away localizer) = (unitCoefficient : baseAlgebra) ⊗ₜ (localizedUnit : Localization.Away localizer) := by
  let : Algebra (baseAlgebra ⊗[baseField] baseField[X]) (baseAlgebra ⊗[baseField] Localization.Away localizer) :=
    (Algebra.TensorProduct.map (AlgHom.id baseField baseAlgebra)
      (IsScalarTower.toAlgHom baseField baseField[X] (Localization.Away localizer))).toAlgebra
  have : IsScalarTower baseAlgebra (baseAlgebra ⊗[baseField] baseField[X]) (baseAlgebra ⊗[baseField] Localization.Away localizer) := by
    refine IsScalarTower.of_algebraMap_eq (R := baseAlgebra)
      (S := baseAlgebra ⊗[baseField] baseField[X])
      (A := baseAlgebra ⊗[baseField] Localization.Away localizer) ?_
    intro scalar
    change scalar ⊗ₜ[baseField] (1 : Localization.Away localizer) =
      scalar ⊗ₜ[baseField] (algebraMap baseField[X] (Localization.Away localizer) 1)
    rw [map_one]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right baseField baseAlgebra (Submonoid.powers localizer)
    (Localization.Away localizer) (by ext <;> simp [RingHom.algebraMap_toAlgebra])
  rw [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply] at hloc
  have halg (x : baseAlgebra) (y : baseField[X]) : algebraMap (baseAlgebra ⊗[baseField] baseField[X]) (baseAlgebra ⊗[baseField] Localization.Away localizer)
      (x ⊗ₜ y) = x ⊗ₜ algebraMap baseField[X] _ y := rfl
  have hM : Submonoid.powers ((1 : baseAlgebra) ⊗ₜ[baseField] localizer) ≤ nonZeroDivisors (baseAlgebra ⊗[baseField] baseField[X]) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (one_tmul_ne_zero baseAlgebra hh)
  obtain ⟨⟨numerator, roots, exponent, rfl⟩, hP⟩ := IsLocalization.surj (Submonoid.powers ((1 : baseAlgebra) ⊗ₜ[baseField] localizer))
    (unitValue : baseAlgebra ⊗[baseField] Localization.Away localizer)
  obtain ⟨⟨inverseNumerator, s', inverseExponent, rfl⟩, hQ⟩ := IsLocalization.surj (Submonoid.powers ((1 : baseAlgebra) ⊗ₜ[baseField] localizer))
    (↑unitValue⁻¹ : baseAlgebra ⊗[baseField] Localization.Away localizer)
  have hPQ : numerator * inverseNumerator = (1 ⊗ₜ localizer) ^ (exponent + inverseExponent) := by
    apply IsLocalization.injective (baseAlgebra ⊗[baseField] Localization.Away localizer) hM
    rw [map_mul, ← hP, ← hQ, mul_mul_mul_comm, Units.mul_inv, one_mul, ← map_mul, pow_add]
  have hdvd : (polyEquivTensor baseField baseAlgebra).symm numerator ∣ (localizer ^ (exponent + inverseExponent)).map (algebraMap baseField baseAlgebra) := by
    refine ⟨(polyEquivTensor baseField baseAlgebra).symm inverseNumerator, ?_⟩
    rw [← map_mul, hPQ, Algebra.TensorProduct.tmul_pow, one_pow,
      polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]
  obtain ⟨unitCoefficient, factor, hg, hPg⟩ := exists_eq_C_mul_map_of_dvd_map (pow_ne_zero _ hh) hdvd
  have hgu : IsUnit (algebraMap baseField[X] (Localization.Away localizer) factor) := by
    obtain ⟨c, hc⟩ := hg
    refine isUnit_of_mul_isUnit_left (y := algebraMap baseField[X] (Localization.Away localizer) c) ?_
    rw [← map_mul, ← hc, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit localizer).pow _
  have hhu : IsUnit (algebraMap baseField[X] (Localization.Away localizer) localizer ^ exponent) :=
    (IsLocalization.Away.algebraMap_isUnit localizer).pow _
  refine ⟨unitCoefficient, hgu.unit * hhu.unit⁻¹, ?_⟩
  have hP' : numerator = (unitCoefficient : baseAlgebra) ⊗ₜ factor := by
    rw [← (polyEquivTensor baseField baseAlgebra).apply_symm_apply numerator, hPg, ← smul_eq_C_mul,
      ← polyEquivTensor_symm_apply_tmul_eq_smul, AlgEquiv.apply_symm_apply]
  have hunit : IsUnit (algebraMap (baseAlgebra ⊗[baseField] baseField[X]) (baseAlgebra ⊗[baseField] Localization.Away localizer)
      ((1 ⊗ₜ localizer) ^ exponent)) := IsLocalization.map_units _ (⟨_, exponent, rfl⟩ : Submonoid.powers _)
  rw [← hunit.mul_left_inj, hP, hP', halg, Algebra.TensorProduct.tmul_pow, one_pow, halg,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, Units.val_mul, mul_assoc, map_pow,
    IsUnit.val_inv_mul, mul_one, IsUnit.unit_spec]

end TensorProduct
