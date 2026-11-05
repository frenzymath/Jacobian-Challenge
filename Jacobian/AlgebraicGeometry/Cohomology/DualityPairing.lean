import Mathlib.LinearAlgebra.Dual.Lemmas
import Jacobian.AlgebraicGeometry.Cohomology.LongExact
import Jacobian.AlgebraicGeometry.Cohomology.InternalHom

/-!
# Degree-one duality pairings

A linear form on the first cohomology of a module defines a natural pairing
from morphisms into that module to the dual of first cohomology. Bijectivity
passes through finite coproducts and presentations. The internal-hom version
is linear and uses the canonical degree-zero cohomology identification.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

section LongExact

variable {scheme : Scheme.{schemeUniverse}} {shortComplex : ShortComplex scheme.Modules}

/-- In firstForm short exact sequence `0 → M₁ → M₂ → M₃ → 0` with `H⁰(M₃) = 0`, the map
`H¹(M₁) ⟶ H¹(M₂)` is injective. -/
lemma H.injective_map_f_one (shortExact : shortComplex.ShortExact) [Subsingleton (shortComplex.X₃.H 0)] :
    Function.Injective (H.map shortComplex.f 1) := by
  refine (injective_iff_map_eq_zero _).2 fun firstValue descentIdentity ↦ ?_
  obtain ⟨secondValue, rfl⟩ := (H.ker_map_f_eq_range_δ shortExact 0).le descentIdentity
  rw [Subsingleton.elim secondValue 0, map_zero]

/-- In firstForm short exact sequence `0 → M₁ → M₂ → M₃ → 0` with `H^{degree+1}(M₁) = 0`, the map
`H^degree(M₂) ⟶ H^degree(M₃)` is surjective. -/
lemma H.surjective_map_g (shortExact : shortComplex.ShortExact) (degree : ℕ) [Subsingleton (shortComplex.X₁.H (degree + 1))] :
    Function.Surjective (H.map shortComplex.g degree) := by
  intro firstValue
  exact (H.ker_δ_eq_range_map_g shortExact degree).le (Subsingleton.elim (H.δ shortExact degree firstValue) 0)

end LongExact

variable {field : Type schemeUniverse} [Field field] {scheme : Scheme.{schemeUniverse}} [scheme.Over (Spec (.of field))] {dualizingModule : scheme.Modules}
  (traceForm : Module.Dual field (dualizingModule.H 1))

/-- The duality pairing `Hom(coefficient, dualizingModule) → H¹(scheme, coefficient)^∨`, `morphism ↦ traceForm ∘ H¹(morphism)`. -/
def dualPairing (coefficient : scheme.Modules) : (coefficient ⟶ dualizingModule) →+ Module.Dual field (coefficient.H 1) where
  toFun morphism := traceForm ∘ₗ H.mapLinearMap field morphism 1
  map_zero' := by
    ext firstValue
    simp
  map_add' morphism liftedMorphism := by
    ext firstValue
    simp

lemma dualPairing_apply {coefficient : scheme.Modules} (morphism : coefficient ⟶ dualizingModule) (firstValue : coefficient.H 1) :
    dualPairing traceForm coefficient morphism firstValue = traceForm (H.map morphism 1 firstValue) :=
  rfl

/-- **Naturality of the duality pairing.** -/
lemma dualPairing_comp {otherCoefficient coefficient : scheme.Modules} (family : otherCoefficient ⟶ coefficient) (morphism : coefficient ⟶ dualizingModule) :
    dualPairing traceForm otherCoefficient (family ≫ morphism) = dualPairing traceForm coefficient morphism ∘ₗ H.mapLinearMap field family 1 := by
  ext firstValue
  simp [dualPairing_apply, H.map_comp_apply]

/-- **Transport of surjectivity.** If `schemeUniverse : firstModule ⟶ targetModule` induces an injection on `H¹` and the duality
pairing of `targetModule` is surjective, then so is the one of `firstModule`. -/
lemma surjective_dualPairing_of_injective {firstModule targetModule : scheme.Modules} (inclusion : firstModule ⟶ targetModule)
    (injectiveMap : Function.Injective (H.map inclusion 1)) (surjectivePairing : Function.Surjective (dualPairing traceForm targetModule)) :
    Function.Surjective (dualPairing traceForm firstModule) := by
  intro secondValue
  obtain ⟨retraction, retractionIdentity⟩ := LinearMap.exists_leftInverse_of_injective (H.mapLinearMap field inclusion 1)
    (LinearMap.ker_eq_bot.2 injectiveMap)
  obtain ⟨liftedMorphism, liftIdentity⟩ := surjectivePairing (secondValue ∘ₗ retraction)
  refine ⟨inclusion ≫ liftedMorphism, ?_⟩
  rw [dualPairing_comp, liftIdentity, LinearMap.comp_assoc, retractionIdentity, LinearMap.comp_id]

/-- **The duality pairing and finite coproducts.** If the duality pairing is bijective for every
`family index`, it is bijective for the coproduct `∐ family`. -/
lemma bijective_dualPairing_sigma {indexType : Type schemeUniverse} [Finite indexType] (family : indexType → scheme.Modules)
    (bijectiveFamily : ∀ index, Function.Bijective (dualPairing traceForm (family index))) :
    Function.Bijective (dualPairing traceForm (∐ family)) := by
  classical
  have := Fintype.ofFinite indexType
  have : HasFiniteBiproducts scheme.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  have totalIdentity : ∑ index, (Sigma.desc (biproduct.ι family) ≫ biproduct.π family index) ≫ Sigma.ι family index = 𝟙 (∐ family) := by
    refine Sigma.hom_ext _ _ fun otherIndex ↦ ?_
    simp [Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp]
  have sumIdentity (classValue : (∐ family).H 1) : classValue = ∑ index, H.map (Sigma.ι family index) 1
      (H.map (Sigma.desc (biproduct.ι family) ≫ biproduct.π family index) 1 classValue) := by
    conv_lhs => rw [← H.map_id_apply (∐ family) 1 classValue, ← totalIdentity]
    rw [H.map_sum_apply]
    simp only [H.map_comp_apply]
  constructor
  · intro firstValue secondValue valueEquality
    refine Sigma.hom_ext _ _ fun index ↦ (bijectiveFamily index).1 ?_
    rw [dualPairing_comp, dualPairing_comp, valueEquality]
  · intro secondValue
    choose firstValue descentIdentity using fun index ↦ (bijectiveFamily index).2 (secondValue ∘ₗ H.mapLinearMap field (Sigma.ι family index) 1)
    refine ⟨Sigma.desc firstValue, LinearMap.ext fun classValue ↦ ?_⟩
    rw [sumIdentity classValue, map_sum, map_sum]
    refine Finset.sum_congr rfl fun index _ ↦ ?_
    rw [dualPairing_apply, ← H.map_comp_apply, Sigma.ι_desc, ← dualPairing_apply, descentIdentity index]
    rfl

/-- **The duality pairing and binary biproducts.** -/
lemma bijective_dualPairing_biprod (firstModule secondModule : scheme.Modules) (bijectiveFirst : Function.Bijective (dualPairing traceForm firstModule))
    (bijectiveSecond : Function.Bijective (dualPairing traceForm secondModule)) :
    Function.Bijective (dualPairing traceForm (firstModule ⊞ secondModule)) := by
  have sumIdentity (classValue : (firstModule ⊞ secondModule).H 1) :
      classValue = H.map biprod.inl 1 (H.map biprod.fst 1 classValue) +
        H.map biprod.inr 1 (H.map biprod.snd 1 classValue) := by
    conv_lhs => rw [← H.map_id_apply (firstModule ⊞ secondModule) 1 classValue, ← biprod.total]
    rw [H.map_add_apply, H.map_comp_apply, H.map_comp_apply]
  constructor
  · intro firstValue secondValue valueEquality
    refine biprod.hom_ext' _ _ (bijectiveFirst.1 ?_) (bijectiveSecond.1 ?_) <;>
    rw [dualPairing_comp, dualPairing_comp, valueEquality]
  · intro secondValue
    obtain ⟨firstLift, firstIdentity⟩ := bijectiveFirst.2 (secondValue ∘ₗ H.mapLinearMap field biprod.inl 1)
    obtain ⟨secondLift, secondIdentity⟩ := bijectiveSecond.2 (secondValue ∘ₗ H.mapLinearMap field biprod.inr 1)
    have firstComparison (liftedValue : firstModule.H 1) : traceForm (H.map (biprod.desc firstLift secondLift) 1 (H.map biprod.inl 1 liftedValue)) =
        secondValue (H.map biprod.inl 1 liftedValue) := by
      rw [← H.map_comp_apply, biprod.inl_desc]
      exact LinearMap.congr_fun firstIdentity liftedValue
    have secondComparison (liftedValue : secondModule.H 1) : traceForm (H.map (biprod.desc firstLift secondLift) 1 (H.map biprod.inr 1 liftedValue)) =
        secondValue (H.map biprod.inr 1 liftedValue) := by
      rw [← H.map_comp_apply, biprod.inr_desc]
      exact LinearMap.congr_fun secondIdentity liftedValue
    refine ⟨biprod.desc firstLift secondLift, LinearMap.ext fun classValue ↦ ?_⟩
    rw [sumIdentity classValue, map_add, map_add, dualPairing_apply, dualPairing_apply, firstComparison, secondComparison]

/-- **The duality pairing on firstForm presentation.** Let `relationsModule ⟶ presentationModule ⟶ coefficient ⟶ 0` be exact, otherIndex.e. `presentation : presentationModule ⟶ coefficient`
is an epimorphism and `relations : relationsModule ⟶ ker presentation` is an epimorphism, and assume that `H¹(presentation)` is
surjective. If the duality pairing is bijective for `presentationModule` and injective for `relationsModule`, then it is
bijective for `coefficient`. -/
lemma bijective_dualPairing_of_epi {presentationModule relationsModule coefficient : scheme.Modules} (presentation : presentationModule ⟶ coefficient) [Epi presentation]
    (relations : relationsModule ⟶ kernel presentation) [Epi relations] (bijectivePresentation : Function.Bijective (dualPairing traceForm presentationModule))
    (injectiveRelations : Function.Injective (dualPairing traceForm relationsModule)) (surjectivePresentation : Function.Surjective (H.map presentation 1)) :
    Function.Bijective (dualPairing traceForm coefficient) := by
  have dualInjective : Function.Injective fun firstForm : Module.Dual field (coefficient.H 1) ↦ firstForm ∘ₗ H.mapLinearMap field presentation 1 := by
    intro firstForm secondForm hab
    ext classValue
    obtain ⟨classValue, rfl⟩ := surjectivePresentation classValue
    exact LinearMap.congr_fun hab classValue
  constructor
  · intro firstValue secondValue valueEquality
    refine (cancel_epi presentation).1 (bijectivePresentation.1 ?_)
    rw [dualPairing_comp, dualPairing_comp, valueEquality]
  · intro secondValue
    obtain ⟨liftedValue, pairingIdentity⟩ := bijectivePresentation.2 (secondValue ∘ₗ H.mapLinearMap field presentation 1)
    have kernelZero : kernel.ι presentation ≫ liftedValue = 0 := by
      refine (cancel_epi relations).1 (injectiveRelations ?_)
      rw [comp_zero, ← Category.assoc, dualPairing_comp, pairingIdentity, map_zero, LinearMap.comp_assoc,
        ← H.mapLinearMap_comp, Category.assoc, kernel.condition, comp_zero]
      ext classValue
      simp
    obtain ⟨firstValue, descentIdentity⟩ := CokernelCofork.IsColimit.desc'
      (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel presentation)) liftedValue kernelZero
    refine ⟨firstValue, dualInjective ?_⟩
    change dualPairing traceForm coefficient firstValue ∘ₗ H.mapLinearMap field presentation 1 = secondValue ∘ₗ H.mapLinearMap field presentation 1
    rw [← dualPairing_comp]
    exact (congrArg (dualPairing traceForm presentationModule) descentIdentity).trans pairingIdentity

/-- **The duality pairing on `H⁰(scheme, Hom(coefficient, dualizingModule))`**, as firstForm `field`-linear map
`H⁰(scheme, Hom(coefficient, dualizingModule)) ⟶ H¹(scheme, coefficient)^∨`: the duality pairing `dualPairing` composed with
`H⁰(scheme, Hom(coefficient, dualizingModule)) ≃ Hom(coefficient, dualizingModule)`. -/
def dualPairingH (coefficient : scheme.Modules) :
    H (X := scheme) (SheafOfModules.homObj (R := scheme.sheaf) coefficient dualizingModule) 0 →ₗ[field] Module.Dual field (coefficient.H 1) where
  toFun firstValue := dualPairing traceForm coefficient (homObjHZeroAddEquiv coefficient dualizingModule firstValue)
  map_add' firstValue secondValue := by
    rw [map_add, map_add]
  map_smul' classValue firstValue := by
    rw [smul_H_eq_globalSectionsRingHom_smul, homObjHZeroAddEquiv_smul]
    ext secondValue
    rw [dualPairing_apply, H.map_comp_apply, ← smul_H_eq_map,
      ← smul_H_eq_globalSectionsRingHom_smul, LinearMap.map_smul, RingHom.id_apply,
      LinearMap.smul_apply, dualPairing_apply]

lemma dualPairingH_apply (coefficient : scheme.Modules)
    (firstValue : H (X := scheme) (SheafOfModules.homObj (R := scheme.sheaf) coefficient dualizingModule) 0) :
    dualPairingH traceForm coefficient firstValue = dualPairing traceForm coefficient (homObjHZeroAddEquiv coefficient dualizingModule firstValue) :=
  rfl

lemma bijective_dualPairingH_iff (coefficient : scheme.Modules) :
    Function.Bijective (dualPairingH traceForm coefficient) ↔ Function.Bijective (dualPairing traceForm coefficient) := by
  change Function.Bijective (dualPairing traceForm coefficient ∘ homObjHZeroAddEquiv coefficient dualizingModule) ↔ _
  exact Function.Bijective.of_comp_iff _ (homObjHZeroAddEquiv coefficient dualizingModule).bijective

end AlgebraicGeometry.Scheme.Modules
