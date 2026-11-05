import Jacobian.RingTheory.Flat.Exact

/-!
# Tensor exactness and kernels

Exactness after tensoring passes to module retracts. If a complex of flat modules
stays exact in degree one after tensoring with every module, its zero-cycles embed
after tensoring with an arbitrary module.
-/

noncomputable section

section
open scoped TensorProduct

namespace Function.Exact

variable {baseRing : Type*} [CommRing baseRing] {firstTerm middleTerm lastTerm moduleType retractTarget : Type*} [AddCommGroup firstTerm] [AddCommGroup middleTerm]
  [AddCommGroup lastTerm] [AddCommGroup moduleType] [AddCommGroup retractTarget] [Module baseRing firstTerm] [Module baseRing middleTerm] [Module baseRing lastTerm]
  [Module baseRing moduleType] [Module baseRing retractTarget]

omit [AddCommGroup firstTerm] [AddCommGroup middleTerm] [AddCommGroup lastTerm] [AddCommGroup moduleType] [AddCommGroup retractTarget]
  [Module baseRing firstTerm] [Module baseRing middleTerm] [Module baseRing lastTerm] [Module baseRing moduleType] [Module baseRing retractTarget] in
private lemma lTensor_rTensor_comm {firstModule secondModule sourceModule targetModule : Type*} [AddCommGroup firstModule] [AddCommGroup secondModule]
    [Module baseRing firstModule] [Module baseRing secondModule] (moduleMap : firstModule →ₗ[baseRing] secondModule) [AddCommGroup sourceModule] [AddCommGroup targetModule] [Module baseRing sourceModule]
    [Module baseRing targetModule] (differential : sourceModule →ₗ[baseRing] targetModule) (element : firstModule ⊗[baseRing] sourceModule) :
    differential.lTensor secondModule (moduleMap.rTensor sourceModule element) = moduleMap.rTensor targetModule (differential.lTensor firstModule element) := by
  rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
    LinearMap.comp_apply]

/-- **Exactness after tensoring passes to retracts.** If `firstDifferential, secondDifferential` stay exact after tensoring
with `retractTarget` and `moduleType` is a retract of `retractTarget`, they stay exact after tensoring with `moduleType`. -/
lemma lTensor_of_retract {firstDifferential : firstTerm →ₗ[baseRing] middleTerm} {secondDifferential : middleTerm →ₗ[baseRing] lastTerm} (inclusion : moduleType →ₗ[baseRing] retractTarget)
    (retraction : retractTarget →ₗ[baseRing] moduleType) (hri : retraction ∘ₗ inclusion = LinearMap.id)
    (exactness : Function.Exact (firstDifferential.lTensor retractTarget) (secondDifferential.lTensor retractTarget)) :
    Function.Exact (firstDifferential.lTensor moduleType) (secondDifferential.lTensor moduleType) := by
  have hr (element : moduleType ⊗[baseRing] middleTerm) : retraction.rTensor middleTerm (inclusion.rTensor middleTerm element) = element := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hri, LinearMap.rTensor_id,
      LinearMap.id_apply]
  have hr₂ (element : moduleType ⊗[baseRing] lastTerm) : retraction.rTensor lastTerm (inclusion.rTensor lastTerm element) = element := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hri, LinearMap.rTensor_id,
      LinearMap.id_apply]
  intro element
  constructor
  · intro hx
    obtain ⟨cycle, hz⟩ := (exactness (inclusion.rTensor middleTerm element)).mp (by rw [lTensor_rTensor_comm, hx, map_zero])
    refine ⟨retraction.rTensor firstTerm cycle, ?_⟩
    rw [lTensor_rTensor_comm, hz, hr]
  · rintro ⟨cycle, rfl⟩
    have h0 : secondDifferential.lTensor retractTarget (firstDifferential.lTensor retractTarget (inclusion.rTensor firstTerm cycle)) = 0 :=
      (exactness _).mpr ⟨_, rfl⟩
    rw [← hr₂ (secondDifferential.lTensor moduleType (firstDifferential.lTensor moduleType cycle)), ← lTensor_rTensor_comm inclusion secondDifferential,
      ← lTensor_rTensor_comm inclusion firstDifferential, h0, map_zero]

end Function.Exact

universe schemeUniverse

/-- If a complex of flat modules stays exact in degree one after every scalar tensor,
then its degree-zero cycles stay a submodule after any scalar tensor. -/
theorem Module.Flat.lTensor_injective_ker_subtype {baseRing : Type schemeUniverse} [CommRing baseRing]
    {firstTerm middleTerm lastTerm : Type*} [AddCommGroup firstTerm] [AddCommGroup middleTerm] [AddCommGroup lastTerm] [Module baseRing firstTerm]
    [Module baseRing middleTerm] [Module baseRing lastTerm] [Module.Flat baseRing middleTerm] [Module.Flat baseRing lastTerm] (firstDifferential : firstTerm →ₗ[baseRing] middleTerm)
    (secondDifferential : middleTerm →ₗ[baseRing] lastTerm) (hd : secondDifferential ∘ₗ firstDifferential = 0)
    (universalExactness : ∀ (moduleType : Type schemeUniverse) [AddCommGroup moduleType] [Module baseRing moduleType],
      Function.Exact (firstDifferential.lTensor moduleType) (secondDifferential.lTensor moduleType))
    (moduleType : Type*) [AddCommGroup moduleType] [Module baseRing moduleType] :
    Function.Injective ((LinearMap.ker firstDifferential).subtype.lTensor moduleType) := by
  let quotientMap := (LinearMap.range firstDifferential).mkQ
  have hπ : Function.Surjective quotientMap := Submodule.mkQ_surjective _
  have hdπ : Function.Exact firstDifferential quotientMap := LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)
  have hle : LinearMap.range firstDifferential ≤ LinearMap.ker secondDifferential := by
    rintro _ ⟨element, rfl⟩
    exact congr($hd element)
  let quotientDifferential := (LinearMap.range firstDifferential).liftQ secondDifferential hle
  have hqπ : quotientDifferential ∘ₗ quotientMap = secondDifferential := Submodule.liftQ_mkQ _ _ _
  have hq (testModule : Type schemeUniverse) [AddCommGroup testModule] [Module baseRing testModule] : Function.Injective (quotientDifferential.lTensor testModule) := by
    rw [injective_iff_map_eq_zero]
    intro cycle hz
    obtain ⟨liftedElement, rfl⟩ := LinearMap.lTensor_surjective testModule hπ cycle
    have hw : secondDifferential.lTensor testModule liftedElement = 0 := by
      rw [← hqπ, LinearMap.lTensor_comp, LinearMap.comp_apply, hz]
    obtain ⟨preimage, rfl⟩ := (universalExactness testModule liftedElement).mp hw
    exact (_root_.lTensor_exact testModule hdπ hπ _).mpr ⟨preimage, rfl⟩
  have : Module.Flat baseRing (middleTerm ⧸ LinearMap.range firstDifferential) := by
    rw [Module.Flat.iff_rTensor_preserves_injective_linearMap'.{schemeUniverse}]
    intro testModule targetTestModule _ _ _ _ testMap hι
    have exactness : (testMap.rTensor lastTerm) ∘ₗ (quotientDifferential.lTensor testModule) = (quotientDifferential.lTensor targetTestModule) ∘ₗ (testMap.rTensor _) := by
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    refine Function.Injective.of_comp (f := quotientDifferential.lTensor targetTestModule) ?_
    rw [← LinearMap.coe_comp, ← exactness, LinearMap.coe_comp]
    exact (Module.Flat.rTensor_preserves_injective_linearMap _ hι).comp (hq testModule)
  have : Module.Flat baseRing (LinearMap.range firstDifferential) :=
    Module.Flat.of_exact_of_flat_of_flat_right (LinearMap.range firstDifferential).subtype quotientMap
      Subtype.val_injective hπ (by
        rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype])
  exact LinearMap.lTensor_injective_of_exact_of_flat firstDifferential.rangeRestrict firstDifferential.surjective_rangeRestrict
    (LinearMap.ker firstDifferential).subtype Subtype.val_injective
    (by rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]) moduleType
