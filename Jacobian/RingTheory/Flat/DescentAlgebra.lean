import Mathlib.RingTheory.Flat.Equalizer

set_option backward.isDefEq.respectTransparency false

section
open TensorProduct

namespace Algebra

section MulMap

variable (baseRing coverRing totalRing : Type*) [CommRing baseRing] [CommRing coverRing] [CommRing totalRing] [Algebra baseRing coverRing] [Algebra baseRing totalRing]
  [Algebra coverRing totalRing] [IsScalarTower baseRing coverRing totalRing]

noncomputable def TensorProduct.mulMap : coverRing ⊗[baseRing] totalRing →ₐ[coverRing] totalRing :=
  Algebra.TensorProduct.lift (Algebra.ofId coverRing totalRing) (AlgHom.id baseRing totalRing) fun _ _ ↦ Commute.all _ _

variable {baseRing coverRing totalRing}

@[simp]
lemma TensorProduct.mulMap_tmul (scalar : coverRing) (element : totalRing) :
    TensorProduct.mulMap baseRing coverRing totalRing (scalar ⊗ₜ element) = scalar • element := by
  simp [TensorProduct.mulMap, Algebra.smul_def, Algebra.ofId_apply]

@[simp]
lemma TensorProduct.mulMap_includeRight (element : totalRing) :
    TensorProduct.mulMap baseRing coverRing totalRing (Algebra.TensorProduct.includeRight element) = element := by
  simp

end MulMap

structure DescentDatum (baseRing coverRing totalRing : Type*) [CommRing baseRing] [CommRing coverRing] [CommRing totalRing] [Algebra baseRing coverRing]
    [Algebra baseRing totalRing] [Algebra coverRing totalRing] [IsScalarTower baseRing coverRing totalRing] where

  coaction : totalRing →ₐ[coverRing] coverRing ⊗[baseRing] totalRing

  counit : ∀ element, TensorProduct.mulMap baseRing coverRing totalRing (coaction element) = element

  coassoc : ∀ element, Algebra.TensorProduct.map (AlgHom.id baseRing coverRing) (coaction.restrictScalars baseRing) (coaction element) =
    Algebra.TensorProduct.map (AlgHom.id baseRing coverRing) Algebra.TensorProduct.includeRight (coaction element)

namespace DescentDatum

variable {baseRing coverRing totalRing : Type*} [CommRing baseRing] [CommRing coverRing] [CommRing totalRing] [Algebra baseRing coverRing] [Algebra baseRing totalRing]
  [Algebra coverRing totalRing] [IsScalarTower baseRing coverRing totalRing] (datum : DescentDatum baseRing coverRing totalRing)

lemma coaction_smul (scalar : coverRing) (element : totalRing) : datum.coaction (scalar • element) = scalar • datum.coaction element :=
  map_smul datum.coaction scalar element

lemma coaction_algebraMap (scalar : coverRing) : datum.coaction (algebraMap coverRing totalRing scalar) = scalar ⊗ₜ 1 := by
  rw [AlgHom.commutes]
  rfl

noncomputable def descended : Subalgebra baseRing totalRing :=
  AlgHom.equalizer (datum.coaction.restrictScalars baseRing) Algebra.TensorProduct.includeRight

lemma mem_descended_iff (element : totalRing) : element ∈ datum.descended ↔ datum.coaction element = 1 ⊗ₜ element :=
  Iff.rfl

lemma coaction_of_mem_descended {element : totalRing} (membership : element ∈ datum.descended) : datum.coaction element = 1 ⊗ₜ element :=
  membership

noncomputable def descendedMap : coverRing ⊗[baseRing] datum.descended →ₐ[coverRing] totalRing :=
  Algebra.TensorProduct.lift (Algebra.ofId coverRing totalRing) datum.descended.val fun _ _ ↦ Commute.all _ _

@[simp]
lemma descendedMap_tmul (scalar : coverRing) (invariant : datum.descended) : datum.descendedMap (scalar ⊗ₜ invariant) = scalar • (invariant : totalRing) := by
  simp [descendedMap, Algebra.smul_def, Algebra.ofId_apply]

section Flat

variable [Module.Flat baseRing coverRing]

private noncomputable abbrev tensorEqualizer : Subalgebra coverRing (coverRing ⊗[baseRing] totalRing) :=
  AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id coverRing coverRing) (datum.coaction.restrictScalars baseRing))
    (Algebra.TensorProduct.map (AlgHom.id coverRing coverRing) Algebra.TensorProduct.includeRight)

omit [Module.Flat baseRing coverRing] in
private lemma coaction_mem_tensorEqualizer (element : totalRing) : datum.coaction element ∈ datum.tensorEqualizer :=
  datum.coassoc element

private noncomputable def liftCoaction (element : totalRing) : coverRing ⊗[baseRing] datum.descended :=
  (AlgHom.tensorEqualizerEquiv coverRing coverRing (datum.coaction.restrictScalars baseRing)
    Algebra.TensorProduct.includeRight).symm ⟨datum.coaction element, datum.coaction_mem_tensorEqualizer element⟩

private lemma coe_liftCoaction (element : totalRing) :
    Algebra.TensorProduct.map (AlgHom.id coverRing coverRing) datum.descended.val (datum.liftCoaction element) = datum.coaction element := by
  have := congrArg Subtype.val ((AlgHom.tensorEqualizerEquiv coverRing coverRing (datum.coaction.restrictScalars baseRing)
    Algebra.TensorProduct.includeRight).apply_symm_apply ⟨datum.coaction element, datum.coaction_mem_tensorEqualizer element⟩)
  rw [AlgHom.tensorEqualizerEquiv_apply, AlgHom.coe_tensorEqualizer] at this
  exact this

private lemma liftCoaction_injective : Function.Injective datum.liftCoaction :=
  fun firstElement secondElement equality ↦ by
    have := congrArg (fun tensor ↦ Algebra.TensorProduct.map (AlgHom.id coverRing coverRing) datum.descended.val tensor) equality
    simp only [coe_liftCoaction] at this
    rw [← datum.counit firstElement, ← datum.counit secondElement, this]

omit [Module.Flat baseRing coverRing] in
private lemma descendedMap_comp_map_val (tensor : coverRing ⊗[baseRing] datum.descended) :
    TensorProduct.mulMap baseRing coverRing totalRing (Algebra.TensorProduct.map (AlgHom.id coverRing coverRing) datum.descended.val tensor) =
      datum.descendedMap tensor := by
  induction tensor using TensorProduct.inductionOn with
  | tmul scalar invariant => simp
  | add tensor otherTensor first_eq second_eq => simp [first_eq, second_eq]

private lemma descendedMap_liftCoaction (element : totalRing) : datum.descendedMap (datum.liftCoaction element) = element := by
  rw [← descendedMap_comp_map_val, coe_liftCoaction, datum.counit]

private lemma map_val_injective :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id coverRing coverRing) datum.descended.val) := by
  intro firstTensor secondTensor equality
  apply (AlgHom.tensorEqualizerEquiv coverRing coverRing (datum.coaction.restrictScalars baseRing)
    Algebra.TensorProduct.includeRight).injective
  ext1
  rw [AlgHom.tensorEqualizerEquiv_apply, AlgHom.tensorEqualizerEquiv_apply,
    AlgHom.coe_tensorEqualizer, AlgHom.coe_tensorEqualizer]
  exact equality

private lemma liftCoaction_descendedMap (tensor : coverRing ⊗[baseRing] datum.descended) : datum.liftCoaction (datum.descendedMap tensor) = tensor := by
  apply datum.map_val_injective
  rw [coe_liftCoaction]
  induction tensor using TensorProduct.inductionOn with
  | tmul scalar invariant =>
    rw [descendedMap_tmul, datum.coaction_smul, datum.coaction_of_mem_descended invariant.2]
    simp [TensorProduct.smul_tmul']
  | add tensor otherTensor first_eq second_eq => simp only [map_add, first_eq, second_eq]

theorem bijective_descendedMap : Function.Bijective datum.descendedMap :=
  ⟨fun tensor otherTensor equality ↦ by rw [← datum.liftCoaction_descendedMap tensor, ← datum.liftCoaction_descendedMap otherTensor, equality],
    fun element ↦ ⟨datum.liftCoaction element, datum.descendedMap_liftCoaction element⟩⟩

noncomputable def descendedEquiv : coverRing ⊗[baseRing] datum.descended ≃ₐ[coverRing] totalRing :=
  AlgEquiv.ofBijective datum.descendedMap datum.bijective_descendedMap

@[simp]
lemma descendedEquiv_apply (tensor : coverRing ⊗[baseRing] datum.descended) : datum.descendedEquiv tensor = datum.descendedMap tensor :=
  rfl

end Flat

end DescentDatum

end Algebra
