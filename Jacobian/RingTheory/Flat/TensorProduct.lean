import Mathlib.RingTheory.Flat.Stability

/-!
# Flat tensor products over an intermediate algebra

If an `S`-module is flat over `S` and another `S`-module is flat over `R`,
their tensor product over `S` is flat over `R`. The tensor associator expresses
the induced map as a composition of two maps preserving injectivity.
-/

universe u v w t

open TensorProduct

namespace Module.Flat

variable (baseRing : Type u) (algebraRing : Type v)
  (leftFactor : Type w) (rightFactor : Type t)
  [CommRing baseRing] [CommRing algebraRing] [Algebra baseRing algebraRing]
  [AddCommMonoid leftFactor] [Module baseRing leftFactor] [Module algebraRing leftFactor]
  [IsScalarTower baseRing algebraRing leftFactor]
  [AddCommMonoid rightFactor] [Module baseRing rightFactor] [Module algebraRing rightFactor]
  [IsScalarTower baseRing algebraRing rightFactor]

/-- Tensoring a flat module over an intermediate algebra with a module flat
over the base gives a module flat over the base. -/
theorem tensorProduct_of_flat [Flat algebraRing leftFactor] [Flat baseRing rightFactor] :
    Flat baseRing (leftFactor ⊗[algebraRing] rightFactor) := by
  rw [Flat.iff_lTensor_injectiveₛ]
  intro testModule _ _ testSubmodule
  let associator (targetModule : Type u) [AddCommMonoid targetModule]
      [Module baseRing targetModule] :=
    AlgebraTensorModule.assoc baseRing algebraRing algebraRing leftFactor rightFactor targetModule
  let intermediateMap : rightFactor ⊗[baseRing] testSubmodule →ₗ[algebraRing]
      rightFactor ⊗[baseRing] testModule :=
    AlgebraTensorModule.lTensor algebraRing rightFactor testSubmodule.subtype
  have comparison :
      (associator testModule).toLinearMap.restrictScalars baseRing ∘ₗ
          testSubmodule.subtype.lTensor (leftFactor ⊗[algebraRing] rightFactor) =
        (intermediateMap.lTensor leftFactor).restrictScalars baseRing ∘ₗ
          (associator testSubmodule).toLinearMap.restrictScalars baseRing := by
    refine LinearMap.ext fun value ↦ ?_
    induction value using TensorProduct.induction_on with
    | zero => simp
    | add firstValue secondValue firstEquality secondEquality =>
      simp only [map_add] at firstEquality secondEquality ⊢
      rw [firstEquality, secondEquality]
    | tmul tensorValue moduleElement =>
      induction tensorValue using TensorProduct.induction_on with
      | zero => simp
      | add firstValue secondValue firstEquality secondEquality =>
        simp only [LinearMap.coe_comp, Function.comp_apply, add_tmul, map_add]
          at firstEquality secondEquality ⊢
        rw [firstEquality, secondEquality]
      | tmul leftElement rightElement => rfl
  have injective : Function.Injective
      ((intermediateMap.lTensor leftFactor).restrictScalars baseRing ∘ₗ
        (associator testSubmodule).toLinearMap.restrictScalars baseRing) :=
    (Flat.lTensor_preserves_injective_linearMap intermediateMap
      (Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)).comp
      (associator testSubmodule).injective
  rw [← comparison] at injective
  intro firstValue secondValue equality
  exact injective (by simp only [LinearMap.coe_comp, Function.comp_apply, equality])

end Module.Flat
