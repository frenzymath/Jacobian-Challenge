import Jacobian.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Tensor products after successive scalar extensions

Tensoring a native scalar extension along a further algebra identifies with
tensoring over the original ring. This identification is natural in the module.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace TensorProduct

variable {baseRing : Type u} [CommRing baseRing] (extensionRing : Type u)
  [CommRing extensionRing] [Algebra baseRing extensionRing]
  {moduleType : Type u} [AddCommGroup moduleType] [Module baseRing moduleType]

/-- Moving a scalar from the right factor across the tensor product. -/
lemma one_tmul_smul_eq_algebraMap_smul (scalar : baseRing) (element : moduleType) :
    (1 : extensionRing) ⊗ₜ[baseRing] (scalar • element) =
      algebraMap baseRing extensionRing scalar • ((1 : extensionRing) ⊗ₜ[baseRing] element) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul',
    _root_.Algebra.smul_def scalar, smul_eq_mul]

/-- A pure tensor with a scalar multiple in its right factor is a multiple of `1 ⊗ element`. -/
lemma tmul_smul_eq_mul_algebraMap_smul (coefficient : extensionRing) (scalar : baseRing)
    (element : moduleType) :
    coefficient ⊗ₜ[baseRing] (scalar • element) =
      (coefficient * algebraMap baseRing extensionRing scalar) •
        ((1 : extensionRing) ⊗ₜ[baseRing] element) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    _root_.Algebra.smul_def scalar coefficient, mul_comm]

end TensorProduct

namespace ModuleCat

open TensorProduct

variable (baseRing middleRing extensionRing : Type u)
  [CommRing baseRing] [CommRing middleRing] [CommRing extensionRing]
  [Algebra baseRing middleRing] [Algebra baseRing extensionRing]
  [Algebra middleRing extensionRing] [IsScalarTower baseRing middleRing extensionRing]

/-- Cancellation of an intermediate native extension of scalars inside a tensor product. -/
def tensorExtendScalarsCancel (moduleObject : ModuleCat.{u} baseRing) :
    extensionRing ⊗[middleRing] (extendScalars (algebraMap baseRing middleRing)).obj moduleObject ≃ₗ[
      extensionRing] extensionRing ⊗[baseRing] moduleObject :=
  ((tensorEquivExtendScalars baseRing middleRing moduleObject).symm.baseChange
    middleRing extensionRing _ _).trans
      (AlgebraTensorModule.cancelBaseChange baseRing middleRing extensionRing extensionRing moduleObject)

/-- Cancellation intertwines the scalar extensions of a linear map. -/
lemma tensorExtendScalarsCancel_naturality {source target : ModuleCat.{u} baseRing}
    (morphism : source ⟶ target)
    (element : extensionRing ⊗[middleRing]
      (extendScalars (algebraMap baseRing middleRing)).obj source) :
    tensorExtendScalarsCancel baseRing middleRing extensionRing target
        (((extendScalars (algebraMap baseRing middleRing)).map morphism).hom.baseChange
          extensionRing element) =
      morphism.hom.baseChange extensionRing
        (tensorExtendScalarsCancel baseRing middleRing extensionRing source element) := by
  have compatibility :
      (tensorEquivExtendScalars baseRing middleRing target).symm.toLinearMap ∘ₗ
          ((extendScalars (algebraMap baseRing middleRing)).map morphism).hom =
        morphism.hom.baseChange middleRing ∘ₗ
          (tensorEquivExtendScalars baseRing middleRing source).symm.toLinearMap :=
    LinearMap.ext fun coefficient ↦
      tensorEquivExtendScalars_symm_naturality baseRing middleRing morphism coefficient
  change AlgebraTensorModule.cancelBaseChange baseRing middleRing extensionRing extensionRing target
      (((tensorEquivExtendScalars baseRing middleRing target).symm.toLinearMap.baseChange
        extensionRing) (((extendScalars (algebraMap baseRing middleRing)).map morphism).hom.baseChange
          extensionRing element)) =
    morphism.hom.baseChange extensionRing
      (AlgebraTensorModule.cancelBaseChange baseRing middleRing extensionRing extensionRing source
        (((tensorEquivExtendScalars baseRing middleRing source).symm.toLinearMap.baseChange
          extensionRing) element))
  have tensor_compatibility := LinearMap.congr_fun
    (congrArg (LinearMap.baseChange extensionRing) compatibility) element
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at tensor_compatibility
  rw [tensor_compatibility, LinearMap.baseChange_baseChange]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- Cancellation on a pure tensor whose second factor is given in tensor coordinates. -/
lemma tensorExtendScalarsCancel_tmul (moduleObject : ModuleCat.{u} baseRing)
    (scalar : extensionRing) (element : middleRing ⊗[baseRing] moduleObject) :
    tensorExtendScalarsCancel baseRing middleRing extensionRing moduleObject
        (scalar ⊗ₜ[middleRing] tensorEquivExtendScalars baseRing middleRing moduleObject element) =
      AlgebraTensorModule.cancelBaseChange baseRing middleRing extensionRing extensionRing moduleObject
        (scalar ⊗ₜ[middleRing] element) := by
  simp only [tensorExtendScalarsCancel, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, LinearEquiv.symm_apply_apply]

end ModuleCat
