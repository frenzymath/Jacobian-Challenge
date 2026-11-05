import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Descent of flatness along a faithfully flat extension

If a faithfully flat extension of an algebra is flat over the base, so is the algebra.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Module.Flat

theorem of_flat_of_faithfullyFlat {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.FaithfullyFlat B C] [Module.Flat A C] : Module.Flat A B := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  change Function.Injective (f.baseChange B)
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective B C]
  have : ⇑((f.baseChange B).lTensor C) =
      ⇑(TensorProduct.AlgebraTensorModule.cancelBaseChange A B B C P).symm ∘
        ⇑(f.lTensor C) ∘ ⇑(TensorProduct.AlgebraTensorModule.cancelBaseChange A B B C N) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b n =>
        simp only [Function.comp_apply, LinearMap.lTensor_tmul, LinearMap.baseChange_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
        rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add y z hy hz => simp_all [TensorProduct.tmul_add]
    | add x y hx hy => simp_all
  rw [this]
  exact (LinearEquiv.injective _).comp
    ((Module.Flat.lTensor_preserves_injective_linearMap f hf).comp (LinearEquiv.injective _))

end Module.Flat
