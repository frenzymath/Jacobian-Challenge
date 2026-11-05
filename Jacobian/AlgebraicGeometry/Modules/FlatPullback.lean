import Jacobian.AlgebraicGeometry.Modules.Exactness
import Jacobian.AlgebraicGeometry.Modules.StalkPullback
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Exactness of flat pullback

Monomorphisms of module sheaves are detected on stalks. Under the tensor-product
description of pullback stalks, flatness therefore implies that pullback is an
exact functor.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

lemma mono_of_injective_stalkLinearMap {scheme : Scheme.{u}} {source target : scheme.Modules}
    (morphism : source ⟶ target)
    (injective : ∀ point, Function.Injective (morphism.stalkLinearMap point)) : Mono morphism := by
  refine ShortComplex.Exact.mono_g (S := ShortComplex.mk (0 : 0 ⟶ source) morphism zero_comp) ?_ rfl
  rw [exact_iff_stalkFunctor]
  intro point
  rw [ShortComplex.ab_exact_iff]
  intro element image_zero
  refine ⟨0, ?_⟩
  rw [map_zero]
  exact (injective point (image_zero.trans (map_zero _).symm)).symm

lemma injective_stalkLinearMap_of_mono {scheme : Scheme.{u}} {source target : scheme.Modules}
    (morphism : source ⟶ target) [Mono morphism] (point : scheme) :
    Function.Injective (morphism.stalkLinearMap point) :=
  (AddCommGrpCat.mono_iff_injective ((stalkFunctor point).map morphism)).mp inferInstance

attribute [local instance] stalkAlgebra stalkModule in
/-- Pullback along a flat morphism preserves monomorphisms. -/
theorem mono_pullback_map {baseScheme sourceScheme : Scheme.{u}}
    (morphism : sourceScheme ⟶ baseScheme) [Flat morphism] {source target : baseScheme.Modules}
    (coefficientMap : source ⟶ target) [Mono coefficientMap] :
    Mono ((pullback morphism).map coefficientMap) := by
  refine mono_of_injective_stalkLinearMap _ fun point ↦ ?_
  have : Module.Flat (baseScheme.presheaf.stalk (morphism point))
      (sourceScheme.presheaf.stalk point) := Flat.stalkMap morphism point
  have tensor_injective : Function.Injective (LinearMap.lTensor (sourceScheme.presheaf.stalk point)
      (coefficientMap.stalkLinearMap (morphism point))) :=
    Module.Flat.lTensor_preserves_injective_linearMap _
      (injective_stalkLinearMap_of_mono coefficientMap _)
  intro first second image_eq
  obtain ⟨first, rfl⟩ := (bijective_pullbackStalkMap morphism point source).surjective first
  obtain ⟨second, rfl⟩ := (bijective_pullbackStalkMap morphism point source).surjective second
  rw [← pullbackStalkMap_naturality, ← pullbackStalkMap_naturality] at image_eq
  exact congrArg _ (tensor_injective
    ((bijective_pullbackStalkMap morphism point target).injective image_eq))

instance {baseScheme sourceScheme : Scheme.{u}} (morphism : sourceScheme ⟶ baseScheme)
    [Flat morphism] : (pullback morphism).PreservesMonomorphisms :=
  ⟨fun coefficientMap _ ↦ mono_pullback_map morphism coefficientMap⟩

instance {baseScheme sourceScheme : Scheme.{u}} (morphism : sourceScheme ⟶ baseScheme) :
    PreservesFiniteColimits (pullback morphism) :=
  have := (pullbackPushforwardAdjunction morphism).leftAdjoint_preservesColimits.{0, 0}
  inferInstance

instance {baseScheme sourceScheme : Scheme.{u}} (morphism : sourceScheme ⟶ baseScheme)
    [Flat morphism] : (pullback morphism).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance {baseScheme sourceScheme : Scheme.{u}} (morphism : sourceScheme ⟶ baseScheme)
    [Flat morphism] : PreservesFiniteLimits (pullback morphism) :=
  (pullback morphism).preservesFiniteLimits_of_preservesHomology

end AlgebraicGeometry.Scheme.Modules
