import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Tensor products with a free generator

Tensor products preserve free generators. Tensoring with a free generator of a
rank-one free module gives a bijection on the other factor.
-/

/-- **The tensor product of free generators is a free generator.** If `r ↦ r • a` and
`r ↦ r • b` are bijective, so is `r ↦ r • (a ⊗ₜ b)`. -/
lemma TensorProduct.bijective_smul_tmul {baseRing firstModule secondModule : Type*} [CommRing baseRing] [AddCommGroup firstModule]
    [Module baseRing firstModule] [AddCommGroup secondModule] [Module baseRing secondModule] {firstGenerator : firstModule} {secondGenerator : secondModule}
    (ha : Function.Bijective fun scalar : baseRing ↦ scalar • firstGenerator) (hb : Function.Bijective fun scalar : baseRing ↦ scalar • secondGenerator) :
    Function.Bijective fun scalar : baseRing ↦ scalar • (firstGenerator ⊗ₜ[baseRing] secondGenerator) := by
  have ha' : Function.Bijective (LinearMap.toSpanSingleton baseRing firstModule firstGenerator) := ha
  have hb' : Function.Bijective (LinearMap.toSpanSingleton baseRing secondModule secondGenerator) := hb
  let eA := LinearEquiv.ofBijective (LinearMap.toSpanSingleton baseRing firstModule firstGenerator) ha'
  let eB := LinearEquiv.ofBijective (LinearMap.toSpanSingleton baseRing secondModule secondGenerator) hb'
  have eA_apply (scalar : baseRing) : eA scalar = scalar • firstGenerator := rfl
  have eB_apply (scalar : baseRing) : eB scalar = scalar • secondGenerator := rfl
  have : (fun scalar : baseRing ↦ scalar • (firstGenerator ⊗ₜ[baseRing] secondGenerator)) =
      TensorProduct.congr eA eB ∘ (TensorProduct.lid baseRing baseRing).symm := by
    funext scalar
    simp only [Function.comp_apply, TensorProduct.lid_symm_apply,
      TensorProduct.congr_tmul]
    rw [eA_apply, eB_apply, one_smul, TensorProduct.tmul_smul]
  rw [this]
  exact (TensorProduct.congr eA eB).bijective.comp (TensorProduct.lid baseRing baseRing).symm.bijective

/-- If `e` is a basis of a free module `B` of rank one, i.e. `r ↦ r • e` is bijective, then
`a ↦ a ⊗ₜ e` is a bijection `A → A ⊗[R] B`. -/
lemma TensorProduct.bijective_tmul_right_of_bijective_smul {baseRing firstModule secondModule : Type*} [CommRing baseRing]
    [AddCommGroup firstModule] [Module baseRing firstModule] [AddCommGroup secondModule] [Module baseRing secondModule] {generator : secondModule}
    (he : Function.Bijective fun scalar : baseRing ↦ scalar • generator) :
    Function.Bijective fun firstGenerator : firstModule ↦ firstGenerator ⊗ₜ[baseRing] generator := by
  have he' : Function.Bijective (LinearMap.toSpanSingleton baseRing secondModule generator) := he
  let comparison : baseRing ≃ₗ[baseRing] secondModule := LinearEquiv.ofBijective (LinearMap.toSpanSingleton baseRing secondModule generator) he'
  have : (fun firstGenerator : firstModule ↦ firstGenerator ⊗ₜ[baseRing] generator) =
      TensorProduct.congr (LinearEquiv.refl baseRing firstModule) comparison ∘ (TensorProduct.rid baseRing firstModule).symm := by
    ext firstGenerator
    simp only [comparison, Function.comp_apply, TensorProduct.rid_symm_apply, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply]
    rw [LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply, one_smul]
  rw [this]
  exact (EquivLike.bijective _).comp (EquivLike.bijective _)
