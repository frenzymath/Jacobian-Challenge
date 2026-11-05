import Jacobian.AlgebraicGeometry.Modules.TensorInvertible

/-!
# Tensor powers of module sheaves

Tensor powers use the actual symmetric monoidal structure on module sheaves.
Powers of invertible sheaves are invertible.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{u}}

/-- The `n`-th tensor power `M^{⊗ n}` of an `𝒪_X`-module: `M^{⊗ 0} = 𝟙_ X.Modules` and
`M^{⊗ (n + 1)} = M ⊗ M^{⊗ n}`. -/
noncomputable def tensorPow (moduleSheaf : scheme.Modules) : ℕ → scheme.Modules
  | 0 => 𝟙_ scheme.Modules
  | otherExponent + 1 => moduleSheaf ⊗ tensorPow moduleSheaf otherExponent

@[simp]
lemma tensorPow_zero (moduleSheaf : scheme.Modules) : moduleSheaf.tensorPow 0 = 𝟙_ scheme.Modules :=
  rfl

lemma tensorPow_succ (moduleSheaf : scheme.Modules) (otherExponent : ℕ) : moduleSheaf.tensorPow (otherExponent + 1) = moduleSheaf ⊗ moduleSheaf.tensorPow otherExponent :=
  rfl

/-- `M^{⊗ (a + b)} ≅ M^{⊗ a} ⊗ M^{⊗ b}`. -/
noncomputable def tensorPowAddIso (moduleSheaf : scheme.Modules) :
    ∀ firstElement secondElement : ℕ, moduleSheaf.tensorPow (firstElement + secondElement) ≅ moduleSheaf.tensorPow firstElement ⊗ moduleSheaf.tensorPow secondElement
  | 0, secondElement => eqToIso (congrArg moduleSheaf.tensorPow (Nat.zero_add secondElement)) ≪≫ (λ_ _).symm
  | firstElement + 1, secondElement => eqToIso (congrArg moduleSheaf.tensorPow (Nat.succ_add firstElement secondElement)) ≪≫
      (Iso.refl moduleSheaf ⊗ᵢ tensorPowAddIso moduleSheaf firstElement secondElement) ≪≫ (α_ _ _ _).symm


/-- Tensor powers of invertible module sheaves are invertible. -/
instance isInvertible_tensorPow (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible] (exponent : ℕ) :
    (moduleSheaf.tensorPow exponent).IsInvertible := by
  induction exponent with
  | zero => exact isInvertible_tensorUnit
  | succ exponent inductionHypothesis =>
    letI := inductionHypothesis
    exact isInvertible_tensorObj moduleSheaf (moduleSheaf.tensorPow exponent)

end AlgebraicGeometry.Scheme.Modules
