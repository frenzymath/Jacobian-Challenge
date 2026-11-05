import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Localization.Defs

/-!
# Derivations on a localization

Let `B` be a localization of `A` at a submonoid `S`, `ψ : B →+* C` a ring homomorphism and `N` a
`C`-module. A derivation along `ψ` is an additive map `δ : B → N` with
`δ (x * y) = ψ x • δ y + ψ y • δ x`. Such a derivation is determined by its restriction to `A`,
and every derivation `A → N` along `ψ ∘ algebraMap A B` extends to `B`, by the quotient rule.

## Main definitions and results

- `IsLocalization.derivation_ext`: two derivations on `B` along `ψ` agreeing on the image of `A`
  are equal.
- `IsLocalization.extendDerivation`: the extension to `B` of a derivation on `A`, constructed as
  the second component of the ring homomorphism `B →+* C ⊕ N` (trivial square-zero extension)
  induced by `a ↦ (ψ a, δ a)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TrivSqZeroExt

namespace IsLocalization

variable {A B C N : Type*} [CommRing A] [CommRing B] [Algebra A B] [CommRing C]
  [AddCommGroup N] [Module C N] (S : Submonoid A) [IsLocalization S B] (ψ : B →+* C)

include S in
/-- **Derivations on a localization are determined on the base ring.** Two additive maps
`δ₁ δ₂ : B → N` satisfying the Leibniz rule along `ψ : B →+* C` and agreeing on the image of
`A` are equal. -/
theorem derivation_ext {δ₁ δ₂ : B → N}
    (h₁ : ∀ x y, δ₁ (x * y) = ψ x • δ₁ y + ψ y • δ₁ x)
    (h₂ : ∀ x y, δ₂ (x * y) = ψ x • δ₂ y + ψ y • δ₂ x)
    (h : ∀ a, δ₁ (algebraMap A B a) = δ₂ (algebraMap A B a)) : δ₁ = δ₂ := by
  funext b
  obtain ⟨⟨a, s⟩, hb⟩ := IsLocalization.surj S b
  have hu : IsUnit (ψ (algebraMap A B s)) := (IsLocalization.map_units B s).map ψ
  have e₁ := h₁ b (algebraMap A B s)
  have e₂ := h₂ b (algebraMap A B s)
  simp only at hb
  rw [hb] at e₁ e₂
  rw [h, h s] at e₁
  rw [e₁, add_right_inj] at e₂
  exact hu.smul_left_cancel.1 e₂

variable (δ : A →+ N)
  (hδ : ∀ x y, δ (x * y) = ψ (algebraMap A B x) • δ y + ψ (algebraMap A B y) • δ x)

/-- The right action of `Cᵐᵒᵖ` on `N` through the left action of the commutative ring `C`. -/
abbrev opModule : Module Cᵐᵒᵖ N :=
  Module.compHom N ((RingHom.id C).fromOpposite fun _ _ ↦ mul_comm _ _)

attribute [local instance] opModule

instance : IsCentralScalar C N := ⟨fun _ _ ↦ rfl⟩

include hδ in
/-- The ring homomorphism `a ↦ (ψ a, δ a)` from `A` to the trivial square-zero extension. -/
def derivationToTrivSqZeroExt : A →+* TrivSqZeroExt C N where
  toFun a := inl (ψ (algebraMap A B a)) + inr (δ a)
  map_one' := by
    have h := hδ 1 1
    simp only [mul_one, map_one, one_smul] at h
    ext
    · simp
    · simpa using (left_eq_add.mp h)
  map_mul' x y := by
    ext
    · simp
    · simp only [map_mul, snd_add, snd_inl, snd_inr, zero_add, snd_mul, fst_add, fst_inl,
        fst_inr, add_zero, hδ]
      change _ = ψ (algebraMap A B x) • δ y + ψ (algebraMap A B y) • δ x
      rfl
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [add_add_add_comm]

lemma fst_derivationToTrivSqZeroExt (a : A) :
    (derivationToTrivSqZeroExt ψ δ hδ a).fst = ψ (algebraMap A B a) := by
  simp [derivationToTrivSqZeroExt]

lemma snd_derivationToTrivSqZeroExt (a : A) :
    (derivationToTrivSqZeroExt ψ δ hδ a).snd = δ a := by
  simp [derivationToTrivSqZeroExt]

/-- The extension to `B` of the ring homomorphism `a ↦ (ψ a, δ a)`. -/
noncomputable def derivationLift : B →+* TrivSqZeroExt C N :=
  IsLocalization.lift (M := S) (g := derivationToTrivSqZeroExt ψ δ hδ) fun s ↦
    isUnit_iff_isUnit_fst.2 (by
      rw [fst_derivationToTrivSqZeroExt]
      exact (IsLocalization.map_units B s).map ψ)

lemma fst_derivationLift (b : B) : (derivationLift S ψ δ hδ b).fst = ψ b := by
  have : (fstHom C C N).toRingHom.comp (derivationLift S ψ δ hδ) = ψ :=
    IsLocalization.ringHom_ext S (RingHom.ext fun a ↦ by
      simp [derivationLift, derivationToTrivSqZeroExt])
  exact congrArg (· b) (congrArg DFunLike.coe this)

/-- **The extension of a derivation to a localization**: for a derivation `δ : A → N` along
`ψ ∘ algebraMap A B`, the unique derivation `B → N` along `ψ` extending it, given by the quotient
rule. -/
noncomputable def extendDerivation : B →+ N where
  toFun b := (derivationLift S ψ δ hδ b).snd
  map_zero' := by simp
  map_add' x y := by simp

lemma extendDerivation_algebraMap (a : A) :
    extendDerivation S ψ δ hδ (algebraMap A B a) = δ a := by
  simp [extendDerivation, derivationLift, derivationToTrivSqZeroExt]

lemma extendDerivation_mul (x y : B) :
    extendDerivation S ψ δ hδ (x * y) =
      ψ x • extendDerivation S ψ δ hδ y + ψ y • extendDerivation S ψ δ hδ x := by
  change (derivationLift S ψ δ hδ (x * y)).snd = _
  rw [map_mul, snd_mul, fst_derivationLift, fst_derivationLift]
  rfl

end IsLocalization
