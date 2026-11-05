import Jacobian.AlgebraicGeometry.Hilbert.RelativeDivisor
import Jacobian.AlgebraicGeometry.IdealSheaf.FiniteFlat

/-!
# Addition and subtraction of finite flat divisors

On a smooth relative curve, multiplying the ideals of two finite flat families
adds their degrees. If a degree-`d₂` divisor is contained in one of degree
`d₁ + d₂`, colon subtraction produces a finite flat family of degree `d₁`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite
open scoped nonZeroDivisors

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A contained finite flat divisor can be subtracted using its colon ideal. -/
theorem IsHilbertSubscheme.exists_eq_mul {f : X ⟶ S} [SmoothOfRelativeDimension 1 f]
    {d₁ d₂ : ℕ} {T : Over S} {D E : (pullback f T.hom).IdealSheafData}
    (hD : IsHilbertSubscheme f (d₁ + d₂) T D) (hE : IsHilbertSubscheme f d₂ T E) (hle : D ≤ E) :
    ∃ D' : (pullback f T.hom).IdealSheafData, IsHilbertSubscheme f d₁ T D' ∧ D = D' * E := by
  have : SmoothOfRelativeDimension 1 (pullback.snd f T.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f T.hom) ‹_›
  have := SmoothOfRelativeDimension.smooth 1 (pullback.snd f T.hom)
  have hDi := hD.isInvertible
  have hEi := hE.isInvertible
  obtain ⟨_, _, _, hDr⟩ := hD
  obtain ⟨_, _, _, hEr⟩ := hE
  set D' := D.colon E hEi.fg_ideal
  have heq := Scheme.IdealSheafData.eq_colon_mul hDi hEi hle
  have hD'i := Scheme.IdealSheafData.isInvertible_colon hDi hEi hle
  have := Scheme.IdealSheafData.flat_subschemeι_colon_comp (pullback.snd f T.hom) hDi hEi hle
  have hDD' : D ≤ D' := heq.le.trans (fun U ↦ Ideal.mul_le_left)
  have : IsFinite (D'.subschemeι ≫ pullback.snd f T.hom) := by
    rw [← Scheme.IdealSheafData.inclusion_subschemeι hDD', Category.assoc]
    infer_instance
  have hlfp := hD'i.isLocallyPrincipal.locallyOfFinitePresentation_subschemeι_comp
    (pullback.snd f T.hom)
  refine ⟨D', ⟨inferInstance, inferInstance, hlfp, fun t ↦ ?_⟩, heq⟩
  have : IsFinite ((D' * E).subschemeι ≫ pullback.snd f T.hom) := by rw [← heq]; infer_instance
  have : Flat ((D' * E).subschemeι ≫ pullback.snd f T.hom) := by rw [← heq]; infer_instance
  have key := Scheme.IdealSheafData.finrank_subschemeι_mul_comp (pullback.snd f T.hom) hD'i hEi t
  rw [← heq, hDr, hEr] at key
  exact (Nat.add_right_cancel key).symm

end AlgebraicGeometry

namespace AlgebraicGeometry
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Multiplication of divisor ideals adds their finite flat degrees. -/
theorem IsHilbertSubscheme.mul [SmoothOfRelativeDimension 1 f] {d₁ d₂ : ℕ} {T : Over S}
    {I₁ I₂ : (pullback f T.hom).IdealSheafData} (h₁ : IsHilbertSubscheme f d₁ T I₁)
    (h₂ : IsHilbertSubscheme f d₂ T I₂) : IsHilbertSubscheme f (d₁ + d₂) T (I₁ * I₂) := by
  have : SmoothOfRelativeDimension 1 (pullback.snd f T.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f T.hom) ‹_›
  have := SmoothOfRelativeDimension.smooth 1 (pullback.snd f T.hom)
  have hI₁ := h₁.isInvertible
  have hI₂ := h₂.isInvertible
  obtain ⟨_, _, _, hr₁⟩ := h₁
  obtain ⟨_, _, _, hr₂⟩ := h₂
  have := Scheme.IdealSheafData.flat_subschemeι_mul_comp (pullback.snd f T.hom) hI₁ hI₂
  have := Scheme.IdealSheafData.isFinite_subschemeι_mul_comp (pullback.snd f T.hom) (I := I₁)
    (J := I₂)
  refine ⟨inferInstance, inferInstance,
    (hI₁.mul_effectiveCartier hI₂).isLocallyPrincipal.locallyOfFinitePresentation_subschemeι_comp
      (pullback.snd f T.hom), fun t ↦ ?_⟩
  rw [Scheme.IdealSheafData.finrank_subschemeι_mul_comp _ hI₁ hI₂, hr₁, hr₂]

end AlgebraicGeometry
