import Mathlib.RingTheory.Extension.Presentation.Core

/-!
# Finitely generated models of finitely presented algebras

A finitely presented algebra is obtained by base change from a finitely
presented algebra over a finitely generated subring of its base.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open TensorProduct MvPolynomial

namespace Algebra.FinitePresentation

/-- Noetherian approximation of a finitely presented algebra (Stacks 00R0, 05N9): `B` descends
to a finitely generated `ℤ`-subalgebra `A₀` of `A`. That is, there is a finitely presented
`A₀`-algebra `B₀` with `B ≅ A ⊗[A₀] B₀`. -/
theorem exists_fg_subalgebra_isPushout
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B] :
    ∃ (A₀ : Subalgebra ℤ A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀)
      (_ : Algebra B₀ B) (_ : IsScalarTower A₀ B₀ B),
      A₀.FG ∧ Algebra.FinitePresentation A₀ B₀ ∧ Algebra.IsPushout A₀ A B₀ B := by
  let P := Presentation.ofFinitePresentation A B
  let A₀ : Subalgebra ℤ A := Algebra.adjoin ℤ P.coeffs
  have hA₀ : A₀.FG := Subalgebra.fg_def.mpr ⟨_, P.finite_coeffs, rfl⟩
  have : P.HasCoeffs A₀ := ⟨by
    rw [Subalgebra.setRange_algebraMap]
    exact Algebra.subset_adjoin⟩
  let B₀ := P.ModelOfHasCoeffs A₀
  let f : B₀ →ₐ[A₀] B := Ideal.Quotient.liftₐ _ (aeval P.val) fun a ha ↦
    (Ideal.span_le (I := RingHom.ker (aeval (R := A₀) P.val))).mpr
      (Set.range_subset_iff.mpr fun i ↦ by simp) ha
  let _ : Algebra B₀ B := f.toRingHom.toAlgebra
  have : IsScalarTower A₀ B₀ B := .of_algebraMap_eq fun x ↦ (f.commutes x).symm
  refine ⟨A₀, B₀, inferInstance, inferInstance, inferInstance, inferInstance, hA₀,
    inferInstance, ⟨.of_equiv (P.tensorModelOfHasCoeffsEquiv A₀).toLinearEquiv fun b ↦ ?_⟩⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine (P.tensorModelOfHasCoeffsEquiv_tmul A₀ 1 p).trans ?_
  rw [map_one, one_mul]
  rfl

end Algebra.FinitePresentation
