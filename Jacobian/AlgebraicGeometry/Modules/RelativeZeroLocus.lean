import Jacobian.AlgebraicGeometry.IdealSheaf.FiniteCartier
import Jacobian.AlgebraicGeometry.Modules.ZeroLocusFunctorial

/-!
# Relative divisors of line-bundle morphisms

On a flat family of integral schemes, a morphism of line bundles which is
nonzero on every fibre defines a relative effective Cartier divisor. When
the family is a proper smooth relative curve, this divisor is finite and
locally of finite presentation over the base.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} {M N : X.Modules} [M.IsInvertible] [N.IsInvertible]

/-- A line-bundle morphism nonzero on all integral fibres cuts out a flat Cartier divisor. -/
theorem Hom.isInvertible_zeroLocus_and_flat (π : X ⟶ S) [Flat π]
    [LocallyOfFinitePresentation π] (φ : M ⟶ N)
    (integralFibres : ∀ s : S, IsIntegral (π.fiber s))
    (nonzeroFibres : ∀ s : S, (pullback (π.fiberι s)).map φ ≠ 0) :
    φ.zeroLocus.IsInvertible ∧ Flat (φ.zeroLocus.subschemeι ≫ π) := by
  apply φ.isLocallyPrincipal_zeroLocus.isInvertible_and_flat π
  intro s
  have : IsIntegral (π.fiber s) := integralFibres s
  rw [Hom.comap_zeroLocus]
  exact Hom.isInvertible_zeroLocus (nonzeroFibres s)

/-- Such a divisor on a proper smooth relative curve is finite, flat and locally
of finite presentation over the base. -/
theorem Hom.isInvertible_zeroLocus_and_isFinite (π : X ⟶ S) [IsProper π]
    [SmoothOfRelativeDimension 1 π] (φ : M ⟶ N)
    (integralFibres : ∀ s : S, IsIntegral (π.fiber s))
    (nonzeroFibres : ∀ s : S, (pullback (π.fiberι s)).map φ ≠ 0) :
    φ.zeroLocus.IsInvertible ∧ IsFinite (φ.zeroLocus.subschemeι ≫ π) ∧
      Flat (φ.zeroLocus.subschemeι ≫ π) ∧
        LocallyOfFinitePresentation (φ.zeroLocus.subschemeι ≫ π) := by
  have := SmoothOfRelativeDimension.smooth 1 π
  obtain ⟨invertible, flat⟩ := φ.isInvertible_zeroLocus_and_flat π integralFibres nonzeroFibres
  obtain ⟨finite, finitePresentation⟩ :=
    invertible.isFinite_and_locallyOfFinitePresentation π flat
  exact ⟨invertible, finite, flat, finitePresentation⟩

end AlgebraicGeometry.Scheme.Modules
