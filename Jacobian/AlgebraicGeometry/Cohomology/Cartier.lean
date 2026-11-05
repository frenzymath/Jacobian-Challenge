import Jacobian.AlgebraicGeometry.Cohomology.Affine.Pushforward
import Jacobian.AlgebraicGeometry.Cohomology.FiniteScheme
import Jacobian.AlgebraicGeometry.Cohomology.Finiteness
import Jacobian.AlgebraicGeometry.Cohomology.LongExact
import Jacobian.AlgebraicGeometry.IdealSheaf.ExactSequence

/-!
# Cohomology of quotients by finite divisors

The quotient of a line bundle by an ideal is the pushforward of its restriction to the closed
subscheme. When that subscheme is finite over a field, the quotient has vanishing higher
cohomology and Euler characteristic equal to the length of the closed subscheme, independently
of the line bundle.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- A line-bundle quotient supported on a finite subscheme has finite-dimensional cohomology
in every degree. -/
theorem finite_H_tensorCokernel (J : X.IdealSheafData)
    [IsFinite (J.subschemeι ≫ (X ↘ Spec (.of k)))]
    (M : X.Modules) [M.IsInvertible] (degree : ℕ) :
    Module.Finite k ((cokernel (J.toModulesι ▷ M)).H degree) := by
  let restrictedModule := (Modules.pullback J.subschemeι).obj M
  have finiteRestriction : Modules.HasFiniteH
      (J.subschemeι ≫ (X ↘ Spec (.of k))) restrictedModule :=
    Modules.hasFiniteH_of_isFinite _ restrictedModule
  have finitePushforward : Modules.HasFiniteH (X ↘ Spec (.of k))
      ((Modules.pushforward J.subschemeι).obj restrictedModule) :=
    (Modules.hasFiniteH_pushforward_iff J.subschemeι _ restrictedModule).2 finiteRestriction
  exact Modules.finite_H_of_iso (J.tensorCokernelIsoPushforward M).symm degree
    (finitePushforward degree)

/-- Positive cohomology dimensions of a line-bundle quotient supported on a finite subscheme
vanish. -/
theorem finrankH_tensorCokernel_succ_eq_zero (J : X.IdealSheafData)
    [IsFinite (J.subschemeι ≫ (X ↘ Spec (.of k)))]
    (M : X.Modules) [M.IsInvertible] (degree : ℕ) :
    (cokernel (J.toModulesι ▷ M)).finrankH k (degree + 1) = 0 := by
  letI : J.subscheme.Over (Spec (.of k)) := ⟨J.subschemeι ≫ (X ↘ Spec (.of k))⟩
  letI : J.subschemeι.IsOver (Spec (.of k)) := ⟨rfl⟩
  letI : IsFinite (J.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsFinite (J.subschemeι ≫ (X ↘ Spec (.of k))))
  rw [Modules.finrankH_congr k (J.tensorCokernelIsoPushforward M),
    Modules.finrankH_pushforward_of_isAffineHom k J.subschemeι]
  letI := Modules.subsingleton_H_succ_of_isFinite (k := k)
    ((Modules.pullback J.subschemeι).obj M) degree
  exact Module.finrank_zero_of_subsingleton

/-- The Euler characteristic of a line-bundle quotient supported on a finite subscheme is the
dimension of its ring of functions. -/
theorem eulerChar_tensorCokernel_eq_finrank (J : X.IdealSheafData)
    [IsFinite (J.subschemeι ≫ (X ↘ Spec (.of k)))] (M : X.Modules) [M.IsInvertible] :
    letI := ((ΓSpecIso (.of k)).inv ≫
      (J.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    (cokernel (J.toModulesι ▷ M)).eulerChar k =
      (Module.finrank k Γ(J.subscheme, ⊤) : ℤ) := by
  letI : J.subscheme.Over (Spec (.of k)) := ⟨J.subschemeι ≫ (X ↘ Spec (.of k))⟩
  letI : J.subschemeι.IsOver (Spec (.of k)) := ⟨rfl⟩
  letI : IsFinite (J.subscheme ↘ Spec (.of k)) :=
    inferInstanceAs (IsFinite (J.subschemeι ≫ (X ↘ Spec (.of k))))
  rw [Modules.eulerChar_congr k (J.tensorCokernelIsoPushforward M),
    Modules.eulerChar_pushforward_of_isAffineHom k J.subschemeι]
  exact Modules.eulerChar_eq_finrank_globalSections_of_isFinite
    ((Modules.pullback J.subschemeι).obj M)

/-- Twisting down by an ideal with finite support decreases Euler characteristic by the
length of the closed subscheme, whenever the two line-bundle cohomologies are finite and
bounded. The ideal need not itself be invertible. -/
theorem eulerChar_eq_tensor_add_finrank (J : X.IdealSheafData)
    [IsFinite (J.subschemeι ≫ (X ↘ Spec (.of k)))] (M : X.Modules) [M.IsInvertible]
    [∀ degree, Module.Finite k ((J.toModules ⊗ M).H degree)]
    [∀ degree, Module.Finite k (M.H degree)] (bound : ℕ)
    (idealVanishing : ∀ degree, bound < degree → Subsingleton ((J.toModules ⊗ M).H degree))
    (lineVanishing : ∀ degree, bound < degree → Subsingleton (M.H degree)) :
    letI := ((ΓSpecIso (.of k)).inv ≫
      (J.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    M.eulerChar k = (J.toModules ⊗ M).eulerChar k +
      (Module.finrank k Γ(J.subscheme, ⊤) : ℤ) := by
  letI finiteQuotient (degree : ℕ) := finite_H_tensorCokernel (k := k) J M degree
  let middleIso : (J.tensorSequence M).X₂ ≅ M := λ_ M
  let middleComparison (degree : ℕ) : (J.tensorSequence M).X₂.H degree ≃ₗ[k] M.H degree :=
    { (Modules.H.mapLinearEquiv middleIso degree).toAddEquiv with
      map_smul' scalar cohomologyClass :=
        (Modules.H.mapLinearEquiv middleIso degree).map_smul
          (globalSectionsRingHom k scalar) cohomologyClass }
  letI finiteFirst (degree : ℕ) : Module.Finite k ((J.tensorSequence M).X₁.H degree) :=
    inferInstanceAs (Module.Finite k ((J.toModules ⊗ M).H degree))
  letI finiteMiddle (degree : ℕ) : Module.Finite k ((J.tensorSequence M).X₂.H degree) :=
    Module.Finite.equiv (middleComparison degree).symm
  letI finiteLast (degree : ℕ) : Module.Finite k ((J.tensorSequence M).X₃.H degree) :=
    finiteQuotient degree
  have middleVanishing (degree : ℕ) (larger : bound < degree) :
      Subsingleton ((J.tensorSequence M).X₂.H degree) := by
    letI := lineVanishing degree larger
    exact (middleComparison degree).injective.subsingleton
  have quotientVanishing (degree : ℕ) (positive : 0 < degree) :
      Subsingleton ((cokernel (J.toModulesι ▷ M)).H degree) := by
    obtain ⟨degree, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt positive)
    exact (Module.finrank_zero_iff (R := k)).mp
      (finrankH_tensorCokernel_succ_eq_zero (k := k) J M degree)
  have additivity := Modules.eulerChar_eq_add_of_shortExact k
    (J.tensorSequence_shortExact M) bound idealVanishing middleVanishing
    (fun degree larger ↦ quotientVanishing degree (lt_of_le_of_lt (Nat.zero_le bound) larger))
  rw [Modules.eulerChar_congr k middleIso] at additivity
  change M.eulerChar k = (J.toModules ⊗ M).eulerChar k +
    (cokernel (J.toModulesι ▷ M)).eulerChar k at additivity
  rw [eulerChar_tensorCokernel_eq_finrank J M] at additivity
  exact additivity

end AlgebraicGeometry.Scheme.IdealSheafData
