import Jacobian.AlgebraicGeometry.Hilbert.RelativeDivisorOperations
import Jacobian.AlgebraicGeometry.IdealSheaf.Tensor
import Jacobian.AlgebraicGeometry.Picard.Sheaf

/-!
# Divisor classes and Abel maps

A finite flat divisor on a smooth relative curve determines the class of its
dual ideal. This construction commutes with base change and sends sums of
divisors to products of Picard classes.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme

variable {total baseScheme : Scheme.{u}} (structureMap : total ⟶ baseScheme)
  [SmoothOfRelativeDimension 1 structureMap]

/-- The Picard class of the line bundle of a finite flat divisor. -/
def abelClass {degree : ℕ} {parameter : Over baseScheme}
    (divisor : (hilbertPresheaf structureMap degree).obj (op parameter)) :
    (pullback structureMap parameter.hom).Pic :=
  letI := divisor.2.isInvertible.isInvertible_dual_toModules
  Pic.mk divisor.1.toModulesᵛ

/-- The dual ideal represents the Picard class of a divisor. -/
def abelClassIso {degree : ℕ} {parameter : Over baseScheme}
    (divisor : (hilbertPresheaf structureMap degree).obj (op parameter)) :
    (fromSkeleton _).obj (abelClass structureMap divisor).val ≅ divisor.1.toModulesᵛ :=
  letI := divisor.2.isInvertible.isInvertible_dual_toModules
  Pic.mkIso _

/-- The line-bundle class of a relative divisor commutes with arbitrary base change. -/
lemma pic_map_abelClass {degree : ℕ} {parameter parameter' : Over baseScheme}
    (restriction : parameter' ⟶ parameter)
    (divisor : (hilbertPresheaf structureMap degree).obj (op parameter)) :
    Pic.map (baseChangeMap structureMap restriction) (abelClass structureMap divisor) =
      abelClass structureMap ((hilbertPresheaf structureMap degree).map restriction.op divisor) := by
  letI := divisor.2.isInvertible.isInvertible_dual_toModules
  have pulledInvertible := (IsHilbertSubscheme.comap restriction divisor.2).isInvertible
  letI := pulledInvertible.isInvertible_dual_toModules
  obtain ⟨comparison⟩ := divisor.2.isInvertible.nonempty_pullback_dual_toModules_iso
    (baseChangeMap structureMap restriction) pulledInvertible
  change Pic.map (baseChangeMap structureMap restriction) (Pic.mk divisor.1.toModulesᵛ) =
    Pic.mk (divisor.1.comap (baseChangeMap structureMap restriction)).toModulesᵛ
  rw [Pic.map_mk]
  exact (Pic.mk_eq_mk_iff _ _).2 ⟨comparison⟩

/-- Adding divisors tensors their line bundles. -/
lemma abelClass_mul {firstDegree secondDegree : ℕ} {parameter : Over baseScheme}
    (first : (hilbertPresheaf structureMap firstDegree).obj (op parameter))
    (second : (hilbertPresheaf structureMap secondDegree).obj (op parameter)) :
    abelClass structureMap ⟨first.1 * second.1, first.2.mul structureMap second.2⟩ =
      abelClass structureMap first * abelClass structureMap second := by
  have firstInvertible := first.2.isInvertible
  have secondInvertible := second.2.isInvertible
  letI := firstInvertible.isInvertible_toModules
  letI := secondInvertible.isInvertible_toModules
  letI := (firstInvertible.mul_effectiveCartier secondInvertible).isInvertible_toModules
  dsimp only [abelClass]
  rw [Pic.mk_dual, Pic.mk_dual, Pic.mk_dual,
    Pic.mk_toModules_mul firstInvertible secondInvertible, mul_inv]

/-- The Abel map to the relative Picard presheaf. -/
def hilbertToPicardNatTrans (degree : ℕ) :
    hilbertPresheaf structureMap degree ⋙ uliftFunctor.{u + 1, u} ⟶
      picardPresheaf structureMap where
  app parameter := TypeCat.ofHom fun divisor ↦ abelClass structureMap divisor.down
  naturality parameter parameter' restriction := by
    ext divisor
    exact (pic_map_abelClass structureMap restriction.unop divisor.down).symm

/-- The Abel map to the fppf Picard sheaf. -/
def hilbertToPicard (degree : ℕ) :
    hilbertPresheaf structureMap degree ⋙ uliftFunctor.{u + 1, u} ⟶
      (picardFunctor structureMap).obj :=
  hilbertToPicardNatTrans structureMap degree ≫ toPicardFunctor structureMap

end AlgebraicGeometry
