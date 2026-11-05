import Jacobian.AlgebraicGeometry.Hilbert.OrderedDivisors
import Jacobian.AlgebraicGeometry.Picard.AbelMap

/-!
# Picard classes of ordered divisors

The line-bundle class of an ordered divisor is the product of the classes of
its graph divisors, on every test scheme and including repeated points.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite
open scoped BigOperators AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Hilbert.OrderedDivisors

variable {total baseScheme : Scheme.{u}} (structureMap : total ⟶ baseScheme)
  [SmoothOfRelativeDimension 1 structureMap] [IsSeparated structureMap]

/-- The empty ordered divisor has trivial Picard class. -/
lemma abelClass_ordered_zero {parameter : Over baseScheme}
    (points : Fin 0 → (parameter ⟶ Over.mk structureMap)) :
    abelClass structureMap (element structureMap points) = 1 := by
  have invertible := (element structureMap points).2.isInvertible
  letI := invertible.isInvertible_toModules
  letI := (Scheme.IdealSheafData.isInvertible_top
    (X := pullback structureMap parameter.hom)).isInvertible_toModules
  have emptyIdeal : (element structureMap points).1 = ⊤ := ideal_zero structureMap points
  have comparison : (element structureMap points).1.toModules ≅
      (⊤ : (pullback structureMap parameter.hom).IdealSheafData).toModules :=
    eqToIso (congrArg (fun ideal : (pullback structureMap parameter.hom).IdealSheafData ↦
      ideal.toModules) emptyIdeal)
  have trivialClass : Scheme.Pic.mk (element structureMap points).1.toModules = 1 :=
    ((Scheme.Pic.mk_eq_mk_iff _ _).2 ⟨comparison⟩).trans Scheme.Pic.mk_toModules_top
  dsimp only [abelClass]
  rw [Scheme.Pic.mk_dual, trivialClass, inv_one]

/-- Adjoining the last graph divisor multiplies its class into the previous divisor class. -/
lemma abelClass_ordered_succ {degree : ℕ} {parameter : Over baseScheme}
    (points : Fin (degree + 1) → (parameter ⟶ Over.mk structureMap)) :
    abelClass structureMap (element structureMap points) =
      abelClass structureMap (element structureMap (fun index ↦ points index.castSucc)) *
        abelClass structureMap (element structureMap
          (fun _ : Fin 1 ↦ points (Fin.last degree))) := by
  let first := element structureMap (fun index : Fin degree ↦ points index.castSucc)
  let last := element structureMap (fun _ : Fin 1 ↦ points (Fin.last degree))
  have lastIdeal : last.1 = graphIdeal structureMap (points (Fin.last degree)) := by
    simp [last, element, ideal]
  have tupleDivisor : element structureMap points =
      ⟨first.1 * last.1, first.2.mul structureMap last.2⟩ := by
    apply Subtype.ext
    change ideal structureMap points = ideal structureMap _ * last.1
    rw [lastIdeal, ideal_succ]
  rw [tupleDivisor, abelClass_mul]

/-- The class of an ordered divisor is the product of its graph-divisor classes. -/
lemma abelClass_ordered_prod {degree : ℕ} {parameter : Over baseScheme}
    (points : Fin degree → (parameter ⟶ Over.mk structureMap)) :
    abelClass structureMap (element structureMap points) =
      ∏ index, abelClass structureMap
        (element structureMap (fun _ : Fin 1 ↦ points index)) := by
  induction degree with
  | zero => rw [abelClass_ordered_zero]; simp
  | succ degree inductionHypothesis =>
    rw [abelClass_ordered_succ, Fin.prod_univ_castSucc, inductionHypothesis]

end AlgebraicGeometry.Hilbert.OrderedDivisors
