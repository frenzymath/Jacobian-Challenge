import Jacobian.AlgebraicGeometry.Curve.Twisting

/-!
# A line bundle of degree equal to the genus

On a smooth proper geometrically irreducible curve over a separably closed
field, the descended twisting theorem produces a line bundle with one global
section and vanishing first cohomology. Riemann--Roch gives its degree.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {baseField : Type u} [Field baseField] [IsSepClosed baseField]
  {source : Scheme.{u}} [source.Over (Spec (.of baseField))]
  [IsProper (source ↘ Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
  [GeometricallyIrreducible (source ↘ Spec (.of baseField))]

/-- A smooth proper geometrically irreducible curve over a separably closed
field has an invertible sheaf of degree equal to its arithmetic genus. -/
theorem exists_isInvertible_degree_eq_genus :
    ∃ lineBundle : source.Modules, lineBundle.IsInvertible ∧
      lineBundle.degree baseField = (source.arithmeticGenus baseField : ℤ) := by
  let fieldMap := Spec.map (CommRingCat.ofHom (algebraMap baseField baseField))
  let extendedCurve := Limits.pullback (source ↘ Spec (.of baseField)) fieldMap
  letI : extendedCurve.Over (Spec (.of baseField)) := ⟨Limits.pullback.snd _ _⟩
  obtain ⟨lineBundle, invertible, dimensionZero, dimensionOne⟩ :=
    exists_isInvertible_twist baseField (unit extendedCurve)
  letI := invertible
  let pulledLine := (pullback (Limits.pullback.fst
    (source ↘ Spec (.of baseField)) fieldMap)).obj lineBundle
  have dimension_eq (degree : ℕ) :
      lineBundle.finrankH baseField degree =
        (unit extendedCurve ⊗ pulledLine).finrankH baseField degree :=
    (finrankH_pullback baseField lineBundle degree).symm.trans
      (finrankH_congr baseField (λ_ pulledLine).symm degree)
  have zeroDimension := (dimension_eq 0).trans dimensionZero
  have oneDimension := (dimension_eq 1).trans dimensionOne
  have riemannRoch := finrankH_zero_sub_finrankH_one (baseField := baseField) lineBundle
  rw [zeroDimension, oneDimension] at riemannRoch
  exact ⟨lineBundle, invertible, by omega⟩

end AlgebraicGeometry.Scheme.Modules
