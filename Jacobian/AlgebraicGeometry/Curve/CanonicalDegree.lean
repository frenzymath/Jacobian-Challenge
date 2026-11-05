import Jacobian.AlgebraicGeometry.Curve.SerreDuality
import Jacobian.AlgebraicGeometry.Curve.LineBundleDegree
import Jacobian.AlgebraicGeometry.Cohomology.DimensionOne

/-!
# Canonical degree and large-degree Riemann--Roch

On a smooth proper geometrically irreducible curve over any field, degree-one Serre
duality identifies the first cohomological dimension of a vector bundle with the zeroth
cohomological dimension of its dual tensored with the differential sheaf. In particular,
the canonical sheaf has degree `2g - 2`. A line bundle of greater degree has vanishing
first cohomology and satisfies the large-degree Riemann--Roch formula.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
  [source.Over (Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
  [IsProper (source ↘ Spec (.of baseField))]
  [GeometricallyIrreducible (source ↘ Spec (.of baseField))]

private def associatedCurve : Curve baseField where
  carrier := Over.mk (source ↘ Spec (.of baseField))
  isProper := inferInstanceAs (IsProper (source ↘ Spec (.of baseField)))
  smoothOfRelativeDimension :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField)))
  geometricallyIrreducible :=
    inferInstanceAs (GeometricallyIrreducible (source ↘ Spec (.of baseField)))

/-- Numerical degree-one Serre duality for finite locally free coefficients. -/
theorem finrankH_one_eq_finrankH_dual_tensor (moduleSheaf : source.Modules)
    [moduleSheaf.IsFiniteLocallyFree] :
    moduleSheaf.finrankH baseField 1 =
      (moduleSheafᵛ ⊗ (source ↘ Spec (.of baseField)).relativeDifferentials).finrankH
        baseField 0 := by
  letI : Smooth (source ↘ Spec (.of baseField)) := SmoothOfRelativeDimension.smooth 1 _
  letI : Subsingleton (Spec (.of baseField)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum baseField))
  letI : IsIntegral source :=
    GeometricallyIntegral.isIntegral_of_subsingleton (source ↘ Spec (.of baseField))
  obtain ⟨duality⟩ := Scheme.nonempty_dual_H_one_iso
    (baseField := baseField) (source := source)
  let coefficient :
      (SheafOfModules.isFiniteLocallyFree source.ringCatSheaf).FullSubcategory :=
    ⟨moduleSheaf, inferInstance⟩
  have dimensions : Module.finrank baseField (Module.Dual baseField (moduleSheaf.H 1)) =
      (moduleSheafᵛ ⊗ (source ↘ Spec (.of baseField)).relativeDifferentials).finrankH
        baseField 0 :=
    (duality.app (op coefficient)).toLinearEquiv.finrank_eq
  simpa only [finrankH, Subspace.dual_finrank_eq] using dimensions

/-- The dimension of global canonical differentials is the arithmetic genus. -/
theorem finrankH_relativeDifferentials_zero_eq_genus :
    (source ↘ Spec (.of baseField)).relativeDifferentials.finrankH baseField 0 =
      arithmeticGenus baseField source := by
  let unitDualIso : (unit source)ᵛ ≅ unit source :=
    (λ_ _).symm ≪≫ tensorObjDualIsoUnit (unit source)
  have duality := finrankH_one_eq_finrankH_dual_tensor
    (baseField := baseField) (unit source)
  exact (finrankH_congr baseField
    (whiskerRightIso unitDualIso _ ≪≫ λ_ _) 0).symm.trans duality.symm

/-- First cohomology of the canonical sheaf is one-dimensional. -/
theorem finrankH_relativeDifferentials_one_eq_one :
    (source ↘ Spec (.of baseField)).relativeDifferentials.finrankH baseField 1 = 1 := by
  letI : Smooth (source ↘ Spec (.of baseField)) := SmoothOfRelativeDimension.smooth 1 _
  letI : (source ↘ Spec (.of baseField)).relativeDifferentials.IsInvertible :=
    Hom.isInvertible_relativeDifferentials (source ↘ Spec (.of baseField))
  exact (finrankH_one_eq_finrankH_dual_tensor
      (baseField := baseField) (source ↘ Spec (.of baseField)).relativeDifferentials).trans
    ((finrankH_congr baseField
      (β_ _ _ ≪≫ tensorObjDualIsoUnit
        (source ↘ Spec (.of baseField)).relativeDifferentials) 0).trans
      (finrankH_unit_zero_eq_one (k := baseField)))

/-- The canonical sheaf on a smooth proper geometrically irreducible curve has degree
twice the arithmetic genus minus two. -/
theorem degree_relativeDifferentials :
    (source ↘ Spec (.of baseField)).relativeDifferentials.degree baseField =
      2 * (arithmeticGenus baseField source : ℤ) - 2 := by
  letI : Smooth (source ↘ Spec (.of baseField)) := SmoothOfRelativeDimension.smooth 1 _
  letI : (source ↘ Spec (.of baseField)).relativeDifferentials.IsInvertible :=
    Hom.isInvertible_relativeDifferentials (source ↘ Spec (.of baseField))
  have canonicalEuler := eulerChar_eq_finrankH_zero_sub_finrankH_one
    (k := baseField) (source ↘ Spec (.of baseField)).relativeDifferentials
    (fun degree bound ↦ (associatedCurve (baseField := baseField) (source := source)).subsingleton_H
      _ bound)
  have unitEuler : eulerChar baseField (SheafOfModules.unit source.ringCatSheaf) =
      1 - (arithmeticGenus baseField source : ℤ) :=
    eulerChar_unit_eq_one_sub_genus (k := baseField) (X := source)
    (fun degree bound ↦ (associatedCurve (baseField := baseField) (source := source)).subsingleton_H
      _ bound)
  rw [finrankH_relativeDifferentials_zero_eq_genus,
    finrankH_relativeDifferentials_one_eq_one] at canonicalEuler
  unfold degree
  rw [canonicalEuler, unitEuler]
  ring

/-- Riemann--Roch in cohomological degree expresses `h⁰ - h¹` as degree plus `1 - g`. -/
theorem finrankH_zero_sub_finrankH_one (moduleSheaf : source.Modules)
    [moduleSheaf.IsFinitePresentation] :
    (moduleSheaf.finrankH baseField 0 : ℤ) - moduleSheaf.finrankH baseField 1 =
      moduleSheaf.degree baseField + 1 - (arithmeticGenus baseField source : ℤ) := by
  letI : Smooth (source ↘ Spec (.of baseField)) := SmoothOfRelativeDimension.smooth 1 _
  have coefficientEuler := eulerChar_eq_finrankH_zero_sub_finrankH_one
    (k := baseField) moduleSheaf
    (fun degree bound ↦ (associatedCurve (baseField := baseField) (source := source)).subsingleton_H
      _ bound)
  have unitEuler : eulerChar baseField (SheafOfModules.unit source.ringCatSheaf) =
      1 - (arithmeticGenus baseField source : ℤ) :=
    eulerChar_unit_eq_one_sub_genus (k := baseField) (X := source)
    (fun degree bound ↦ (associatedCurve (baseField := baseField) (source := source)).subsingleton_H
      _ bound)
  unfold degree
  rw [coefficientEuler, unitEuler]
  ring

/-- The Serre-dual tensor of a line bundle has complementary degree in the canonical
degree. -/
theorem degree_dual_tensor_relativeDifferentials (lineBundle : source.Modules)
    [lineBundle.IsInvertible] :
    (lineBundleᵛ ⊗ (source ↘ Spec (.of baseField)).relativeDifferentials).degree baseField =
      2 * (arithmeticGenus baseField source : ℤ) - 2 - lineBundle.degree baseField := by
  letI : (source ↘ Spec (.of baseField)).relativeDifferentials.IsInvertible :=
    Hom.isInvertible_relativeDifferentials (source ↘ Spec (.of baseField))
  have tensorDegree := degree_tensorObj (k := baseField) lineBundle lineBundleᵛ
  have evaluationDegree : (lineBundle ⊗ lineBundleᵛ).degree baseField = 0 :=
    (degree_congr baseField (tensorObjDualIsoUnit lineBundle)).trans (degree_unit baseField)
  have dualDegree : lineBundleᵛ.degree baseField = -lineBundle.degree baseField := by omega
  rw [degree_tensorObj, dualDegree, degree_relativeDifferentials]
  ring

/-- A line bundle of degree greater than the canonical degree has zero first
cohomological dimension. -/
theorem finrankH_one_eq_zero_of_degree_gt_canonical (lineBundle : source.Modules)
    [lineBundle.IsInvertible]
    (degreeBound : 2 * (arithmeticGenus baseField source : ℤ) - 2 <
      lineBundle.degree baseField) :
    lineBundle.finrankH baseField 1 = 0 := by
  letI : (source ↘ Spec (.of baseField)).relativeDifferentials.IsInvertible :=
    Hom.isInvertible_relativeDifferentials (source ↘ Spec (.of baseField))
  have negativeDegree :
      (lineBundleᵛ ⊗ (source ↘ Spec (.of baseField)).relativeDifferentials).degree baseField < 0 := by
    rw [degree_dual_tensor_relativeDifferentials]
    omega
  exact (finrankH_one_eq_finrankH_dual_tensor (baseField := baseField) lineBundle).trans
    (finrankH_zero_eq_zero_of_degree_neg
      (k := baseField) (lineBundleᵛ ⊗ (source ↘ Spec (.of baseField)).relativeDifferentials)
      negativeDegree)

/-- First cohomology itself vanishes above canonical degree; finite-dimensionality comes
from coherent cohomology of the actual curve. -/
theorem subsingleton_H_one_of_degree_gt_canonical (lineBundle : source.Modules)
    [lineBundle.IsInvertible]
    (degreeBound : 2 * (arithmeticGenus baseField source : ℤ) - 2 <
      lineBundle.degree baseField) :
    Subsingleton (lineBundle.H 1) := by
  letI : Module.Finite baseField (lineBundle.H 1) :=
    (associatedCurve (baseField := baseField) (source := source)).hasFiniteH lineBundle 1
  exact (Module.finrank_eq_zero_iff_of_free baseField _).mp
    (finrankH_one_eq_zero_of_degree_gt_canonical lineBundle degreeBound)

/-- Large-degree Riemann--Roch for line bundles on smooth proper geometrically
irreducible curves over arbitrary fields. -/
theorem finrankH_zero_eq_degree_add_one_sub_genus (lineBundle : source.Modules)
    [lineBundle.IsInvertible]
    (degreeBound : 2 * (arithmeticGenus baseField source : ℤ) - 2 <
      lineBundle.degree baseField) :
    (lineBundle.finrankH baseField 0 : ℤ) =
      lineBundle.degree baseField + 1 - (arithmeticGenus baseField source : ℤ) := by
  have riemannRoch := finrankH_zero_sub_finrankH_one (baseField := baseField) lineBundle
  rw [finrankH_one_eq_zero_of_degree_gt_canonical lineBundle degreeBound] at riemannRoch
  simpa only [Nat.cast_zero, sub_zero] using riemannRoch

end AlgebraicGeometry.Scheme.Modules
