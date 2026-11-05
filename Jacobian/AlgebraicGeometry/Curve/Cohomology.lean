import Jacobian.AlgebraicGeometry.Cohomology.DimensionOne
import Jacobian.AlgebraicGeometry.Cohomology.FiniteProjective
import Jacobian.AlgebraicGeometry.Curve.SeparatingFiniteMap
import Jacobian.AlgebraicGeometry.Geometrically.Smooth

/-!
# Cohomology of smooth proper curves

A finite morphism to the projective line gives finite cohomology for finitely
presented module sheaves on a smooth proper curve. Quasi-coherent cohomology
vanishes above degree one. With cohomological degree, this yields the elementary
Riemann--Roch inequality using the arithmetic genus.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Curve

open Scheme.Modules

variable {baseField : Type u} [Field baseField] (curve : Curve baseField)

/-- Every finitely presented module sheaf on a smooth proper curve has finite
cohomology in all degrees over its ground field. -/
theorem hasFiniteH (moduleSheaf : curve.carrier.left.Modules)
    [moduleSheaf.IsFinitePresentation] :
    HasFiniteH curve.carrier.hom moduleSheaf := by
  obtain ⟨morphism, finite, _, _, _⟩ := curve.exists_isFinite_flat_hom_projectiveLine
  letI : IsFinite morphism.left := finite
  have compatibility : morphism.left ≫ projectiveLineToSpec baseField = curve.carrier.hom :=
    morphism.w
  simpa only [compatibility] using
    hasFiniteH_of_isFinite_projectiveLine baseField morphism.left moduleSheaf

/-- Quasi-coherent cohomology of a smooth proper curve vanishes above degree one. -/
theorem subsingleton_H (moduleSheaf : curve.carrier.left.Modules)
    [moduleSheaf.IsQuasicoherent] {degree : ℕ} (degreeBound : 1 < degree) :
    Subsingleton (moduleSheaf.H degree) := by
  obtain ⟨morphism, finite, _, _, _⟩ := curve.exists_isFinite_flat_hom_projectiveLine
  letI : IsFinite morphism.left := finite
  exact subsingleton_H_of_isAffineHom_projectiveLine
    baseField morphism.left moduleSheaf degreeBound

/-- The elementary Riemann--Roch inequality for a coherent module sheaf, with
cohomological degree and arithmetic genus. -/
theorem degree_add_one_sub_genus_le_finrankH_zero
    (moduleSheaf : curve.carrier.left.Modules) [moduleSheaf.IsFinitePresentation] :
    letI : curve.carrier.left.Over (Spec (.of baseField)) := ⟨curve.carrier.hom⟩
    moduleSheaf.degree baseField + 1 -
        (Scheme.arithmeticGenus baseField curve.carrier.left : ℤ) ≤
      (moduleSheaf.finrankH baseField 0 : ℤ) := by
  letI : curve.carrier.left.Over (Spec (.of baseField)) := ⟨curve.carrier.hom⟩
  letI : IsProper (curve.carrier.left ↘ Spec (.of baseField)) := curve.isProper
  letI : Smooth curve.carrier.hom := SmoothOfRelativeDimension.smooth 1 curve.carrier.hom
  letI : GeometricallyIntegral (curve.carrier.left ↘ Spec (.of baseField)) :=
    Smooth.geometricallyIntegral curve.carrier.hom
  exact Scheme.Modules.degree_add_one_sub_genus_le_finrankH_zero (k := baseField) moduleSheaf
    (fun degree bound ↦ curve.subsingleton_H moduleSheaf bound)
    (fun degree bound ↦ curve.subsingleton_H (unit curve.carrier.left) bound)

end AlgebraicGeometry.Curve
