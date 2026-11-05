import Jacobian.AlgebraicGeometry.Hilbert.SectionPencil.Divisor
import Jacobian.AlgebraicGeometry.Hilbert.TranslatedAbelMap
import Jacobian.AlgebraicGeometry.Picard.PoincareTwist

/-!
# Divisor classes of positive Poincaré sections

A section nonzero on every fibre gives an actual finite flat Hilbert divisor.
Its Abel class is the class of the original line bundle on the entire product.
For a pulled-back positive Poincaré bundle, translation by the marked-point
ideal power cancels its positive twist and recovers the represented parameter.
These identities do not require the parameter scheme to be reduced.
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

namespace SectionPencil

/-- The whole-family class of a section divisor is the class of its line bundle. -/
theorem abelClass_hilbertPoint {source base : Scheme.{u}} (structureMap : source ⟶ base)
    [SmoothOfRelativeDimension 1 structureMap] [IsProper structureMap]
    [GeometricallyIntegral structureMap] (degree : ℕ) (parameter : Over base)
    (lineBundle : (pullback structureMap parameter.hom).Modules)
    [lineBundle.IsInvertible]
    (sectionMap : Modules.unit (pullback structureMap parameter.hom) ⟶ lineBundle)
    (nonzeroFibres : ∀ point : parameter.left,
      (Modules.pullback ((pullback.snd structureMap parameter.hom).fiberι point)).map
        sectionMap ≠ 0)
    (constantDegree : ∀ point : parameter.left,
      fibreDegree (pullback.snd structureMap parameter.hom) lineBundle point = degree) :
    abelClass structureMap
        (hilbertPoint structureMap degree parameter lineBundle sectionMap
          nonzeroFibres constantDegree) = Pic.mk lineBundle := by
  let divisor := hilbertPoint structureMap degree parameter lineBundle sectionMap
    nonzeroFibres constantDegree
  have regular : sectionMap.zeroLocus.IsInvertible := divisor.2.isInvertible
  obtain ⟨comparison⟩ := nonempty_iso_dual_zeroLocus sectionMap regular
  apply Pic.eq_iff_nonempty_iso.mpr
  exact ⟨abelClassIso structureMap divisor ≪≫ comparison.symm ≪≫
    (Pic.mkIso lineBundle).symm⟩

end SectionPencil

namespace PointedCurve

variable {baseField : Type u} [Field baseField] (curve : PointedCurve baseField)

local instance sectionDivisorCurveOver : curve.curve.carrier.left.Over
    (Spec (.of baseField)) := ⟨curve.curve.carrier.hom⟩

local instance sectionDivisorCurveProper :
    IsProper (curve.curve.carrier.left ↘ Spec (.of baseField)) := curve.curve.isProper

local instance sectionDivisorCurveSmoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  curve.curve.smoothOfRelativeDimension

local instance sectionDivisorCurveSmooth :
    Smooth (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  SmoothOfRelativeDimension.smooth 1 _

local instance sectionDivisorCurveGeometricallyIrreducible :
    GeometricallyIrreducible (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  curve.curve.geometricallyIrreducible

local instance sectionDivisorCurveGeometricallyIntegral :
    GeometricallyIntegral (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  Smooth.geometricallyIntegral _

/-- Translating a pulled-back positive Poincaré class recovers the actual
degree-zero parameter in the full Picard sheaf. -/
theorem positivePoincareLineBundle_pullback_translated_classifies
    {representative parameter : Over (Spec (.of baseField))}
    (representation : (picardFunctorDegree curve.curve.carrier.hom 0).obj.RepresentableBy
      representative) (parameterMap : parameter ⟶ representative) (exponent : ℕ) :
    (toPicardFunctor curve.curve.carrier.hom).app (op parameter)
        (Pic.mk ((Modules.pullback (baseChangeMap curve.curve.carrier.hom parameterMap)).obj
            (curve.positivePoincareLineBundle representation exponent)) *
          Pic.map (pullback.fst curve.curve.carrier.hom parameter.hom)
            (curve.pointIdealClass ^ exponent)) =
      (picardFunctorDegreeι curve.curve.carrier.hom 0).hom.app (op parameter)
        (representation.homEquiv parameterMap) := by
  have point_over : curve.point.left ≫ curve.curve.carrier.hom = 𝟙 _ := by
    simpa using Over.w curve.point
  letI : (show (pullback curve.curve.carrier.hom representative.hom).Modules from
      poincareLineBundle (source := curve.curve.carrier.left)
        curve.point.left point_over representation).IsInvertible := by
    change (poincareLineBundle (source := curve.curve.carrier.left)
      curve.point.left point_over representation).IsInvertible
    exact isInvertible_poincareLineBundle (source := curve.curve.carrier.left)
      curve.point.left point_over representation
  have projection : baseChangeMap curve.curve.carrier.hom parameterMap ≫
      pullback.fst curve.curve.carrier.hom representative.hom =
        pullback.fst curve.curve.carrier.hom parameter.hom := pullback.lift_fst _ _ _
  have translatedClass :
      Pic.mk ((Modules.pullback (baseChangeMap curve.curve.carrier.hom parameterMap)).obj
          (curve.positivePoincareLineBundle representation exponent)) *
        Pic.map (pullback.fst curve.curve.carrier.hom parameter.hom)
          (curve.pointIdealClass ^ exponent) =
      Pic.map (baseChangeMap curve.curve.carrier.hom parameterMap)
        (Pic.mk (show (pullback curve.curve.carrier.hom representative.hom).Modules from
          poincareLineBundle (source := curve.curve.carrier.left)
            curve.point.left point_over representation)) := by
    rw [← Pic.map_mk, curve.positivePoincareLineBundle_class, Pic.map_mul,
      ← Pic.map_comp, projection, mul_assoc, ← Pic.map_mul, inv_mul_cancel,
      Pic.map_one, mul_one]
  rw [translatedClass, Pic.map_mk]
  exact @poincareLineBundle_pullback_classifies baseField _ curve.curve.carrier.left
    (sectionDivisorCurveOver (curve := curve)) (sectionDivisorCurveProper (curve := curve))
    (sectionDivisorCurveGeometricallyIntegral (curve := curve)) curve.point.left point_over
    representative representation parameter parameterMap

end PointedCurve

end AlgebraicGeometry
