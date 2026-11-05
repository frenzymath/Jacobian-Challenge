import Jacobian.AlgebraicGeometry.Picard.DegreeMembership
import Jacobian.AlgebraicGeometry.Picard.RationalPoint

/-!
# Normalized representatives of degree-zero Picard sections

A rational point on a proper geometrically integral scheme identifies the
relative Picard sheaf with the presheaf of classes normalized along that point.
Degree-zero sections therefore have canonical normalized classes, natural over
arbitrary parameter schemes. Their fibre degree is already zero before
sheafification.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

open Scheme

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
  [source.Over (Spec (.of baseField))]
  [IsProper (source ↘ Spec (.of baseField))]
  [GeometricallyIntegral (source ↘ Spec (.of baseField))]
  (rationalPoint : Spec (.of baseField) ⟶ source)
  (point_over : rationalPoint ≫ source ↘ Spec (.of baseField) = 𝟙 _)

/-- Normalize a degree-zero Picard section along the chosen rational point. -/
def normalizedDegreeZeroClass :
    (picardFunctorDegree (source ↘ Spec (.of baseField)) 0).obj ⟶
      (picardFunctorNormalized (source ↘ Spec (.of baseField)) rationalPoint
        point_over).toFunctor :=
  (picardFunctorDegreeι (source ↘ Spec (.of baseField)) 0).hom ≫
    (normalizedPicardIso rationalPoint point_over).inv

/-- The normalized class represents the original section in the full Picard sheaf. -/
theorem normalizedDegreeZeroClass_classifies (parameter : Over (Spec (.of baseField)))
    (sectionValue : (picardFunctorDegree (source ↘ Spec (.of baseField)) 0).obj.obj
      (op parameter)) :
    (toPicardFunctor (source ↘ Spec (.of baseField))).app (op parameter)
        ((normalizedDegreeZeroClass rationalPoint point_over).app
          (op parameter) sectionValue).val =
      (picardFunctorDegreeι (source ↘ Spec (.of baseField)) 0).hom.app
        (op parameter) sectionValue := by
  exact ConcreteCategory.congr_hom
    (congr_app (normalizedPicardIso rationalPoint point_over).inv_hom_id (op parameter))
    ((picardFunctorDegreeι (source ↘ Spec (.of baseField)) 0).hom.app
      (op parameter) sectionValue)

/-- The canonical normalized class has degree zero on every field-valued fibre. -/
theorem normalizedDegreeZeroClass_mem (parameter : Over (Spec (.of baseField)))
    (sectionValue : (picardFunctorDegree (source ↘ Spec (.of baseField)) 0).obj.obj
      (op parameter)) :
    ((normalizedDegreeZeroClass rationalPoint point_over).app
      (op parameter) sectionValue).val ∈
        (picardSubfunctorDegree (source ↘ Spec (.of baseField)) 0).obj (op parameter) := by
  apply (exists_picardFunctorDegree_lift_iff (source ↘ Spec (.of baseField)) _ 0).mp
  exact ⟨sectionValue,
    (normalizedDegreeZeroClass_classifies rationalPoint point_over parameter sectionValue).symm⟩

/-- Parameter restriction pulls back the same normalized class on the whole product. -/
theorem normalizedDegreeZeroClass_map
    {parameter otherParameter : Over (Spec (.of baseField))}
    (restriction : otherParameter ⟶ parameter)
    (sectionValue : (picardFunctorDegree (source ↘ Spec (.of baseField)) 0).obj.obj
      (op parameter)) :
    Pic.map (baseChangeMap (source ↘ Spec (.of baseField)) restriction)
        ((normalizedDegreeZeroClass rationalPoint point_over).app
          (op parameter) sectionValue).val =
      ((normalizedDegreeZeroClass rationalPoint point_over).app (op otherParameter)
        ((picardFunctorDegree (source ↘ Spec (.of baseField)) 0).obj.map
          restriction.op sectionValue)).val := by
  exact congrArg Subtype.val
    ((normalizedDegreeZeroClass rationalPoint point_over).naturality_apply
      restriction.op sectionValue).symm

/-- Sheafifying the normalized class in degree zero recovers the given section. -/
theorem normalizedDegreeZeroClass_toSheafify
    (parameter : Over (Spec (.of baseField)))
    (sectionValue : (picardFunctorDegree (source ↘ Spec (.of baseField)) 0).obj.obj
      (op parameter)) :
    (toSheafify (fppfTopology.over (Spec (.of baseField)))
        (picardSubfunctorDegree (source ↘ Spec (.of baseField)) 0).toFunctor).app
        (op parameter)
        ⟨((normalizedDegreeZeroClass rationalPoint point_over).app
          (op parameter) sectionValue).val,
          normalizedDegreeZeroClass_mem rationalPoint point_over parameter sectionValue⟩ =
      sectionValue := by
  apply injective_picardFunctorDegreeι_app (source ↘ Spec (.of baseField)) 0 parameter
  rw [picardFunctorDegreeι_app_toSheafify]
  exact normalizedDegreeZeroClass_classifies rationalPoint point_over parameter sectionValue

end AlgebraicGeometry
