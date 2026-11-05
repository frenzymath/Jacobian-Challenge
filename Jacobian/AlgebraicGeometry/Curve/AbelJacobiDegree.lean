import Jacobian.AlgebraicGeometry.Curve.AbelJacobiFamily
import Jacobian.AlgebraicGeometry.Curve.LineBundleDegree
import Jacobian.AlgebraicGeometry.IdealSheaf.SectionDegree

/-!
# Fibrewise degree of the Abel–Jacobi family

The inverse-diagonal tensor family has degree zero after every field-valued
change of parameter. Both section divisors have degree one, and degree is
additive under tensor products on the resulting smooth proper curve.
In particular, arbitrary parameter schemes and all their residue-field fibres
are allowed; neither geometric points nor algebraically closed fields are required.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Curve

variable {baseField : Type u} [Field baseField]

/-- The Abel–Jacobi family has degree zero on any actual field-valued base change. -/
theorem degree_pullback_abelJacobiFamily_eq_zero (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _)
    {extensionField : Type u} [Field extensionField] {fiberScheme : Scheme.{u}}
    (fiberMap : fiberScheme ⟶ pullback curve.carrier.hom curve.carrier.hom)
    (structureMap : fiberScheme ⟶ Spec (.of extensionField))
    (fieldPoint : Spec (.of extensionField) ⟶ curve.carrier.left)
    (square : IsPullback fiberMap structureMap
      (pullback.fst curve.carrier.hom curve.carrier.hom) fieldPoint) :
    letI : fiberScheme.Over (Spec (.of extensionField)) := ⟨structureMap⟩
    ((Scheme.Modules.pullback fiberMap).obj
      (abelJacobiFamily curve rationalPoint point_over)).degree extensionField = 0 := by
  letI : fiberScheme.Over (Spec (.of extensionField)) := ⟨structureMap⟩
  have curveSquare := square.paste_horiz
    (IsPullback.of_hasPullback curve.carrier.hom curve.carrier.hom).flip
  let fiberCurve : Curve extensionField :=
    { carrier := Over.mk structureMap
      isProper := MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @IsProper) curveSquare inferInstance
      smoothOfRelativeDimension := by
        letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
        exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (P := @SmoothOfRelativeDimension 1) curveSquare inferInstance
      geometricallyIrreducible := MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @GeometricallyIrreducible) curveSquare inferInstance }
  letI : IsProper (fiberScheme ↘ Spec (.of extensionField)) := fiberCurve.isProper
  letI : SmoothOfRelativeDimension 1 (fiberScheme ↘ Spec (.of extensionField)) :=
    fiberCurve.smoothOfRelativeDimension
  letI : GeometricallyIrreducible (fiberScheme ↘ Spec (.of extensionField)) :=
    fiberCurve.geometricallyIrreducible
  let projection := pullback.fst curve.carrier.hom curve.carrier.hom
  letI : IsIso ((diagonal curve).ker.subschemeι ≫ projection) :=
    Scheme.Hom.isIso_ker_subschemeι_comp_of_section
      (diagonal curve) projection (diagonal_fst curve)
  letI : IsIso ((constantSection curve rationalPoint point_over).ker.subschemeι ≫ projection) :=
    Scheme.Hom.isIso_ker_subschemeι_comp_of_section
      (constantSection curve rationalPoint point_over) projection
      (constantSection_fst curve rationalPoint point_over)
  let firstDual := (Scheme.Modules.pullback fiberMap).obj (diagonal curve).ker.toModulesᵛ
  let secondLine := (Scheme.Modules.pullback fiberMap).obj
    (constantSection curve rationalPoint point_over).ker.toModules
  let secondDual := (Scheme.Modules.pullback fiberMap).obj
    (constantSection curve rationalPoint point_over).ker.toModulesᵛ
  have firstDegree : firstDual.degree extensionField = 1 :=
    Scheme.IdealSheafData.IsRelativeEffectiveCartier.degree_pullback_dual_toModules_eq_one
      projection (isRelativeEffectiveCartier_diagonal curve) fiberCurve fiberMap fieldPoint square
  have secondDegree : secondDual.degree extensionField = 1 :=
    Scheme.IdealSheafData.IsRelativeEffectiveCartier.degree_pullback_dual_toModules_eq_one
      projection (isRelativeEffectiveCartier_constantSection curve rationalPoint point_over)
      fiberCurve fiberMap fieldPoint square
  let cancelIso : secondLine ⊗ secondDual ≅ Scheme.Modules.unit fiberScheme :=
    (Scheme.Modules.pullbackTensorObjIso fiberMap _ _).symm ≪≫
      (Scheme.Modules.pullback fiberMap).mapIso
        (Scheme.Modules.tensorObjDualIsoUnit
          (constantSection curve rationalPoint point_over).ker.toModules) ≪≫
      Scheme.Modules.pullbackObjUnitIso fiberMap
  have cancelDegree : secondLine.degree extensionField + secondDual.degree extensionField = 0 :=
    (Scheme.Modules.degree_tensorObj secondLine secondDual).symm.trans
      ((Scheme.Modules.degree_congr extensionField cancelIso).trans (Scheme.Modules.degree_unit _))
  let familyIso :
      (Scheme.Modules.pullback fiberMap).obj (abelJacobiFamily curve rationalPoint point_over) ≅
        firstDual ⊗ secondLine :=
    Scheme.Modules.pullbackTensorObjIso fiberMap _ _
  have familyDegree := (Scheme.Modules.degree_congr extensionField familyIso).trans
    (Scheme.Modules.degree_tensorObj firstDual secondLine)
  omega

/-- Every residue-field fibre of the Abel–Jacobi family has degree zero. -/
theorem abelJacobiFamily_degree_fiber (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _) (point : curve.carrier.left) :
    letI := (pullback.fst curve.carrier.hom curve.carrier.hom).fiberOverSpecResidueField point
    ((Scheme.Modules.pullback
      ((pullback.fst curve.carrier.hom curve.carrier.hom).fiberι point)).obj
        (abelJacobiFamily curve rationalPoint point_over)).degree
          (curve.carrier.left.residueField point) = 0 := by
  exact degree_pullback_abelJacobiFamily_eq_zero curve rationalPoint point_over _ _ _
    (IsPullback.of_hasPullback _ _)

/-- Degree zero persists on every residue-field fibre after arbitrary change of parameter. -/
theorem abelJacobiFamily_degree_fiber_baseChange (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _) {parameterScheme : Scheme.{u}}
    (parameter : parameterScheme ⟶ curve.carrier.left) (point : parameterScheme) :
    let projection := pullback.fst curve.carrier.hom curve.carrier.hom
    let baseProjection := pullback.snd projection parameter
    letI := baseProjection.fiberOverSpecResidueField point
    ((Scheme.Modules.pullback (baseProjection.fiberι point)).obj
      ((Scheme.Modules.pullback (pullback.fst projection parameter)).obj
        (abelJacobiFamily curve rationalPoint point_over))).degree
          (parameterScheme.residueField point) = 0 := by
  let projection := pullback.fst curve.carrier.hom curve.carrier.hom
  let baseProjection := pullback.snd projection parameter
  letI := baseProjection.fiberOverSpecResidueField point
  have square := (IsPullback.of_hasPullback baseProjection
    (parameterScheme.fromSpecResidueField point)).paste_horiz
      (IsPullback.of_hasPullback projection parameter)
  have degreeZero := degree_pullback_abelJacobiFamily_eq_zero curve rationalPoint point_over
    (baseProjection.fiberι point ≫ pullback.fst projection parameter)
    (baseProjection.fiberToSpecResidueField point)
    (parameterScheme.fromSpecResidueField point ≫ parameter) square
  exact (Scheme.Modules.degree_congr (parameterScheme.residueField point)
    ((Scheme.Modules.pullbackComp (baseProjection.fiberι point)
      (pullback.fst projection parameter)).app
        (abelJacobiFamily curve rationalPoint point_over))).trans degreeZero

end AlgebraicGeometry.Curve
