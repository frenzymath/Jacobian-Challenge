import Jacobian.AlgebraicGeometry.Curve.Basic
import Jacobian.AlgebraicGeometry.IdealSheaf.Section
import Jacobian.AlgebraicGeometry.Modules.Dual

/-!
# The diagonal-minus-constant family on a curve

For a smooth proper curve `C` and a rational point `P`, the diagonal and
`C × {P}` are relative effective Cartier divisors on `C × C`, with the first
factor as parameter. Their ideal modules define the invertible family
`I_Δᵛ ⊗ I_(C × {P})`.
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

/-- The diagonal of the underlying curve. -/
def diagonal (curve : Curve baseField) :
    curve.carrier.left ⟶ pullback curve.carrier.hom curve.carrier.hom :=
  pullback.lift (𝟙 _) (𝟙 _) (by simp)

@[reassoc (attr := simp)]
theorem diagonal_fst (curve : Curve baseField) :
    diagonal curve ≫ pullback.fst curve.carrier.hom curve.carrier.hom = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The constant divisor family with value the rational point. -/
def constantSection (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _) :
    curve.carrier.left ⟶ pullback curve.carrier.hom curve.carrier.hom :=
  pullback.lift (𝟙 _) (curve.carrier.hom ≫ rationalPoint) (by
    rw [Category.assoc, point_over]
    simp)

@[reassoc (attr := simp)]
theorem constantSection_fst (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _) :
    constantSection curve rationalPoint point_over ≫
      pullback.fst curve.carrier.hom curve.carrier.hom = 𝟙 _ :=
  pullback.lift_fst _ _ _

private theorem smooth_fst (curve : Curve baseField) :
    SmoothOfRelativeDimension 1 (pullback.fst curve.carrier.hom curve.carrier.hom) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (IsPullback.of_hasPullback curve.carrier.hom curve.carrier.hom).flip inferInstance

/-- The diagonal is a relative effective Cartier divisor over the first factor. -/
theorem isRelativeEffectiveCartier_diagonal (curve : Curve baseField) :
    (diagonal curve).ker.IsRelativeEffectiveCartier
      (pullback.fst curve.carrier.hom curve.carrier.hom) := by
  letI := smooth_fst curve
  exact (diagonal curve).isRelativeEffectiveCartier_ker_of_section _ (diagonal_fst curve)

/-- The constant section is a relative effective Cartier divisor over the first factor. -/
theorem isRelativeEffectiveCartier_constantSection (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _) :
    (constantSection curve rationalPoint point_over).ker.IsRelativeEffectiveCartier
      (pullback.fst curve.carrier.hom curve.carrier.hom) := by
  letI := smooth_fst curve
  exact Scheme.Hom.isRelativeEffectiveCartier_ker_of_section
    (constantSection curve rationalPoint point_over)
    (pullback.fst curve.carrier.hom curve.carrier.hom)
    (constantSection_fst curve rationalPoint point_over)

instance isInvertible_diagonal_toModules (curve : Curve baseField) :
    (diagonal curve).ker.toModules.IsInvertible :=
  (isRelativeEffectiveCartier_diagonal curve).1.isInvertible_toModules

instance isInvertible_constantSection_toModules (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _) :
    (constantSection curve rationalPoint point_over).ker.toModules.IsInvertible :=
  (isRelativeEffectiveCartier_constantSection curve rationalPoint point_over).1.isInvertible_toModules

/-- The invertible module sheaf `I_Δᵛ ⊗ I_(C × {P})` on the literal product of curves. -/
def abelJacobiFamily (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _) :
    (pullback curve.carrier.hom curve.carrier.hom).Modules :=
  (diagonal curve).ker.toModulesᵛ ⊗
    (constantSection curve rationalPoint point_over).ker.toModules

instance isInvertible_abelJacobiFamily (curve : Curve baseField)
    (rationalPoint : Spec (.of baseField) ⟶ curve.carrier.left)
    (point_over : rationalPoint ≫ curve.carrier.hom = 𝟙 _) :
    (abelJacobiFamily curve rationalPoint point_over).IsInvertible := by
  unfold abelJacobiFamily
  infer_instance

/-- The dual diagonal ideal is a tensor inverse of the diagonal ideal. -/
def diagonalDualTensorIsoUnit (curve : Curve baseField) :
    (diagonal curve).ker.toModulesᵛ ⊗ (diagonal curve).ker.toModules ≅
      SheafOfModules.unit (pullback curve.carrier.hom curve.carrier.hom).ringCatSheaf :=
  β_ _ _ ≪≫ Scheme.Modules.tensorObjDualIsoUnit _

end AlgebraicGeometry.Curve
