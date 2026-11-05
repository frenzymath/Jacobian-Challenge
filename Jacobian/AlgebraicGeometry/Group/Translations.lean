import Jacobian.AlgebraicGeometry.Group.Separated
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Translations of group schemes

Rational points act on a group scheme by left and right translations. The
inverse point gives the inverse translation, hence an automorphism.
-/

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

variable {baseField : Type schemeUniverse} [Field baseField]

/-- Left translation by a rational point of a group scheme. -/
noncomputable def GrpObj.mulLeft (group : Over (Spec (.of baseField))) [GrpObj group]
    (groupPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ group) : group ⟶ group :=
  lift (toUnit group ≫ groupPoint) (𝟙 group) ≫ μ[group]

variable (group : Over (Spec (.of baseField))) [GrpObj group]

lemma GrpObj.mulLeft_eq_mul (groupPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ group) :
    GrpObj.mulLeft group groupPoint = (toUnit group ≫ groupPoint) * 𝟙 group := rfl

/-- Right translation by a rational point of a group scheme. -/
noncomputable def GrpObj.mulRight (groupPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ group) : group ⟶ group :=
  lift (𝟙 group) (toUnit group ≫ groupPoint) ≫ μ[group]

lemma GrpObj.mulRight_eq_mul (groupPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ group) :
    GrpObj.mulRight group groupPoint = 𝟙 group * (toUnit group ≫ groupPoint) := rfl

lemma GrpObj.mulLeft_comp_mulLeft (groupPoint otherPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ group) :
    GrpObj.mulLeft group groupPoint ≫ GrpObj.mulLeft group otherPoint = GrpObj.mulLeft group (otherPoint * groupPoint) := by
  rw [mulLeft_eq_mul, mulLeft_eq_mul, mulLeft_eq_mul, MonObj.comp_mul, ← Category.assoc,
    toUnit_unique (_ ≫ toUnit group), Category.comp_id, ← mul_assoc, MonObj.comp_mul]

lemma GrpObj.mulRight_comp_mulRight (groupPoint otherPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ group) :
    GrpObj.mulRight group groupPoint ≫ GrpObj.mulRight group otherPoint = GrpObj.mulRight group (groupPoint * otherPoint) := by
  rw [mulRight_eq_mul, mulRight_eq_mul, mulRight_eq_mul, MonObj.comp_mul, ← Category.assoc,
    toUnit_unique (_ ≫ toUnit group), Category.comp_id, mul_assoc, MonObj.comp_mul]

lemma GrpObj.mulLeft_one : GrpObj.mulLeft group 1 = 𝟙 group := by
  rw [mulLeft_eq_mul, MonObj.comp_one, one_mul]

lemma GrpObj.mulRight_one : GrpObj.mulRight group 1 = 𝟙 group := by
  rw [mulRight_eq_mul, MonObj.comp_one, mul_one]

@[simps]
noncomputable def GrpObj.mulLeftIso (groupPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ group) : group ≅ group where
  hom := GrpObj.mulLeft group groupPoint
  inv := GrpObj.mulLeft group groupPoint⁻¹
  hom_inv_id := by rw [mulLeft_comp_mulLeft, inv_mul_cancel, mulLeft_one]
  inv_hom_id := by rw [mulLeft_comp_mulLeft, mul_inv_cancel, mulLeft_one]

@[simps]
noncomputable def GrpObj.mulRightIso (groupPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ group) : group ≅ group where
  hom := GrpObj.mulRight group groupPoint
  inv := GrpObj.mulRight group groupPoint⁻¹
  hom_inv_id := by rw [mulRight_comp_mulRight, mul_inv_cancel, mulRight_one]
  inv_hom_id := by rw [mulRight_comp_mulRight, inv_mul_cancel, mulRight_one]

/-- Left translation induces an isomorphism of the underlying schemes. -/
theorem GrpObj.isIso_mulLeft_left (groupPoint : 𝟙_ (Over (Spec (.of baseField))) ⟶ group) :
    IsIso (GrpObj.mulLeft group groupPoint).left :=
  inferInstanceAs (IsIso ((Over.forget _).mapIso (GrpObj.mulLeftIso group groupPoint)).hom)

end AlgebraicGeometry
