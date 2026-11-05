import Jacobian.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Group schemes over a field are separated

The unit section is a closed immersion. The shear automorphism carries its
base-changed slice to the diagonal, so the diagonal is a closed immersion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Every group scheme over a field is separated over that field. -/
instance GrpObj.isSeparated_hom {baseField : Type u} [Field baseField]
    (group : Over (Spec (.of baseField))) [GrpObj group] : IsSeparated group.hom := by
  have unitClosed : IsClosedImmersion η[group].left :=
    isClosedImmersion_of_comp_eq_id group.hom _ (Over.w η[group])
  have diagonal_eq : lift (𝟙 group) (𝟙 group) =
      ((ρ_ group).inv ≫ group ◁ η[group]) ≫
        (CategoryTheory.GrpObj.shearIso group).hom := by
    ext <;> simp [MonObj.comp_mul, ← Hom.one_def]
  letI : IsClosedImmersion (group ◁ η[group]).left := by
    rw [Over.whiskerLeft_left]
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (MorphismProperty.id_mem _ _) unitClosed (by simp) (by simp)
  refine ⟨?_⟩
  have diagonal : Limits.pullback.diagonal group.hom =
      (lift (𝟙 group) (𝟙 group)).left := by
    ext <;> simp
  rw [diagonal, diagonal_eq, Over.comp_left, Over.comp_left]
  infer_instance

end AlgebraicGeometry
