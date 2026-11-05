import Jacobian.AlgebraicGeometry.Curve.Basic

/-!
# Pointed smooth proper curves

A pointed curve is a smooth proper geometrically irreducible curve with a rational
point. Morphisms are all curve morphisms preserving that point.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- A smooth proper geometrically irreducible curve with a rational point. -/
structure PointedCurve (baseField : Type u) [Field baseField] where
  curve : Curve baseField
  point : 𝟙_ (Over (Spec (.of baseField))) ⟶ curve.carrier

namespace PointedCurve

variable {baseField : Type u} [Field baseField]

/-- A curve morphism preserving the specified rational points. -/
structure Hom (source target : PointedCurve baseField) where
  map : source.curve ⟶ target.curve
  point_map : source.point ≫ map = target.point

/-- A pointed morphism is determined by its underlying curve morphism. -/
@[ext]
theorem Hom.ext {source target : PointedCurve baseField} (first second : Hom source target)
    (equality : first.map = second.map) : first = second := by
  cases first
  cases second
  cases equality
  rfl

instance : Category (PointedCurve baseField) where
  Hom := Hom
  id curve := ⟨𝟙 curve.curve, Category.comp_id _⟩
  comp {source middle target} first second := ⟨first.map ≫ second.map, by
    change source.point ≫ ((first.map : source.curve.carrier ⟶ middle.curve.carrier) ≫
      (second.map : middle.curve.carrier ⟶ target.curve.carrier)) = target.point
    rw [← Category.assoc, first.point_map, second.point_map]⟩
  id_comp morphism := Hom.ext _ _ (Category.id_comp _)
  comp_id morphism := Hom.ext _ _ (Category.comp_id _)
  assoc first second third := Hom.ext _ _ (Category.assoc _ _ _)

/-- Forget the specified rational point. -/
def forget : PointedCurve baseField ⥤ Curve baseField where
  obj curve := curve.curve
  map morphism := morphism.map

/-- A curve isomorphism carrying one marked point to the other is pointed. -/
def isoMk {source target : PointedCurve baseField}
    (comparison : source.curve ≅ target.curve)
    (point_eq : source.point ≫ comparison.hom = target.point) : source ≅ target where
  hom := ⟨comparison.hom, point_eq⟩
  inv := ⟨comparison.inv, by
    have inverse : (comparison.hom : source.curve.carrier ⟶ target.curve.carrier) ≫
        comparison.inv = 𝟙 source.curve.carrier := comparison.hom_inv_id
    rw [← point_eq]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun morphism : source.curve.carrier ⟶ source.curve.carrier ↦
        source.point ≫ morphism) inverse).trans (Category.comp_id _))⟩
  hom_inv_id := Hom.ext _ _ comparison.hom_inv_id
  inv_hom_id := Hom.ext _ _ comparison.inv_hom_id

end PointedCurve
end AlgebraicGeometry
