import Jacobian.AlgebraicGeometry.Picard.NormalizedDegreeZero

/-!
# A normalized Poincaré line bundle

A rational point on a proper geometrically integral scheme supplies normalized
representatives of relative Picard classes over arbitrary parameter schemes.
Applying this construction to the identity of a degree-zero Picard
representative gives an actual invertible module sheaf on the product. Its
pullback along every parameter morphism classifies that morphism, and its
restriction along the rational point is trivial.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
  [source.Over (Spec (.of baseField))]
  [IsProper (source ↘ Spec (.of baseField))]
  [GeometricallyIntegral (source ↘ Spec (.of baseField))]
  (rationalPoint : Spec (.of baseField) ⟶ source)
  (point_over : rationalPoint ≫ source ↘ Spec (.of baseField) = 𝟙 _)
  {representative : Over (Spec (.of baseField))}
  (representation : (picardFunctorDegree (source ↘ Spec (.of baseField)) 0).obj.RepresentableBy
    representative)

/-- The normalized line bundle associated to the identity of a degree-zero
Picard representative. -/
def poincareLineBundle : (pullback (source ↘ Spec (.of baseField)) representative.hom).Modules :=
  (fromSkeleton _).obj
    (((normalizedDegreeZeroClass rationalPoint point_over).app (op representative)
      (representation.homEquiv (𝟙 representative))).val).val

/-- The Poincaré module sheaf is invertible, without a noetherian hypothesis on
the Picard representative or the parameter schemes. -/
instance isInvertible_poincareLineBundle :
    (poincareLineBundle rationalPoint point_over representation).IsInvertible :=
  Pic.isInvertible _

/-- Its Picard class is the normalized class of the universal parameter. -/
theorem poincareLineBundle_class :
    Pic.mk (poincareLineBundle rationalPoint point_over representation) =
      ((normalizedDegreeZeroClass rationalPoint point_over).app (op representative)
        (representation.homEquiv (𝟙 representative))).val :=
  Pic.mk_fromSkeleton _

/-- The universal line bundle has degree zero on every fibre. -/
theorem poincareLineBundle_mem :
    Pic.mk (poincareLineBundle rationalPoint point_over representation) ∈
      (picardSubfunctorDegree (source ↘ Spec (.of baseField)) 0).obj
        (op representative) := by
  rw [poincareLineBundle_class]
  exact normalizedDegreeZeroClass_mem rationalPoint point_over representative _

/-- The universal class is trivial along the chosen rational point. -/
theorem poincareLineBundle_normalized :
    Pic.map (sectionBaseChange (source ↘ Spec (.of baseField)) rationalPoint point_over
        representative) (Pic.mk (poincareLineBundle rationalPoint point_over representation)) =
      1 := by
  rw [poincareLineBundle_class]
  exact ((normalizedDegreeZeroClass rationalPoint point_over).app (op representative)
    (representation.homEquiv (𝟙 representative))).property

/-- Normalization is an actual trivialization of the restricted line bundle. -/
theorem nonempty_poincareLineBundle_section_iso_unit :
    Nonempty
      ((Modules.pullback (sectionBaseChange (source ↘ Spec (.of baseField)) rationalPoint
          point_over representative)).obj
          (poincareLineBundle rationalPoint point_over representation) ≅
        SheafOfModules.unit representative.left.ringCatSheaf) := by
  apply (Pic.mk_eq_mk_iff _ _).mp
  rw [← Pic.map_mk, poincareLineBundle_normalized, Pic.one_eq_mk_unit]

/-- Pulling the Poincaré bundle to an arbitrary test scheme gives precisely its
normalized degree-zero class. -/
theorem poincareLineBundle_pullback_class
    {parameter : Over (Spec (.of baseField))} (parameterMap : parameter ⟶ representative) :
    Pic.mk ((Modules.pullback (baseChangeMap (source ↘ Spec (.of baseField)) parameterMap)).obj
        (poincareLineBundle rationalPoint point_over representation)) =
      ((normalizedDegreeZeroClass rationalPoint point_over).app (op parameter)
        (representation.homEquiv parameterMap)).val := by
  rw [← Pic.map_mk, poincareLineBundle_class,
    normalizedDegreeZeroClass_map rationalPoint point_over]
  have parameterEquality := representation.homEquiv_comp parameterMap (𝟙 representative)
  rw [Category.comp_id] at parameterEquality
  rw [← parameterEquality]

/-- This identity is in the actual Picard sheaf and holds on the entire test
scheme, including nonreduced parameter schemes. -/
theorem poincareLineBundle_pullback_classifies
    {parameter : Over (Spec (.of baseField))} (parameterMap : parameter ⟶ representative) :
    (toPicardFunctor (source ↘ Spec (.of baseField))).app (op parameter)
        (Pic.mk ((Modules.pullback (baseChangeMap (source ↘ Spec (.of baseField))
          parameterMap)).obj (poincareLineBundle rationalPoint point_over representation))) =
      (picardFunctorDegreeι (source ↘ Spec (.of baseField)) 0).hom.app (op parameter)
        (representation.homEquiv parameterMap) := by
  rw [poincareLineBundle_pullback_class]
  exact normalizedDegreeZeroClass_classifies rationalPoint point_over parameter _

end AlgebraicGeometry
