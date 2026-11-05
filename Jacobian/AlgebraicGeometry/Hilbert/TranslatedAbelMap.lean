import Jacobian.AlgebraicGeometry.Curve.Basic
import Jacobian.AlgebraicGeometry.Picard.AbelMapDegree
import Jacobian.AlgebraicGeometry.Picard.DegreeTranslation

/-!
# Translated Abel maps to the degree-zero Picard scheme

A line-bundle class of degree `-d` translates the Abel class of an effective
divisor of degree `d` into degree zero. Given a scheme representing the
degree-zero Picard sheaf, this defines an actual morphism from the Hilbert
scheme. Its classifying formula holds over every parameter scheme, not only
on field-valued points.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Hilbert

open Scheme

variable {baseField : Type u} [Field baseField] (curve : Curve baseField)

local instance : curve.carrier.left.Over (Spec (.of baseField)) := ⟨curve.carrier.hom⟩

local instance : IsProper (curve.carrier.left ↘ Spec (.of baseField)) :=
  inferInstanceAs (IsProper curve.carrier.hom)

local instance : SmoothOfRelativeDimension 1 (curve.carrier.left ↘ Spec (.of baseField)) :=
  inferInstanceAs (SmoothOfRelativeDimension 1 curve.carrier.hom)

local instance : GeometricallyIrreducible (curve.carrier.left ↘ Spec (.of baseField)) :=
  inferInstanceAs (GeometricallyIrreducible curve.carrier.hom)

variable (degree : ℕ) (twistClass : curve.carrier.left.Pic)
  (twistDegree : Pic.degreeHom (k := baseField) twistClass =
    Multiplicative.ofAdd (-(degree : ℤ)))

/-- Translate each actual divisor class into the degree-zero Picard sheaf. -/
def translatedAbelClass :
    hilbertPresheaf curve.carrier.hom degree ⋙ uliftFunctor.{u + 1, u} ⟶
      (picardFunctorDegree curve.carrier.hom 0).obj :=
  abelMapPresheaf curve.carrier.hom degree ≫
    picardSubfunctorDegreeTensorHom (degree := (degree : ℤ))
      (targetDegree := 0) (shift := -(degree : ℤ)) twistClass twistDegree (by omega) ≫
    toSheafify (fppfTopology.over (Spec (.of baseField)))
      (picardSubfunctorDegree curve.carrier.hom 0).toFunctor

/-- The translated divisor class determines a morphism to any degree-zero
Picard representative. -/
def translatedAbelMap
    {hilbertScheme picardScheme : Over (Spec (.of baseField))}
    (hilbertRepresentation : (hilbertPresheaf curve.carrier.hom degree).RepresentableBy
      hilbertScheme)
    (picardRepresentation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy
      picardScheme) : hilbertScheme ⟶ picardScheme :=
  picardRepresentation.homEquiv.symm
    ((translatedAbelClass curve degree twistClass twistDegree).app (op hilbertScheme)
      (ULift.up (hilbertRepresentation.homEquiv (𝟙 hilbertScheme))))

/-- The defining divisor-class formula is natural on all parameter schemes. -/
theorem translatedAbelMap_homEquiv
    {hilbertScheme picardScheme parameter : Over (Spec (.of baseField))}
    (hilbertRepresentation : (hilbertPresheaf curve.carrier.hom degree).RepresentableBy
      hilbertScheme)
    (picardRepresentation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy
      picardScheme) (parameterMap : parameter ⟶ hilbertScheme) :
    picardRepresentation.homEquiv (parameterMap ≫
        translatedAbelMap curve degree twistClass twistDegree
          hilbertRepresentation picardRepresentation) =
      (translatedAbelClass curve degree twistClass twistDegree).app (op parameter)
        (ULift.up (hilbertRepresentation.homEquiv parameterMap)) := by
  rw [picardRepresentation.homEquiv_comp]
  dsimp only [translatedAbelMap]
  rw [Equiv.apply_symm_apply]
  have divisorRestriction : (hilbertPresheaf curve.carrier.hom degree).map parameterMap.op
      (hilbertRepresentation.homEquiv (𝟙 hilbertScheme)) =
        hilbertRepresentation.homEquiv parameterMap := by
    simpa only [Category.comp_id] using
      (hilbertRepresentation.homEquiv_comp parameterMap (𝟙 hilbertScheme)).symm
  rw [← divisorRestriction]
  exact ((translatedAbelClass curve degree twistClass twistDegree).naturality_apply
    (CD := fun coefficient : Type (u + 1) ↦ coefficient) parameterMap.op
    (ULift.up (hilbertRepresentation.homEquiv (𝟙 hilbertScheme)))).symm

/-- In the full Picard sheaf, the map classifies the divisor line bundle
tensored with the fixed class pulled back from the curve. -/
theorem translatedAbelMap_classifies
    {hilbertScheme picardScheme parameter : Over (Spec (.of baseField))}
    (hilbertRepresentation : (hilbertPresheaf curve.carrier.hom degree).RepresentableBy
      hilbertScheme)
    (picardRepresentation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy
      picardScheme) (parameterMap : parameter ⟶ hilbertScheme) :
    (picardFunctorDegreeι curve.carrier.hom 0).hom.app (op parameter)
        (picardRepresentation.homEquiv (parameterMap ≫
          translatedAbelMap curve degree twistClass twistDegree
            hilbertRepresentation picardRepresentation)) =
      (toPicardFunctor curve.carrier.hom).app (op parameter)
        (abelClass curve.carrier.hom (hilbertRepresentation.homEquiv parameterMap) *
          Pic.map (pullback.fst curve.carrier.hom parameter.hom) twistClass) := by
  rw [translatedAbelMap_homEquiv]
  exact picardFunctorDegreeι_app_toSheafify curve.carrier.hom 0 _

end AlgebraicGeometry.Hilbert
