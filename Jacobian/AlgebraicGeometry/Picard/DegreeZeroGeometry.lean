import Jacobian.AlgebraicGeometry.Curve.GenusLineBundle
import Jacobian.AlgebraicGeometry.Picard.AbelCover
import Jacobian.AlgebraicGeometry.Picard.DegreeTranslation

/-!
# A proper Hilbert cover of the degree-zero Picard scheme

Over a separably closed field, a line bundle of degree equal to the genus
identifies the degree-zero and degree-genus Picard sheaves. Thus the proper
Hilbert cover of the degree-genus sheaf covers every representative of the
degree-zero sheaf as well. Such a representative is universally closed and
geometrically irreducible.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable {baseField : Type u} [Field baseField] [IsSepClosed baseField]
  {source : Scheme.{u}} [source.Over (Spec (.of baseField))]
  [IsProper (source ↘ Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
  [GeometricallyIrreducible (source ↘ Spec (.of baseField))]

private def genusRepresentation (representative : Over (Spec (.of baseField)))
    (representation : (picardFunctorDegree (source ↘ Spec (.of baseField)) 0).obj.RepresentableBy
      representative) :
    (picardFunctorDegree (source ↘ Spec (.of baseField))
      (source.arithmeticGenus baseField)).obj.RepresentableBy representative := by
  let existence := Modules.exists_isInvertible_degree_eq_genus
    (baseField := baseField) (source := source)
  let genusLine := existence.choose
  letI := existence.choose_spec.1
  have genusDegree : Pic.degreeHom (k := baseField) (Pic.mk genusLine) =
      Multiplicative.ofAdd (source.arithmeticGenus baseField : ℤ) := by
    change Multiplicative.ofAdd (Pic.degree baseField (Pic.mk genusLine)) = _
    rw [Pic.degree_mk, existence.choose_spec.2]
  let translation := picardFunctorDegreeTensorIso (Pic.mk genusLine) genusDegree
    (degree := 0) (targetDegree := (source.arithmeticGenus baseField : ℤ)) (by omega)
  exact representation.ofIso ((sheafToPresheaf _ _).mapIso translation)

/-- Any representative of the degree-zero Picard sheaf over a separably
closed field is covered by a proper geometrically integral Hilbert scheme. -/
theorem exists_surjective_of_representableBy_picardFunctorDegree_zero
    (representative : Over (Spec (.of baseField)))
    (representation : (picardFunctorDegree (source ↘ Spec (.of baseField)) 0).obj.RepresentableBy
      representative) :
    ∃ (cover : Over (Spec (.of baseField))) (coverMap : cover ⟶ representative),
      IsProper cover.hom ∧ GeometricallyIntegral cover.hom ∧ Surjective coverMap.left :=
  exists_surjective_of_representableBy_picardFunctorDegree_genus representative
    (genusRepresentation representative representation)

/-- The degree-zero Picard sheaf has universally closed representatives over
a separably closed ground field. -/
theorem universallyClosed_of_representableBy_picardFunctorDegree_zero
    (representative : Over (Spec (.of baseField)))
    (representation : (picardFunctorDegree (source ↘ Spec (.of baseField)) 0).obj.RepresentableBy
      representative) : UniversallyClosed representative.hom :=
  universallyClosed_of_representableBy_picardFunctorDegree_genus representative
    (genusRepresentation representative representation)

/-- The degree-zero Picard sheaf has geometrically irreducible representatives
over a separably closed ground field. -/
theorem geometricallyIrreducible_of_representableBy_picardFunctorDegree_zero
    (representative : Over (Spec (.of baseField)))
    (representation : (picardFunctorDegree (source ↘ Spec (.of baseField)) 0).obj.RepresentableBy
      representative) : GeometricallyIrreducible representative.hom :=
  geometricallyIrreducible_of_representableBy_picardFunctorDegree_genus representative
    (genusRepresentation representative representation)

end AlgebraicGeometry
