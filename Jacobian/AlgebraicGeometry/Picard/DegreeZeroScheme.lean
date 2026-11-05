import Jacobian.AlgebraicGeometry.Picard.DegreeComponents
import Jacobian.AlgebraicGeometry.Picard.Representability
import Jacobian.AlgebraicGeometry.Picard.TensorRepresentation

/-!
# The degree-zero Picard scheme over a separably closed field

The degree-zero part of the relative Picard sheaf of a smooth proper
geometrically integral curve over a separably closed field is represented by
a commutative group scheme. Its group law classifies tensor products of line
bundles over every parameter scheme.

The representative is obtained from the open and closed degree-zero component
of the actual Picard scheme. No Picard representative is required as input.
-/

noncomputable section

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

open Scheme

variable {baseField : Type u} [Field baseField] [IsSepClosed baseField]
  {sourceScheme : Scheme.{u}}

/-- The degree-zero Picard sheaf of a smooth proper geometrically integral
curve over a separably closed field has a scheme representative whose
commutative group law is compatible with tensor product of line bundles. -/
theorem exists_picardDegreeZeroScheme
    (projection : sourceScheme ⟶ Spec (.of baseField))
    [SmoothOfRelativeDimension 1 projection] [IsProper projection]
    [GeometricallyIntegral projection] :
    ∃ (representing : Over (Spec (.of baseField)))
      (groupStructure : CommGrpObj representing)
      (representation : (picardFunctorDegree projection 0).obj.RepresentableBy representing),
      letI := groupStructure
      PicardTensorCompatible projection (CommGrp.mk representing) representation := by
  letI : Smooth projection := SmoothOfRelativeDimension.smooth 1 projection
  obtain ⟨picardScheme, ⟨picardRepresentation⟩⟩ :=
    exists_representableBy_picardFunctor projection
  obtain ⟨components, _, componentRepresentations, _⟩ :=
    exists_decomposition_picardFunctor_representableBy projection
      picardScheme picardRepresentation
  exact ⟨components 0, picardDegreeZeroCommGrpObj projection (componentRepresentations 0),
    componentRepresentations 0,
    picardTensorCompatible_ofRepresentableBy projection (componentRepresentations 0)⟩

end AlgebraicGeometry
