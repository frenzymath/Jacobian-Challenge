import Jacobian.AlgebraicGeometry.AbelianVariety.Basic
import Jacobian.AlgebraicGeometry.Group.Separated
import Jacobian.AlgebraicGeometry.Picard.DegreeZeroGeometry
import Jacobian.AlgebraicGeometry.Picard.DegreeZeroScheme
import Jacobian.AlgebraicGeometry.Picard.Smooth

/-!
# The degree-zero Picard scheme as an abelian variety

Over a separably closed field, the degree-zero Picard scheme of a smooth proper
geometrically integral curve is smooth of genus dimension. Its proper Hilbert
cover makes it universally closed, and its group structure makes it separated.
Thus it is an abelian variety representing the degree-zero Picard sheaf.
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
  [GeometricallyIntegral (source ↘ Spec (.of baseField))]

/-- Every degree-zero Picard representative is smooth of genus dimension. -/
theorem smoothOfRelativeDimension_of_representableBy_picardFunctorDegree_zero
    (representative : Over (Spec (.of baseField)))
    (representation : (picardFunctorDegree (source ↘ Spec (.of baseField)) 0).obj.RepresentableBy
      representative) :
    SmoothOfRelativeDimension (source.arithmeticGenus baseField) representative.hom := by
  let structureMap : source ⟶ Spec (.of baseField) := source ↘ Spec (.of baseField)
  letI : Smooth structureMap := SmoothOfRelativeDimension.smooth 1 structureMap
  obtain ⟨fullScheme, ⟨fullRepresentation⟩⟩ := exists_representableBy_picardFunctor structureMap
  obtain ⟨components, inclusion, componentRepresentation, componentOpen, _⟩ :=
    exists_decomposition_picardFunctor_representableBy structureMap fullScheme fullRepresentation
  letI := smoothOfRelativeDimension_of_representableBy_picardFunctor fullScheme fullRepresentation
  letI := componentOpen 0
  have componentSmooth := smoothOfRelativeDimension_comp
    (n := 0) (m := source.arithmeticGenus baseField) (inclusion 0).left fullScheme.hom
  rw [zero_add, Over.w (inclusion 0)] at componentSmooth
  let comparison := representation.uniqueUpToIso (componentRepresentation 0)
  haveI : IsIso comparison.hom.left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (.of baseField))).map comparison.hom))
  rw [← Over.w comparison.hom, MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension (source.arithmeticGenus baseField))]
  exact componentSmooth

/-- Every degree-zero Picard representative is proper over its ground field. -/
theorem isProper_of_representableBy_picardFunctorDegree_zero
    (representative : Over (Spec (.of baseField)))
    (representation : (picardFunctorDegree (source ↘ Spec (.of baseField)) 0).obj.RepresentableBy
      representative) : IsProper representative.hom := by
  letI := picardDegreeZeroCommGrpObj (source ↘ Spec (.of baseField)) representation
  letI := smoothOfRelativeDimension_of_representableBy_picardFunctorDegree_zero
    representative representation
  letI : Smooth representative.hom :=
    SmoothOfRelativeDimension.smooth (source.arithmeticGenus baseField) representative.hom
  letI := universallyClosed_of_representableBy_picardFunctorDegree_zero
    representative representation
  exact {}

/-- The degree-zero Picard sheaf is represented by an abelian variety whose
group law classifies tensor products, with dimension equal to the genus. -/
theorem exists_abelianVariety_representableBy_picardFunctorDegree_zero :
    ∃ (variety : AbelianVariety baseField)
      (representation : (picardFunctorDegree (source ↘ Spec (.of baseField)) 0).obj.RepresentableBy
        variety.group.X),
      PicardTensorCompatible (source ↘ Spec (.of baseField)) variety.group representation ∧
      SmoothOfRelativeDimension (source.arithmeticGenus baseField) variety.group.X.hom := by
  obtain ⟨representative, groupStructure, representation, tensorCompatible⟩ :=
    exists_picardDegreeZeroScheme (source ↘ Spec (.of baseField))
  letI := groupStructure
  letI := smoothOfRelativeDimension_of_representableBy_picardFunctorDegree_zero
    representative representation
  letI : Smooth representative.hom :=
    SmoothOfRelativeDimension.smooth (source.arithmeticGenus baseField) representative.hom
  letI := isProper_of_representableBy_picardFunctorDegree_zero representative representation
  letI := geometricallyIrreducible_of_representableBy_picardFunctorDegree_zero
    representative representation
  exact ⟨⟨CommGrp.mk representative⟩, representation, tensorCompatible, inferInstance⟩

end AlgebraicGeometry
