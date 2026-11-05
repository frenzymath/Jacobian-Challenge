import Jacobian.AlgebraicGeometry.Picard.DegreeZero

/-!
# Tensor-compatible Picard representations

A commutative group representing the degree-zero Picard sheaf is tensor
compatible when its identity classifies the trivial line bundle and its
products classify tensor products whenever the points have line-bundle
representatives. Fppf local representatives imply that the representing
correspondence is multiplicative on all sections, including those without
global line-bundle representatives.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry

variable {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}

/-- A supplied representing group classifies the trivial bundle at its identity
and tensor products at products of points with bundle representatives. -/
def PicardTensorCompatible (structureMap : scheme ⟶ Spec (.of baseField))
    (representingGroup : CommGrp (Over (Spec (.of baseField))))
    (representation : (picardFunctorDegree structureMap 0).obj.RepresentableBy
      representingGroup.X) : Prop :=
  (∀ parameter : Over (Spec (.of baseField)),
    (picardFunctorDegreeι structureMap 0).hom.app (.op parameter)
        (representation.homEquiv (1 : parameter ⟶ representingGroup.X)) =
      (toPicardFunctor structureMap).app (.op parameter)
        (Scheme.Pic.mk (Scheme.Modules.unit (pullback structureMap parameter.hom)))) ∧
  ∀ (parameter : Over (Spec (.of baseField)))
    (firstPoint secondPoint : parameter ⟶ representingGroup.X)
    (firstLine secondLine tensorLine : (pullback structureMap parameter.hom).Modules)
    [firstLine.IsInvertible] [secondLine.IsInvertible] [tensorLine.IsInvertible],
    Nonempty (tensorLine ≅ firstLine ⊗ secondLine) →
    (picardFunctorDegreeι structureMap 0).hom.app (.op parameter)
        (representation.homEquiv firstPoint) =
      (toPicardFunctor structureMap).app (.op parameter) (Scheme.Pic.mk firstLine) →
    (picardFunctorDegreeι structureMap 0).hom.app (.op parameter)
        (representation.homEquiv secondPoint) =
      (toPicardFunctor structureMap).app (.op parameter) (Scheme.Pic.mk secondLine) →
    (picardFunctorDegreeι structureMap 0).hom.app (.op parameter)
        (representation.homEquiv (firstPoint * secondPoint)) =
      (toPicardFunctor structureMap).app (.op parameter) (Scheme.Pic.mk tensorLine)

namespace PicardTensorCompatible

variable {structureMap : scheme ⟶ Spec (.of baseField)}
  [IsProper structureMap] [SmoothOfRelativeDimension 1 structureMap]
  [GeometricallyIrreducible structureMap]
  {representingGroup : CommGrp (Over (Spec (.of baseField)))}
  {representation : (picardFunctorDegree structureMap 0).obj.RepresentableBy
    representingGroup.X}

private theorem localRepresentative {parameter cover : Over (Spec (.of baseField))}
    (restriction : cover ⟶ parameter) (point : parameter ⟶ representingGroup.X)
    (localClass : picardDegreeZeroSubgroup structureMap cover)
    (localEquality :
      (toSheafify (Scheme.fppfTopology.over (Spec (.of baseField)))
        (picardSubfunctorDegree structureMap 0).toFunctor).app (.op cover) localClass =
      (picardFunctorDegree structureMap 0).obj.map restriction.op
        (representation.homEquiv point)) :
    (picardFunctorDegreeι structureMap 0).hom.app (.op cover)
        (representation.homEquiv (restriction ≫ point)) =
      (toPicardFunctor structureMap).app (.op cover) localClass.val := by
  rw [representation.homEquiv_comp, ← localEquality]
  exact picardFunctorDegreeι_app_toSheafify structureMap 0 localClass

/-- Bundle-level tensor compatibility makes the representing correspondence a
group isomorphism on every test scheme. No global representatives are required. -/
def homMulEquiv (compatibility : PicardTensorCompatible structureMap representingGroup
    representation) (parameter : Over (Spec (.of baseField))) :
    (parameter ⟶ representingGroup.X) ≃*
      (picardDegreeZeroFunctorGrp structureMap).obj (.op parameter) := by
  let classifyingEquiv (testScheme : Over (Spec (.of baseField))) :
      (testScheme ⟶ representingGroup.X) ≃
        (picardDegreeZeroFunctorGrp structureMap).obj (.op testScheme) :=
    representation.homEquiv
  refine { classifyingEquiv parameter with map_mul' := ?_ }
  intro firstPoint secondPoint
  let topology := Scheme.fppfTopology.over (Spec (.of baseField))
  let presentation := toSheafify topology (picardSubfunctorDegree structureMap 0).toFunctor
  let coveringSieve := Presheaf.imageSieve presentation (representation.homEquiv firstPoint) ⊓
    Presheaf.imageSieve presentation (representation.homEquiv secondPoint)
  have covering : coveringSieve ∈ topology parameter := topology.intersection_covering
    (Presheaf.imageSieve_mem topology presentation _) (Presheaf.imageSieve_mem topology presentation _)
  apply (((isSheaf_iff_isSheaf_of_type topology _).1
    (picardFunctorDegree structureMap 0).property).isSeparated coveringSieve covering).ext
  rintro cover restriction ⟨⟨firstLift, firstEquality⟩, ⟨secondLift, secondEquality⟩⟩
  let firstClass : picardDegreeZeroSubgroup structureMap cover := firstLift
  let secondClass : picardDegreeZeroSubgroup structureMap cover := secondLift
  obtain ⟨firstLine, firstInvertible, firstRepresentative⟩ := Scheme.Pic.exists_mk_eq firstClass.val
  obtain ⟨secondLine, secondInvertible, secondRepresentative⟩ :=
    Scheme.Pic.exists_mk_eq secondClass.val
  letI := firstInvertible
  letI := secondInvertible
  have firstClassifies :
      (picardFunctorDegreeι structureMap 0).hom.app (.op cover)
          (representation.homEquiv (restriction ≫ firstPoint)) =
        (toPicardFunctor structureMap).app (.op cover) (Scheme.Pic.mk firstLine) := by
    rw [firstRepresentative]
    exact localRepresentative restriction firstPoint firstClass firstEquality
  have secondClassifies :
      (picardFunctorDegreeι structureMap 0).hom.app (.op cover)
          (representation.homEquiv (restriction ≫ secondPoint)) =
        (toPicardFunctor structureMap).app (.op cover) (Scheme.Pic.mk secondLine) := by
    rw [secondRepresentative]
    exact localRepresentative restriction secondPoint secondClass secondEquality
  have tensorClassifies := compatibility.2 cover (restriction ≫ firstPoint)
    (restriction ≫ secondPoint) firstLine secondLine (firstLine ⊗ secondLine)
    ⟨Iso.refl _⟩ firstClassifies secondClassifies
  have restrictedProduct :
      (picardDegreeZeroFunctorGrp structureMap).map restriction.op
        (classifyingEquiv parameter firstPoint * classifyingEquiv parameter secondPoint) =
        presentation.app (.op cover) (firstClass * secondClass) :=
    map_sheafify_mul topology (picardDegreeZeroPresheafGrp structureMap)
      (object := parameter) (otherObject := cover)
      (classifyingEquiv parameter firstPoint) (classifyingEquiv parameter secondPoint)
      restriction firstClass secondClass firstEquality secondEquality
  have restrictedRepresented :
      (picardDegreeZeroFunctorGrp structureMap).map restriction.op
        (classifyingEquiv parameter (firstPoint * secondPoint)) =
      classifyingEquiv cover ((restriction ≫ firstPoint) * (restriction ≫ secondPoint)) := by
    change (picardFunctorDegree structureMap 0).obj.map restriction.op
        (representation.homEquiv (firstPoint * secondPoint)) =
      representation.homEquiv ((restriction ≫ firstPoint) * (restriction ≫ secondPoint))
    rw [← representation.homEquiv_comp, MonObj.comp_mul]
  change (picardDegreeZeroFunctorGrp structureMap).map restriction.op
      (classifyingEquiv parameter (firstPoint * secondPoint)) =
    (picardDegreeZeroFunctorGrp structureMap).map restriction.op
      (classifyingEquiv parameter firstPoint * classifyingEquiv parameter secondPoint)
  calc
    (picardDegreeZeroFunctorGrp structureMap).map restriction.op
        (classifyingEquiv parameter (firstPoint * secondPoint)) =
      classifyingEquiv cover ((restriction ≫ firstPoint) * (restriction ≫ secondPoint)) :=
        restrictedRepresented
    _ = presentation.app (.op cover) (firstClass * secondClass) := by
      apply injective_picardFunctorDegreeι_app structureMap 0 cover
      rw [picardFunctorDegreeι_app_toSheafify]
      change (picardFunctorDegreeι structureMap 0).hom.app (.op cover)
          (representation.homEquiv ((restriction ≫ firstPoint) * (restriction ≫ secondPoint))) =
        (toPicardFunctor structureMap).app (.op cover) (firstClass.val * secondClass.val)
      exact tensorClassifies.trans (by
        rw [Scheme.Pic.mk_tensorObj, firstRepresentative, secondRepresentative])
    _ = (picardDegreeZeroFunctorGrp structureMap).map restriction.op
        (classifyingEquiv parameter firstPoint * classifyingEquiv parameter secondPoint) :=
      restrictedProduct.symm

end PicardTensorCompatible

end AlgebraicGeometry
