import Jacobian.AlgebraicGeometry.Picard.TensorCompatible
import Jacobian.CategoryTheory.Sites.SheafifyGrpMap

/-!
# Tensor compatibility of the represented degree-zero Picard group

The inclusion of the degree-zero Picard sheaf into the full Picard sheaf
preserves tensor products. Consequently the canonical commutative group
structure on a representing scheme classifies the trivial line bundle at its
identity and tensor products at products of points.
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
  (structureMap : scheme ⟶ Spec (.of baseField))
  [IsProper structureMap] [SmoothOfRelativeDimension 1 structureMap]
  [GeometricallyIrreducible structureMap]

private def degreeZeroPresheafInclusionGrp :
    picardDegreeZeroPresheafGrp structureMap ⟶ picardPresheafGrp structureMap where
  app parameter := GrpCat.ofHom
    (picardDegreeZeroSubgroup structureMap parameter.unop).subtype
  naturality _ _ restriction := by
    apply GrpCat.hom_ext
    refine MonoidHom.ext fun picardClass ↦ ?_
    rfl

/-- The inclusion of the degree-zero Picard sheaf preserves its group law. -/
def picardDegreeZeroFunctorιGrp :
    picardDegreeZeroFunctorGrp structureMap ⟶ picardFunctorGrp structureMap :=
  sheafifyGrpMap (Scheme.fppfTopology.over (Spec (.of baseField)))
    (degreeZeroPresheafInclusionGrp structureMap)

/-- Forgetting the group laws gives the inclusion of the degree-zero sheaf. -/
theorem picardDegreeZeroFunctorιGrp_whiskerRight :
    CategoryTheory.Functor.whiskerRight (picardDegreeZeroFunctorιGrp structureMap)
        (forget GrpCat) = (picardFunctorDegreeι structureMap 0).hom := by
  change sheafifyMap (Scheme.fppfTopology.over (Spec (.of baseField)))
    (picardSubfunctorDegree structureMap 0).ι = _
  apply sheafifyLift_unique
  exact (toSheafify_naturality (Scheme.fppfTopology.over (Spec (.of baseField)))
    (picardSubfunctorDegree structureMap 0).ι).symm

/-- The tensor-induced group structure on a representing scheme is compatible
with its line-bundle classifying correspondence. -/
theorem picardTensorCompatible_ofRepresentableBy
    {representing : Over (Spec (.of baseField))}
    (representation : (picardFunctorDegree structureMap 0).obj.RepresentableBy representing) :
    letI := picardDegreeZeroCommGrpObj structureMap representation
    PicardTensorCompatible structureMap (CommGrp.mk representing) representation := by
  letI := picardDegreeZeroCommGrpObj structureMap representation
  let classifies (parameter : Over (Spec (.of baseField))) :
      (parameter ⟶ representing) →* (picardFunctorGrp structureMap).obj (.op parameter) :=
    ((picardDegreeZeroFunctorιGrp structureMap).app (.op parameter)).hom.comp
      (GrpObj.homMulEquivOfRepresentableBy
        (sourceFunctor := picardDegreeZeroFunctorGrp structureMap)
          representation parameter).toMonoidHom
  have classifies_apply (parameter : Over (Spec (.of baseField)))
      (point : parameter ⟶ representing) :
      classifies parameter point =
        (picardFunctorDegreeι structureMap 0).hom.app (.op parameter)
          (representation.homEquiv point) := by
    exact ConcreteCategory.congr_hom
      (congr_app (picardDegreeZeroFunctorιGrp_whiskerRight structureMap) (.op parameter))
      (representation.homEquiv point)
  constructor
  · intro parameter
    calc
      _ = classifies parameter 1 := (classifies_apply parameter 1).symm
      _ = 1 := map_one _
      _ = _ := (toPicardFunctorHom structureMap parameter).map_one.symm
  · intro parameter firstPoint secondPoint firstLine secondLine tensorLine
      firstInvertible secondInvertible tensorInvertible comparison firstClassifies secondClassifies
    obtain ⟨comparison⟩ := comparison
    have tensorClass : Scheme.Pic.mk (firstLine ⊗ secondLine) = Scheme.Pic.mk tensorLine :=
      (Scheme.Pic.mk_eq_mk_iff _ _).mpr ⟨comparison.symm⟩
    calc
      _ = classifies parameter (firstPoint * secondPoint) :=
        (classifies_apply parameter (firstPoint * secondPoint)).symm
      _ = classifies parameter firstPoint * classifies parameter secondPoint := map_mul _ _ _
      _ = toPicardFunctorHom structureMap parameter (Scheme.Pic.mk firstLine) *
          toPicardFunctorHom structureMap parameter (Scheme.Pic.mk secondLine) :=
        congrArg₂ (fun firstValue secondValue :
          (picardFunctorGrp structureMap).obj (.op parameter) ↦ firstValue * secondValue)
            ((classifies_apply parameter firstPoint).trans firstClassifies)
            ((classifies_apply parameter secondPoint).trans secondClassifies)
      _ = (toPicardFunctor structureMap).app (.op parameter)
          (Scheme.Pic.mk firstLine * Scheme.Pic.mk secondLine) :=
        (map_mul (toPicardFunctorHom structureMap parameter) _ _).symm
      _ = (toPicardFunctor structureMap).app (.op parameter) (Scheme.Pic.mk tensorLine) :=
        congrArg ((toPicardFunctor structureMap).app (.op parameter))
          ((Scheme.Pic.mk_tensorObj firstLine secondLine).symm.trans tensorClass)

end AlgebraicGeometry
