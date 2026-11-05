import Jacobian.AlgebraicGeometry.Curve.LineBundleDegree
import Jacobian.AlgebraicGeometry.Picard.DegreeSheaf
import Jacobian.AlgebraicGeometry.Picard.RepresentableGroup

/-!
# The degree-zero Picard group functor

Fibrewise degree-zero classes on a smooth proper geometrically irreducible curve
form a subgroup of the Picard group over every parameter scheme. Sheafification
therefore equips the degree-zero relative Picard sheaf with a group law. A
scheme representing this sheaf inherits the corresponding commutative group
structure, and its classifying correspondence respects tensor products.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite
open scoped MonObj

namespace AlgebraicGeometry

open Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} (structureMap : X ⟶ Spec (.of k))
  [IsProper structureMap] [SmoothOfRelativeDimension 1 structureMap]
  [GeometricallyIrreducible structureMap]

private def fibreDegreeHom {parameter : Over (Spec (.of k))} {K : Type u}
    [Field K] [Algebra k K]
    (point : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ parameter) :
    (pullback structureMap parameter.hom).Pic →* Multiplicative ℤ := by
  let fieldPoint := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  letI : (pullback structureMap fieldPoint.hom).Over (Spec (.of K)) :=
    ⟨pullback.snd structureMap fieldPoint.hom⟩
  letI : IsProper (pullback structureMap fieldPoint.hom ↘ Spec (.of K)) :=
    MorphismProperty.pullback_snd structureMap fieldPoint.hom inferInstance
  letI : GeometricallyIrreducible (pullback structureMap fieldPoint.hom ↘ Spec (.of K)) :=
    MorphismProperty.pullback_snd structureMap fieldPoint.hom inferInstance
  have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  letI : SmoothOfRelativeDimension 1 (pullback structureMap fieldPoint.hom ↘ Spec (.of K)) :=
    MorphismProperty.pullback_snd structureMap fieldPoint.hom inferInstance
  exact (Pic.degreeHom (k := K) (X := pullback structureMap fieldPoint.hom)).comp
    (Pic.mapHom (baseChangeMap structureMap point))

/-- The subgroup of classes of fibrewise degree zero over a parameter scheme. -/
def picardDegreeZeroSubgroup (parameter : Over (Spec (.of k))) :
    Subgroup (pullback structureMap parameter.hom).Pic where
  carrier := (picardSubfunctorDegree structureMap 0).obj (.op parameter)
  one_mem' := by
    intro K _ _ point
    change fibreDegreeHom structureMap point 1 = 1
    exact map_one _
  mul_mem' := by
    intro firstClass secondClass firstDegree secondDegree K _ _ point
    have firstZero := firstDegree K point
    have secondZero := secondDegree K point
    change fibreDegreeHom structureMap point firstClass = 1 at firstZero
    change fibreDegreeHom structureMap point secondClass = 1 at secondZero
    change fibreDegreeHom structureMap point (firstClass * secondClass) = 1
    rw [map_mul, firstZero, secondZero, one_mul]
  inv_mem' := by
    intro picardClass degreeZero K _ _ point
    have zeroDegree := degreeZero K point
    change fibreDegreeHom structureMap point picardClass = 1 at zeroDegree
    change fibreDegreeHom structureMap point picardClass⁻¹ = 1
    rw [map_inv, zeroDegree, inv_one]

/-- Fibrewise degree-zero Picard classes, with restriction by pullback. -/
def picardDegreeZeroPresheafGrp :
    (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj parameter := GrpCat.of (picardDegreeZeroSubgroup structureMap parameter.unop)
  map restriction := GrpCat.ofHom
    { toFun := fun picardClass ↦
        ⟨(picardPresheaf structureMap).map restriction picardClass.val,
          (picardSubfunctorDegree structureMap 0).map restriction picardClass.property⟩
      map_one' := Subtype.ext (map_one ((picardPresheafGrp structureMap).map restriction).hom)
      map_mul' firstClass secondClass :=
        Subtype.ext (map_mul ((picardPresheafGrp structureMap).map restriction).hom
          firstClass.val secondClass.val) }
  map_id parameter := by
    refine GrpCat.hom_ext (MonoidHom.ext fun picardClass ↦ Subtype.ext ?_)
    change Pic.map (baseChangeMap structureMap (𝟙 parameter).unop) picardClass.val =
      picardClass.val
    rw [unop_id, baseChangeMap_id, Pic.map_id]
  map_comp firstRestriction secondRestriction := by
    refine GrpCat.hom_ext (MonoidHom.ext fun picardClass ↦ Subtype.ext ?_)
    change Pic.map (baseChangeMap structureMap (firstRestriction ≫ secondRestriction).unop)
        picardClass.val = Pic.map (baseChangeMap structureMap secondRestriction.unop)
          (Pic.map (baseChangeMap structureMap firstRestriction.unop) picardClass.val)
    rw [unop_comp, baseChangeMap_comp, Pic.map_comp]

/-- Forgetting the group law recovers exactly the degree-zero subfunctor. -/
theorem picardDegreeZeroPresheafGrp_comp_forget :
    picardDegreeZeroPresheafGrp structureMap ⋙ forget GrpCat.{u + 1} =
      (picardSubfunctorDegree structureMap 0).toFunctor :=
  rfl

/-- The degree-zero Picard sheaf as a group-valued presheaf. -/
def picardDegreeZeroFunctorGrp :
    (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u + 1} :=
  sheafifyGrp (fppfTopology.over (Spec (.of k))) (picardDegreeZeroPresheafGrp structureMap)

/-- Forgetting the sheafified group law gives the degree-zero Picard sheaf. -/
theorem picardDegreeZeroFunctorGrp_comp_forget :
    picardDegreeZeroFunctorGrp structureMap ⋙ forget GrpCat.{u + 1} =
      (picardFunctorDegree structureMap 0).obj :=
  rfl

/-- A scheme representing the degree-zero Picard sheaf inherits its
commutative group structure from tensor product. -/
@[instance_reducible]
def picardDegreeZeroCommGrpObj {representing : Over (Spec (.of k))}
    (representation : (picardFunctorDegree structureMap 0).obj.RepresentableBy representing) :
    CommGrpObj representing := by
  letI := GrpObj.ofRepresentableBySheafify (fppfTopology.over (Spec (.of k)))
    (picardDegreeZeroPresheafGrp structureMap) representing representation
  haveI := isCommMonObj_ofRepresentableBySheafify (fppfTopology.over (Spec (.of k)))
    (picardDegreeZeroPresheafGrp structureMap)
    (fun parameter (firstClass secondClass : picardDegreeZeroSubgroup structureMap parameter.unop) ↦
      mul_comm firstClass secondClass) representation
  exact {}

/-- The correspondence classifying degree-zero line bundles is a group
homomorphism for the tensor-induced structure on the representing scheme. -/
def picardDegreeZeroClassifyingHom {representing : Over (Spec (.of k))}
    (representation : (picardFunctorDegree structureMap 0).obj.RepresentableBy representing)
    (parameter : Over (Spec (.of k))) :
    letI := picardDegreeZeroCommGrpObj structureMap representation
    picardDegreeZeroSubgroup structureMap parameter →* (parameter ⟶ representing) := by
  letI := picardDegreeZeroCommGrpObj structureMap representation
  exact MonoidHom.mk'
    (fun picardClass ↦ representation.homEquiv.symm
      ((toSheafify (fppfTopology.over (Spec (.of k)))
        (picardSubfunctorDegree structureMap 0).toFunctor).app (.op parameter) picardClass))
    (homEquiv_symm_toSheafify_mul (fppfTopology.over (Spec (.of k)))
      (picardDegreeZeroPresheafGrp structureMap) representation)

end AlgebraicGeometry
