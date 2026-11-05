import Jacobian.AlgebraicGeometry.Picard.DegreeFieldExtension
import Jacobian.AlgebraicGeometry.Picard.DegreeZero
import Jacobian.AlgebraicGeometry.Curve.BaseChange
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Tensor groups of Picard classes under field extension

The field-extension comparison of degree-zero Picard sheaves respects tensor
products. This is checked on a common fppf cover where both sections have
actual degree-zero Picard representatives, and then descends by separation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {baseField extensionField : Type u} [Field baseField] [Field extensionField]
  [Algebra baseField extensionField] (curve : Curve baseField)

private abbrev fieldMap : Spec (.of extensionField) ⟶ Spec (.of baseField) :=
  Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))

private def rawClassHom (parameter : Over (Spec (.of extensionField))) :
    picardDegreeZeroSubgroup curve.carrier.hom ((Over.map fieldMap).obj parameter) →*
      picardDegreeZeroSubgroup ((Curve.baseChange baseField extensionField).obj curve).carrier.hom
        parameter where
  toFun := (picardPresheafDegreeIsoOfIsPullback
    (IsPullback.of_hasPullback curve.carrier.hom fieldMap) 0).hom.app (.op parameter)
  map_one' := Subtype.ext ((Pic.mapHom
    (pullbackIsoOfIsPullback (IsPullback.of_hasPullback curve.carrier.hom fieldMap)
      parameter).hom).map_one)
  map_mul' firstClass secondClass := Subtype.ext ((Pic.mapHom
    (pullbackIsoOfIsPullback (IsPullback.of_hasPullback curve.carrier.hom fieldMap)
      parameter).hom).map_mul firstClass.val secondClass.val)

private def originalClassHom {groundField : Type u} [Field groundField]
    (groundCurve : Curve groundField) (parameter : Over (Spec (.of groundField))) :
    picardDegreeZeroSubgroup groundCurve.carrier.hom parameter →*
      (picardDegreeZeroFunctorGrp groundCurve.carrier.hom).obj (.op parameter) where
  toFun := (toSheafify (fppfTopology.over (Spec (.of groundField)))
    (picardSubfunctorDegree groundCurve.carrier.hom 0).toFunctor).app (.op parameter)
  map_one' := rfl
  map_mul' firstClass secondClass := toSheafify_mul
    (fppfTopology.over (Spec (.of groundField)))
    (picardDegreeZeroPresheafGrp groundCurve.carrier.hom) firstClass secondClass

private def fieldExtensionEquiv (parameter : Over (Spec (.of extensionField))) :
    (picardDegreeZeroFunctorGrp curve.carrier.hom).obj
        (.op ((Over.map (fieldMap (extensionField := extensionField))).obj parameter)) ≃
      (picardDegreeZeroFunctorGrp
        ((Curve.baseChange baseField extensionField).obj curve).carrier.hom).obj (.op parameter) :=
  ((picardFunctorDegreeIsoOfIsPullback
    (IsPullback.of_hasPullback curve.carrier.hom
      (fieldMap (extensionField := extensionField))) 0).app (.op parameter)).toEquiv

private theorem fieldExtensionEquiv_class (parameter : Over (Spec (.of extensionField)))
    (picardClass : picardDegreeZeroSubgroup curve.carrier.hom
      ((Over.map (fieldMap (extensionField := extensionField))).obj parameter)) :
    fieldExtensionEquiv curve parameter
        (originalClassHom curve ((Over.map fieldMap).obj parameter) picardClass) =
      originalClassHom ((Curve.baseChange baseField extensionField).obj curve) parameter
        (rawClassHom curve parameter picardClass) :=
  picardFunctorDegreeIsoOfIsPullback_hom_app_toSheafify
    (IsPullback.of_hasPullback curve.carrier.hom fieldMap) 0 parameter picardClass

private theorem fieldExtensionEquiv_naturality
    {parameter cover : Over (Spec (.of extensionField))} (restriction : cover ⟶ parameter)
    (sectionValue : (picardFunctorDegree curve.carrier.hom 0).obj.obj
      (.op ((Over.map fieldMap).obj parameter))) :
    (picardFunctorDegree
        ((Curve.baseChange baseField extensionField).obj curve).carrier.hom 0).obj.map restriction.op
        (fieldExtensionEquiv curve parameter sectionValue) =
      fieldExtensionEquiv curve cover
        ((picardFunctorDegree curve.carrier.hom 0).obj.map
          ((Over.map fieldMap).map restriction).op sectionValue) := by
  let baseMap : Spec (.of extensionField) ⟶ Spec (.of baseField) := fieldMap
  let comparison := picardFunctorDegreeIsoOfIsPullback
    (extendedMap := ((Curve.baseChange baseField extensionField).obj curve).carrier.hom)
    (IsPullback.of_hasPullback curve.carrier.hom baseMap) 0
  change (picardFunctorDegree
      ((Curve.baseChange baseField extensionField).obj curve).carrier.hom 0).obj.map
      restriction.op (comparison.hom.app (.op parameter) sectionValue) =
    comparison.hom.app (.op cover)
      ((picardFunctorDegree curve.carrier.hom 0).obj.map
        ((Over.map baseMap).map restriction).op sectionValue)
  simpa only [ConcreteCategory.comp_apply, CategoryTheory.Functor.comp_map,
    CategoryTheory.Functor.op_map, Quiver.Hom.unop_op] using
    (ConcreteCategory.congr_hom (comparison.hom.naturality restriction.op) sectionValue).symm

private theorem fieldExtensionEquiv_mul_of_lifts
    {parameter cover : Over (Spec (.of extensionField))} (restriction : cover ⟶ parameter)
    (firstSection secondSection : (picardDegreeZeroFunctorGrp curve.carrier.hom).obj
      (.op ((Over.map fieldMap).obj parameter)))
    (firstClass secondClass : picardDegreeZeroSubgroup curve.carrier.hom
      ((Over.map fieldMap).obj cover))
    (firstLift : originalClassHom curve ((Over.map fieldMap).obj cover) firstClass =
      (picardDegreeZeroFunctorGrp curve.carrier.hom).map
        ((Over.map fieldMap).map restriction).op firstSection)
    (secondLift : originalClassHom curve ((Over.map fieldMap).obj cover) secondClass =
      (picardDegreeZeroFunctorGrp curve.carrier.hom).map
        ((Over.map fieldMap).map restriction).op secondSection) :
    (picardDegreeZeroFunctorGrp
        ((Curve.baseChange baseField extensionField).obj curve).carrier.hom).map restriction.op
        (fieldExtensionEquiv curve parameter (firstSection * secondSection)) =
      (picardDegreeZeroFunctorGrp
        ((Curve.baseChange baseField extensionField).obj curve).carrier.hom).map restriction.op
        (fieldExtensionEquiv curve parameter firstSection *
          fieldExtensionEquiv curve parameter secondSection) := by
  let baseMap : Spec (.of extensionField) ⟶ Spec (.of baseField) := fieldMap
  let extendedCurve := (Curve.baseChange baseField extensionField).obj curve
  let sourceRestriction := (picardDegreeZeroFunctorGrp curve.carrier.hom).map
    ((Over.map baseMap).map restriction).op
  let targetRestriction := (picardDegreeZeroFunctorGrp extendedCurve.carrier.hom).map
    restriction.op
  change targetRestriction (fieldExtensionEquiv curve parameter (firstSection * secondSection)) =
    targetRestriction (fieldExtensionEquiv curve parameter firstSection *
      fieldExtensionEquiv curve parameter secondSection)
  calc
    _ = fieldExtensionEquiv curve cover
        (sourceRestriction (firstSection * secondSection)) :=
      fieldExtensionEquiv_naturality curve restriction _
    _ = fieldExtensionEquiv curve cover
        (originalClassHom curve ((Over.map baseMap).obj cover) (firstClass * secondClass)) := by
      rw [map_mul sourceRestriction.hom, ← firstLift, ← secondLift,
        map_mul (originalClassHom curve ((Over.map baseMap).obj cover))]
    _ = originalClassHom extendedCurve cover
        (rawClassHom curve cover (firstClass * secondClass)) := fieldExtensionEquiv_class _ _ _
    _ = originalClassHom extendedCurve cover (rawClassHom curve cover firstClass) *
        originalClassHom extendedCurve cover (rawClassHom curve cover secondClass) := by
      rw [map_mul (rawClassHom curve cover), map_mul (originalClassHom extendedCurve cover)]
    _ = fieldExtensionEquiv curve cover (sourceRestriction firstSection) *
        fieldExtensionEquiv curve cover (sourceRestriction secondSection) := by
      rw [← fieldExtensionEquiv_class, ← fieldExtensionEquiv_class, firstLift, secondLift]
    _ = targetRestriction (fieldExtensionEquiv curve parameter firstSection *
        fieldExtensionEquiv curve parameter secondSection) := by
      rw [map_mul targetRestriction.hom]
      exact congrArg₂ (· * ·)
        (fieldExtensionEquiv_naturality curve restriction firstSection).symm
        (fieldExtensionEquiv_naturality curve restriction secondSection).symm

/-- The actual field-extension comparison is a group isomorphism on every test scheme. -/
def picardDegreeZeroFieldExtensionMulEquiv (parameter : Over (Spec (.of extensionField))) :
    (picardDegreeZeroFunctorGrp curve.carrier.hom).obj
        (.op ((Over.map (Spec.map (CommRingCat.ofHom
          (algebraMap baseField extensionField)))).obj parameter)) ≃*
      (picardDegreeZeroFunctorGrp
        ((Curve.baseChange baseField extensionField).obj curve).carrier.hom).obj (.op parameter) := by
  refine { fieldExtensionEquiv curve parameter with map_mul' := ?_ }
  intro firstSection secondSection
  let baseMap : Spec (.of extensionField) ⟶ Spec (.of baseField) := fieldMap
  let topology := fppfTopology.over (Spec (.of extensionField))
  let presentation := CategoryTheory.Functor.whiskerLeft (Over.map baseMap).op
    (toSheafify (fppfTopology.over (Spec (.of baseField)))
      (picardSubfunctorDegree curve.carrier.hom 0).toFunctor)
  haveI : Presheaf.IsLocallySurjective topology presentation :=
    Presheaf.isLocallySurjective_whisker topology
      (fppfTopology.over (Spec (.of baseField))) (Over.map baseMap)
      (toSheafify (fppfTopology.over (Spec (.of baseField)))
        (picardSubfunctorDegree curve.carrier.hom 0).toFunctor)
  let coveringSieve := Presheaf.imageSieve presentation firstSection ⊓
    Presheaf.imageSieve presentation secondSection
  have covering : coveringSieve ∈ topology parameter := topology.intersection_covering
    (Presheaf.imageSieve_mem topology presentation firstSection)
    (Presheaf.imageSieve_mem topology presentation secondSection)
  apply SheafifyGrp.ext (presheaf := (picardSubfunctorDegree
    ((Curve.baseChange baseField extensionField).obj curve).carrier.hom 0).toFunctor)
      coveringSieve covering
  intro cover restriction membership
  obtain ⟨⟨firstClass, firstLift⟩, ⟨secondClass, secondLift⟩⟩ := membership
  exact fieldExtensionEquiv_mul_of_lifts curve restriction firstSection secondSection
    firstClass secondClass firstLift secondLift

end AlgebraicGeometry
