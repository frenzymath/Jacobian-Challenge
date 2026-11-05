import Jacobian.AlgebraicGeometry.Picard.DegreeZeroFieldExtension
import Jacobian.AlgebraicGeometry.Picard.TensorCompatible
import Jacobian.AlgebraicGeometry.BaseChange.GroupPoints

/-!
# Represented Picard groups under field extension

The actual degree-zero Picard comparison and restriction-pullback adjunction
give the field-extension isomorphism for any supplied tensor-compatible
representations. The group law is proved from the multiplicative classifying
correspondences, without assuming abelian-variety geometry.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite MonoidalCategory MonObj

namespace AlgebraicGeometry

variable {baseField extensionField : Type u} [Field baseField] [Field extensionField]
  [Algebra baseField extensionField]

private abbrev fieldMap : Spec (.of extensionField) ⟶ Spec (.of baseField) :=
  Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))

private def representationOnExtendedTests
    {presheaf : (Over (Spec (.of baseField)))ᵒᵖ ⥤ Type (u + 1)}
    {representing : Over (Spec (.of baseField))}
    (representation : presheaf.RepresentableBy representing) :
    ((Over.map (fieldMap (baseField := baseField) (extensionField := extensionField))).op ⋙
      presheaf).RepresentableBy ((baseChange baseField extensionField).obj representing) where
  homEquiv := ((Over.mapPullbackAdj fieldMap).homEquiv _ _).symm.trans representation.homEquiv
  homEquiv_comp restriction point := by
    change representation.homEquiv
      (((Over.mapPullbackAdj fieldMap).homEquiv _ _).symm (restriction ≫ point)) = _
    rw [(Over.mapPullbackAdj fieldMap).homEquiv_naturality_left_symm,
      representation.homEquiv_comp]
    rfl

variable (curve : Curve baseField)
  {sourceGroup : CommGrp (Over (Spec (.of baseField)))}
  {extendedGroup : CommGrp (Over (Spec (.of extensionField)))}
  (sourceRepresentation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy
    sourceGroup.X)
  (extendedRepresentation : (picardFunctorDegree
    ((Curve.baseChange baseField extensionField).obj curve).carrier.hom 0).obj.RepresentableBy
      extendedGroup.X)

private def representedSchemeIso :
    ((baseChange baseField extensionField).mapCommGrp.obj sourceGroup).X ≅ extendedGroup.X :=
  ((representationOnExtendedTests sourceRepresentation).ofIso
    (picardFunctorDegreeIsoOfIsPullback
      (extendedMap := ((Curve.baseChange baseField extensionField).obj curve).carrier.hom)
      (IsPullback.of_hasPullback curve.carrier.hom fieldMap) 0)).uniqueUpToIso
    extendedRepresentation

private theorem representedSchemeIso_app
    (parameter : Over (Spec (.of extensionField)))
    (point : parameter ⟶ (baseChange baseField extensionField).obj sourceGroup.X) :
    extendedRepresentation.homEquiv
        (point ≫ (representedSchemeIso curve sourceRepresentation extendedRepresentation).hom) =
      (picardFunctorDegreeIsoOfIsPullback
      (extendedMap := ((Curve.baseChange baseField extensionField).obj curve).carrier.hom)
        (IsPullback.of_hasPullback curve.carrier.hom fieldMap) 0).hom.app (.op parameter)
          (sourceRepresentation.homEquiv
            (baseChangeHomMulEquiv sourceGroup parameter point)) := by
  rw [extendedRepresentation.homEquiv_comp]
  unfold representedSchemeIso
  change (picardFunctorDegree
    ((Curve.baseChange baseField extensionField).obj curve).carrier.hom 0).obj.map point.op
    (extendedRepresentation.homEquiv (extendedRepresentation.homEquiv.symm
      ((picardFunctorDegreeIsoOfIsPullback
      (extendedMap := ((Curve.baseChange baseField extensionField).obj curve).carrier.hom)
        (IsPullback.of_hasPullback curve.carrier.hom fieldMap) 0).hom.app _
          ((representationOnExtendedTests sourceRepresentation).homEquiv (𝟙 _))))) = _
  rw [Equiv.apply_symm_apply]
  rw [← (picardFunctorDegreeIsoOfIsPullback
      (extendedMap := ((Curve.baseChange baseField extensionField).obj curve).carrier.hom)
    (IsPullback.of_hasPullback curve.carrier.hom fieldMap) 0).hom.naturality_apply]
  rw [← (representationOnExtendedTests sourceRepresentation).homEquiv_comp, Category.comp_id]
  rfl

namespace PicardTensorCompatible

variable {curve sourceRepresentation extendedRepresentation}
  (sourceCompatibility : PicardTensorCompatible curve.carrier.hom sourceGroup
    sourceRepresentation)
  (extendedCompatibility : PicardTensorCompatible
    ((Curve.baseChange baseField extensionField).obj curve).carrier.hom extendedGroup
      extendedRepresentation)

private def pointEquiv (parameter : Over (Spec (.of extensionField))) :
    (parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj sourceGroup).X) ≃*
      (parameter ⟶ extendedGroup.X) :=
  (baseChangeHomMulEquiv sourceGroup parameter).trans
    ((sourceCompatibility.homMulEquiv ((Over.map fieldMap).obj parameter)).trans
      ((picardDegreeZeroFieldExtensionMulEquiv curve parameter).trans
        (extendedCompatibility.homMulEquiv parameter).symm))

private theorem pointEquiv_apply (parameter : Over (Spec (.of extensionField)))
    (point : parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj sourceGroup).X) :
    pointEquiv sourceCompatibility extendedCompatibility parameter point =
      point ≫ (representedSchemeIso curve sourceRepresentation extendedRepresentation).hom := by
  apply extendedRepresentation.homEquiv.injective
  change extendedRepresentation.homEquiv
    (extendedRepresentation.homEquiv.symm
      ((picardFunctorDegreeIsoOfIsPullback
      (extendedMap := ((Curve.baseChange baseField extensionField).obj curve).carrier.hom)
        (IsPullback.of_hasPullback curve.carrier.hom fieldMap) 0).hom.app (.op parameter)
          (sourceRepresentation.homEquiv
            (baseChangeHomMulEquiv sourceGroup parameter point)))) = _
  rw [Equiv.apply_symm_apply]
  exact (representedSchemeIso_app curve sourceRepresentation extendedRepresentation
    parameter point).symm

include sourceCompatibility extendedCompatibility in
private theorem representedSchemeIso_isMonHom :
    IsMonHom (representedSchemeIso curve sourceRepresentation extendedRepresentation).hom where
  one_hom := by
    have unitEquality := (pointEquiv_apply sourceCompatibility extendedCompatibility
      (𝟙_ (Over (Spec (.of extensionField)))) 1).symm.trans
        (map_one (pointEquiv sourceCompatibility extendedCompatibility _))
    simpa only [MonObj.one_eq_one] using unitEquality
  mul_hom := by
    have multiplication (parameter : Over (Spec (.of extensionField)))
        (firstPoint secondPoint : parameter ⟶
          ((baseChange baseField extensionField).mapCommGrp.obj sourceGroup).X) :
        (firstPoint * secondPoint) ≫
            (representedSchemeIso curve sourceRepresentation extendedRepresentation).hom =
          (firstPoint ≫ (representedSchemeIso curve sourceRepresentation extendedRepresentation).hom) *
            (secondPoint ≫ (representedSchemeIso curve sourceRepresentation extendedRepresentation).hom) := by
      rw [← pointEquiv_apply sourceCompatibility extendedCompatibility,
        map_mul, pointEquiv_apply, pointEquiv_apply]
    rw [MonObj.mul_eq_mul, multiplication]
    change CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst _ _ ≫ _)
      (CartesianMonoidalCategory.snd _ _ ≫ _) ≫ μ = _
    congr 1

include sourceCompatibility extendedCompatibility in
/-- The actual field-extension isomorphism for arbitrary tensor-compatible Picard groups. -/
def baseChangeIso :
    (baseChange baseField extensionField).mapCommGrp.obj sourceGroup ≅ extendedGroup :=
  CommGrp.mkIso (representedSchemeIso curve sourceRepresentation extendedRepresentation)
    (representedSchemeIso_isMonHom sourceCompatibility extendedCompatibility).one_hom
    (representedSchemeIso_isMonHom sourceCompatibility extendedCompatibility).mul_hom

/-- The represented group comparison is the actual Cartesian Picard comparison on all points. -/
theorem baseChangeIso_app (parameter : Over (Spec (.of extensionField)))
    (point : parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj sourceGroup).X) :
    extendedRepresentation.homEquiv
        (point ≫ (baseChangeIso sourceCompatibility extendedCompatibility).hom.hom.hom.hom) =
      (picardFunctorDegreeIsoOfIsPullback
      (extendedMap := ((Curve.baseChange baseField extensionField).obj curve).carrier.hom)
        (IsPullback.of_hasPullback curve.carrier.hom
          (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))) 0).hom.app
            (.op parameter)
          (sourceRepresentation.homEquiv
            (baseChangeHomMulEquiv sourceGroup parameter point)) :=
  representedSchemeIso_app curve sourceRepresentation extendedRepresentation parameter point

/-- A represented point classifying a bundle maps to its Cartesian pullback class. -/
theorem baseChangeIso_class (parameter : Over (Spec (.of extensionField)))
    (point : parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj sourceGroup).X)
    (lineBundle : (pullback curve.carrier.hom ((Over.map fieldMap).obj parameter).hom).Modules)
    [lineBundle.IsInvertible]
    (classifies : (picardFunctorDegreeι curve.carrier.hom 0).hom.app
        (.op ((Over.map fieldMap).obj parameter))
        (sourceRepresentation.homEquiv (baseChangeHomMulEquiv sourceGroup parameter point)) =
      (toPicardFunctor curve.carrier.hom).app _ (Scheme.Pic.mk lineBundle)) :
    (picardFunctorDegreeι
        ((Curve.baseChange baseField extensionField).obj curve).carrier.hom 0).hom.app
        (.op parameter) (extendedRepresentation.homEquiv
          (point ≫ (baseChangeIso sourceCompatibility extendedCompatibility).hom.hom.hom.hom)) =
      (toPicardFunctor ((Curve.baseChange baseField extensionField).obj curve).carrier.hom).app
        (.op parameter) (Scheme.Pic.mk ((Scheme.Modules.pullback
          (pullbackIsoOfIsPullback (IsPullback.of_hasPullback curve.carrier.hom fieldMap)
            parameter).hom).obj lineBundle)) := by
  rw [baseChangeIso_app]
  have inclusion : (picardFunctorDegreeι
      ((Curve.baseChange baseField extensionField).obj curve).carrier.hom 0).hom.app
      (.op parameter)
      ((picardFunctorDegreeIsoOfIsPullback
        (extendedMap := ((Curve.baseChange baseField extensionField).obj curve).carrier.hom)
        (IsPullback.of_hasPullback curve.carrier.hom fieldMap) 0).hom.app (.op parameter)
        (sourceRepresentation.homEquiv (baseChangeHomMulEquiv sourceGroup parameter point))) =
      (picardFunctorIsoOfIsPullback
        (f' := ((Curve.baseChange baseField extensionField).obj curve).carrier.hom)
        (IsPullback.of_hasPullback curve.carrier.hom fieldMap)).hom.app (.op parameter)
        ((picardFunctorDegreeι curve.carrier.hom 0).hom.app
          (.op ((Over.map fieldMap).obj parameter))
          (sourceRepresentation.homEquiv (baseChangeHomMulEquiv sourceGroup parameter point))) := by
    simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply,
      CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.op_obj] using
      ConcreteCategory.congr_hom
        (NatTrans.congr_app (picardFunctorDegreeIsoOfIsPullback_inclusion
          (extendedMap := ((Curve.baseChange baseField extensionField).obj curve).carrier.hom)
          (IsPullback.of_hasPullback curve.carrier.hom fieldMap) 0) (.op parameter))
            (sourceRepresentation.homEquiv (baseChangeHomMulEquiv sourceGroup parameter point))
  rw [inclusion, classifies]
  simpa only [CategoryTheory.Functor.op_obj, Scheme.Pic.map_mk] using
    picardFunctorIsoOfIsPullback_hom_app_toPicardFunctor
      (f' := ((Curve.baseChange baseField extensionField).obj curve).carrier.hom)
      (IsPullback.of_hasPullback curve.carrier.hom fieldMap) (.op parameter)
      (Scheme.Pic.mk lineBundle)

end PicardTensorCompatible

/-- Morphisms out of a base-changed Picard representation are determined by their
action on actual bundle families. The target may represent a different curve. -/
theorem picardBaseChange_hom_ext {targetCurve : Curve extensionField}
    {targetGroup : CommGrp (Over (Spec (.of extensionField)))}
    (targetRepresentation : (picardFunctorDegree targetCurve.carrier.hom 0).obj.RepresentableBy
      targetGroup.X)
    (firstMorphism secondMorphism :
      (baseChange baseField extensionField).obj sourceGroup.X ⟶ targetGroup.X)
    (agreement : ∀ (parameter : Over (Spec (.of extensionField)))
      (point : parameter ⟶ (baseChange baseField extensionField).obj sourceGroup.X)
      (lineBundle : (pullback curve.carrier.hom ((Over.map fieldMap).obj parameter).hom).Modules)
      [lineBundle.IsInvertible],
      (picardFunctorDegreeι curve.carrier.hom 0).hom.app
          (.op ((Over.map fieldMap).obj parameter))
          (sourceRepresentation.homEquiv (baseChangeHomMulEquiv sourceGroup parameter point)) =
        (toPicardFunctor curve.carrier.hom).app _ (Scheme.Pic.mk lineBundle) →
      (picardFunctorDegreeι targetCurve.carrier.hom 0).hom.app (.op parameter)
          (targetRepresentation.homEquiv (point ≫ firstMorphism)) =
        (picardFunctorDegreeι targetCurve.carrier.hom 0).hom.app (.op parameter)
          (targetRepresentation.homEquiv (point ≫ secondMorphism))) :
    firstMorphism = secondMorphism := by
  apply targetRepresentation.homEquiv.injective
  let baseMap : Spec (.of extensionField) ⟶ Spec (.of baseField) := fieldMap
  let topology := Scheme.fppfTopology.over (Spec (.of extensionField))
  let extendedRepresentation := representationOnExtendedTests
    (extensionField := extensionField) sourceRepresentation
  let presentation := CategoryTheory.Functor.whiskerLeft (Over.map baseMap).op
    (toSheafify (Scheme.fppfTopology.over (Spec (.of baseField)))
      (picardSubfunctorDegree curve.carrier.hom 0).toFunctor)
  haveI : Presheaf.IsLocallySurjective topology presentation :=
    Presheaf.isLocallySurjective_whisker topology
      (Scheme.fppfTopology.over (Spec (.of baseField))) (Over.map baseMap)
      (toSheafify (Scheme.fppfTopology.over (Spec (.of baseField)))
        (picardSubfunctorDegree curve.carrier.hom 0).toFunctor)
  let coveringSieve := Presheaf.imageSieve presentation
    (extendedRepresentation.homEquiv (𝟙 _))
  have covering : coveringSieve ∈ topology
      ((baseChange baseField extensionField).obj sourceGroup.X) :=
    Presheaf.imageSieve_mem topology presentation (extendedRepresentation.homEquiv (𝟙 _))
  apply (((isSheaf_iff_isSheaf_of_type topology _).1
    (picardFunctorDegree targetCurve.carrier.hom 0).property).isSeparated
      coveringSieve covering).ext
  rintro cover restriction ⟨localLift, localEquality⟩
  let localClass : picardDegreeZeroSubgroup curve.carrier.hom
    ((Over.map baseMap).obj cover) := localLift
  obtain ⟨lineBundle, invertible, representative⟩ := Scheme.Pic.exists_mk_eq localClass.val
  letI := invertible
  have localCorrespondence : sourceRepresentation.homEquiv
      (baseChangeHomMulEquiv sourceGroup cover restriction) =
        presentation.app (.op cover) localLift := by
    change extendedRepresentation.homEquiv restriction = _
    have naturality := extendedRepresentation.homEquiv_comp restriction (𝟙 _)
    rw [Category.comp_id] at naturality
    exact naturality.trans localEquality.symm
  have localClassifies : (picardFunctorDegreeι curve.carrier.hom 0).hom.app
      (.op ((Over.map baseMap).obj cover))
      (sourceRepresentation.homEquiv (baseChangeHomMulEquiv sourceGroup cover restriction)) =
        (toPicardFunctor curve.carrier.hom).app _ (Scheme.Pic.mk lineBundle) := by
    rw [localCorrespondence]
    calc
      _ = (toPicardFunctor curve.carrier.hom).app _ localClass.val :=
        picardFunctorDegreeι_app_toSheafify curve.carrier.hom 0 localClass
      _ = (toPicardFunctor curve.carrier.hom).app _ (Scheme.Pic.mk lineBundle) :=
        congrArg ((toPicardFunctor curve.carrier.hom).app _) representative.symm
  rw [← targetRepresentation.homEquiv_comp, ← targetRepresentation.homEquiv_comp]
  apply injective_picardFunctorDegreeι_app targetCurve.carrier.hom 0 cover
  exact agreement cover restriction lineBundle localClassifies

namespace PicardTensorCompatible

variable {curve sourceRepresentation extendedRepresentation}
  (sourceCompatibility : PicardTensorCompatible curve.carrier.hom sourceGroup
    sourceRepresentation)
  (extendedCompatibility : PicardTensorCompatible
    ((Curve.baseChange baseField extensionField).obj curve).carrier.hom extendedGroup
      extendedRepresentation)

/-- The bundle-class formula uniquely characterizes the represented group comparison. -/
theorem baseChangeIso_unique
    (candidate : (baseChange baseField extensionField).mapCommGrp.obj sourceGroup ≅ extendedGroup)
    (action : ∀ (parameter : Over (Spec (.of extensionField)))
      (point : parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj sourceGroup).X)
      (lineBundle : (pullback curve.carrier.hom ((Over.map fieldMap).obj parameter).hom).Modules)
      [lineBundle.IsInvertible],
      (picardFunctorDegreeι curve.carrier.hom 0).hom.app
          (.op ((Over.map fieldMap).obj parameter))
          (sourceRepresentation.homEquiv (baseChangeHomMulEquiv sourceGroup parameter point)) =
        (toPicardFunctor curve.carrier.hom).app _ (Scheme.Pic.mk lineBundle) →
      (picardFunctorDegreeι
          ((Curve.baseChange baseField extensionField).obj curve).carrier.hom 0).hom.app
          (.op parameter) (extendedRepresentation.homEquiv
            (point ≫ candidate.hom.hom.hom.hom)) =
        (toPicardFunctor ((Curve.baseChange baseField extensionField).obj curve).carrier.hom).app
          (.op parameter) (Scheme.Pic.mk ((Scheme.Modules.pullback
            (pullbackIsoOfIsPullback (IsPullback.of_hasPullback curve.carrier.hom fieldMap)
              parameter).hom).obj lineBundle))) :
    candidate = baseChangeIso sourceCompatibility extendedCompatibility := by
  apply Iso.ext
  apply CommGrp.hom_ext
  apply picardBaseChange_hom_ext curve sourceRepresentation extendedRepresentation
  intro parameter point lineBundle invertible classifies
  exact (action parameter point lineBundle classifies).trans
    (baseChangeIso_class sourceCompatibility extendedCompatibility parameter point lineBundle
      classifies).symm

end PicardTensorCompatible

end AlgebraicGeometry
