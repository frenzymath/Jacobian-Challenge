import Jacobian.AlgebraicGeometry.Picard.FieldExtensionNaturality
import Jacobian.AlgebraicGeometry.Curve.BaseChange

/-!
# Identity extension of represented Picard groups

Extension along the identity of a field, followed by pullback along the canonical
curve comparison, is the canonical identity comparison of group schemes. The
proof compares Picard classes of families over arbitrary test schemes.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

attribute [local irreducible] baseChange.idIso Curve.baseChange.idIso
  PicardTensorCompatible.baseChangeIso PicardTensorCompatible.representedPullback

private abbrev identityFieldMap (baseField : Type u) [Field baseField] :=
  Spec.map (CommRingCat.ofHom (algebraMap baseField baseField))

private theorem inverse_eq_of_mapIso_eq
    {sourceCategory targetCategory : Type*} [Category sourceCategory] [Category targetCategory]
    (forget : sourceCategory ⥤ targetCategory) {source target : sourceCategory}
    (comparison : source ≅ target) (underlying : forget.obj source ≅ forget.obj target)
    (equation : forget.mapIso comparison = underlying) :
    forget.map comparison.inv = underlying.inv := by
  exact congrArg (fun isomorphism : forget.obj source ≅ forget.obj target ↦ isomorphism.inv)
    equation

private theorem identityFamilyMap {baseField : Type u} [Field baseField]
    (source : Over (Spec (.of baseField)))
    (comparison : (baseChange baseField baseField).obj source ≅ source)
    (projection : comparison.inv.left ≫
      pullback.fst source.hom (identityFieldMap baseField) = 𝟙 source.left)
    (parameter : Over (Spec (.of baseField))) :
    picardFamilyMap comparison.inv parameter ≫
        (pullbackIsoOfIsPullback
          (IsPullback.of_hasPullback source.hom (identityFieldMap baseField)) parameter).hom =
      baseChangeMap source.hom (baseChange.restrictionId baseField parameter) := by
  apply pullback.hom_ext
  · simp only [picardFamilyMap, baseChangeMap, Category.assoc,
      Over.pullback_obj_hom, Over.map_obj_hom,
      pullbackIsoOfIsPullback_hom_fst, pullbackIsoOfIsPullback_hom_fst_assoc,
      pullback.lift_fst, pullback.lift_fst_assoc]
    simpa only [Category.assoc, Category.comp_id] using
      congrArg (fun morphism ↦ pullback.fst source.hom parameter.hom ≫ morphism) projection
  · simp only [picardFamilyMap, baseChangeMap, baseChange.restrictionId,
      Over.pullback_obj_hom, Over.map_obj_hom, Over.homMk, CostructuredArrow.homMk_left,
      Category.assoc, pullbackIsoOfIsPullback_hom_snd, pullbackIsoOfIsPullback_hom_snd_assoc,
      pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]

private theorem picardMap_comp_of_eq {source middle target : Scheme.{u}}
    {firstMap : source ⟶ middle} {secondMap : middle ⟶ target}
    {directMap : source ⟶ target} (equation : firstMap ≫ secondMap = directMap)
    (picardClass : target.Pic) :
    Scheme.Pic.map firstMap (Scheme.Pic.map secondMap picardClass) =
      Scheme.Pic.map directMap picardClass := by
  exact (Scheme.Pic.map_comp firstMap secondMap picardClass).symm.trans
    (congrArg (fun morphism ↦ Scheme.Pic.map morphism picardClass) equation)

private theorem identityFamilyClass {baseField : Type u} [Field baseField]
    (curve : Curve baseField) (parameter : Over (Spec (.of baseField)))
    (picardClass : (pullback curve.carrier.hom
      ((Over.map (identityFieldMap baseField)).obj parameter).hom).Pic) :
    Scheme.Pic.map
        (picardFamilyMap ((Curve.baseChange.idIso baseField).app curve).inv parameter)
        (Scheme.Pic.map
          (pullbackIsoOfIsPullback
            (IsPullback.of_hasPullback curve.carrier.hom (identityFieldMap baseField))
            parameter).hom picardClass) =
      Scheme.Pic.map
        (baseChangeMap curve.carrier.hom (baseChange.restrictionId baseField parameter))
        picardClass := by
  have inverseComponent := inverse_eq_of_mapIso_eq (Curve.forget baseField)
    ((Curve.baseChange.idIso baseField).app curve)
    ((baseChange.idIso baseField).app curve.carrier)
    (Curve.forget_mapIso_baseChange_idIso_app baseField curve)
  change ((Curve.baseChange.idIso baseField).app curve).inv =
    ((baseChange.idIso baseField).app curve.carrier).inv at inverseComponent
  rw [inverseComponent]
  have projection := congrArg
    (fun morphism : curve.carrier ⟶ curve.carrier ↦ morphism.left)
    (((baseChange.idIso baseField).app curve.carrier).inv_hom_id)
  change ((baseChange.idIso baseField).app curve.carrier).inv.left ≫
    ((baseChange.idIso baseField).app curve.carrier).hom.left = 𝟙 curve.carrier.left at projection
  rw [baseChange.idIso_hom_app_left] at projection
  have square := identityFamilyMap curve.carrier
    ((baseChange.idIso baseField).app curve.carrier) projection parameter
  exact picardMap_comp_of_eq square picardClass

private def classifiesPicardClass {baseField : Type u} [Field baseField]
    {curve : Curve baseField} {group : CommGrp (Over (Spec (.of baseField)))}
    (representation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy group.X)
    {parameter : Over (Spec (.of baseField))} (point : parameter ⟶ group.X)
    (picardClass : (pullback curve.carrier.hom parameter.hom).Pic) : Prop :=
  (picardFunctorDegreeι curve.carrier.hom 0).hom.app (.op parameter)
      (representation.homEquiv point) =
    (toPicardFunctor curve.carrier.hom).app (.op parameter) picardClass

private theorem classifiesPicardClass_restrict {baseField : Type u} [Field baseField]
    {curve : Curve baseField} {group : CommGrp (Over (Spec (.of baseField)))}
    (representation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy group.X)
    {source target : Over (Spec (.of baseField))} (restriction : source ⟶ target)
    (point : target ⟶ group.X) (picardClass : (pullback curve.carrier.hom target.hom).Pic)
    (classifies : classifiesPicardClass representation point picardClass) :
    classifiesPicardClass representation (restriction ≫ point)
      (Scheme.Pic.map (baseChangeMap curve.carrier.hom restriction) picardClass) := by
  unfold classifiesPicardClass at classifies ⊢
  rw [representation.homEquiv_comp]
  have inclusionNaturality := ConcreteCategory.congr_hom
    ((picardFunctorDegreeι curve.carrier.hom 0).hom.naturality restriction.op)
    (representation.homEquiv point)
  have classNaturality := ConcreteCategory.congr_hom
    ((toPicardFunctor curve.carrier.hom).naturality restriction.op) picardClass
  simp only [ConcreteCategory.comp_apply] at inclusionNaturality classNaturality
  rw [inclusionNaturality, classifies]
  exact classNaturality.symm

private theorem picardClass_hom_ext {baseField : Type u} [Field baseField]
    (curve : Curve baseField) {group : CommGrp (Over (Spec (.of baseField)))}
    (representation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy group.X)
    (firstMap secondMap : (baseChange baseField baseField).obj group.X ⟶ group.X)
    (agreement : ∀ (parameter : Over (Spec (.of baseField)))
      (point : parameter ⟶ (baseChange baseField baseField).obj group.X)
      (picardClass : (pullback curve.carrier.hom
        ((Over.map (identityFieldMap baseField)).obj parameter).hom).Pic),
      classifiesPicardClass representation (baseChangeHomMulEquiv group parameter point)
        picardClass →
      (picardFunctorDegreeι curve.carrier.hom 0).hom.app (.op parameter)
          (representation.homEquiv (point ≫ firstMap)) =
        (picardFunctorDegreeι curve.carrier.hom 0).hom.app (.op parameter)
          (representation.homEquiv (point ≫ secondMap))) :
    firstMap = secondMap := by
  apply picardBaseChange_hom_ext curve representation representation
  intro parameter point lineBundle invertible classifies
  exact agreement parameter point (Scheme.Pic.mk lineBundle) classifies

private theorem representedPullback_picardClass {baseField : Type u} [Field baseField]
    {source target : Curve baseField}
    {sourceGroup targetGroup : CommGrp (Over (Spec (.of baseField)))}
    {sourceRepresentation : (picardFunctorDegree source.carrier.hom 0).obj.RepresentableBy
      sourceGroup.X}
    {targetRepresentation : (picardFunctorDegree target.carrier.hom 0).obj.RepresentableBy
      targetGroup.X}
    (sourceCompatibility : PicardTensorCompatible source.carrier.hom sourceGroup
      sourceRepresentation)
    (targetCompatibility : PicardTensorCompatible target.carrier.hom targetGroup
      targetRepresentation)
    (morphism : source ⟶ target) (parameter : Over (Spec (.of baseField)))
    (point : parameter ⟶ targetGroup.X)
    (picardClass : (pullback target.carrier.hom parameter.hom).Pic)
    (classifies : classifiesPicardClass targetRepresentation point picardClass) :
    classifiesPicardClass sourceRepresentation
      (point ≫ (PicardTensorCompatible.representedPullback sourceCompatibility
        targetCompatibility morphism).hom.hom.hom)
      (Scheme.Pic.map (picardFamilyMap morphism parameter) picardClass) := by
  unfold classifiesPicardClass at classifies ⊢
  rw [PicardTensorCompatible.representedPullback_app]
  have inclusionSquare := congr_app
    (congrArg (fun transformation : picardFunctorDegree target.carrier.hom 0 ⟶
      picardFunctor source.carrier.hom ↦ transformation.hom)
        (picardDegreeZeroFunctorPullback_inclusion morphism)) (.op parameter)
  have evaluatedSquare := ConcreteCategory.congr_hom inclusionSquare
    (targetRepresentation.homEquiv point)
  change (picardFunctorDegreeι source.carrier.hom 0).hom.app (.op parameter)
      ((picardDegreeZeroFunctorPullback morphism).hom.app (.op parameter)
        (targetRepresentation.homEquiv point)) =
    (picardFunctorPullback morphism).hom.app (.op parameter)
      ((picardFunctorDegreeι target.carrier.hom 0).hom.app (.op parameter)
        (targetRepresentation.homEquiv point)) at evaluatedSquare
  change (picardFunctorDegreeι source.carrier.hom 0).hom.app (.op parameter)
      ((picardDegreeZeroFunctorPullback morphism).hom.app (.op parameter)
        (targetRepresentation.homEquiv point)) = _
  rw [evaluatedSquare, classifies, picardFunctorPullback_toPicardFunctor]

private theorem mapCommGrp_identity_of_underlying
    {category : Type*} [Category category] [CartesianMonoidalCategory category]
    [BraidedCategory category] (extensionFunctor : category ⥤ category)
    [extensionFunctor.Braided] (comparison : extensionFunctor ≅ 𝟭 category)
    {group extendedGroup : CommGrp category}
    (extension : extensionFunctor.mapCommGrp.obj group ⟶ extendedGroup)
    (returnMap : extendedGroup ⟶ group)
    (underlying : extension.hom.hom.hom ≫ returnMap.hom.hom.hom =
      (comparison.app group.X).hom) :
    extension ≫ returnMap =
      (Functor.mapCommGrpNatIso comparison).hom.app group ≫
        (Functor.mapCommGrpIdIso (C := category)).hom.app group := by
  apply CommGrp.hom_ext
  change extension.hom.hom.hom ≫ returnMap.hom.hom.hom =
    (comparison.app group.X).hom ≫ 𝟙 group.X
  exact underlying.trans (Category.comp_id _).symm

private theorem hom_comp_eq_of_class_observations
    {category : Type*} [Category category] {source middle target : category}
    {classes : category → Type*} {result : category → Sort*}
    (observe : ∀ parameter, (parameter ⟶ target) → result parameter)
    (classifies : ∀ parameter, (parameter ⟶ source) → classes parameter → Prop)
    (separates : ∀ firstMap secondMap : source ⟶ target,
      (∀ parameter point picardClass, classifies parameter point picardClass →
        observe parameter (point ≫ firstMap) = observe parameter (point ≫ secondMap)) →
      firstMap = secondMap)
    (firstMap : source ⟶ middle) (secondMap : middle ⟶ target)
    (canonicalMap : source ⟶ target)
    (agreement : ∀ parameter point picardClass, classifies parameter point picardClass →
      observe parameter ((point ≫ firstMap) ≫ secondMap) =
        observe parameter (point ≫ canonicalMap)) :
    firstMap ≫ secondMap = canonicalMap := by
  apply separates
  intro parameter point picardClass classified
  simpa only [Category.assoc] using agreement parameter point picardClass classified

namespace PicardTensorCompatible

variable {baseField : Type u} [Field baseField] {curve : Curve baseField}
  {group extendedGroup : CommGrp (Over (Spec (.of baseField)))}
  {representation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy group.X}
  {extendedRepresentation : (picardFunctorDegree
    ((Curve.baseChange baseField baseField).obj curve).carrier.hom 0).obj.RepresentableBy
      extendedGroup.X}

private theorem baseChange_identity_of_classes
    (comparison : baseChange baseField baseField ≅ 𝟭 (Over (Spec (.of baseField))))
    (adjunction : ∀ (parameter : Over (Spec (.of baseField)))
      (point : parameter ⟶ ((baseChange baseField baseField).mapCommGrp.obj group).X),
      point ≫ (comparison.app group.X).hom =
        baseChange.restrictionId baseField parameter ≫
          baseChangeHomMulEquiv group parameter point)
    (extension : (baseChange baseField baseField).mapCommGrp.obj group ⟶ extendedGroup)
    (returnMap : extendedGroup ⟶ group)
    (extensionClassifies : ∀ (parameter : Over (Spec (.of baseField)))
      (point : parameter ⟶ ((baseChange baseField baseField).mapCommGrp.obj group).X)
      (picardClass : (pullback curve.carrier.hom
        ((Over.map (identityFieldMap baseField)).obj parameter).hom).Pic),
      classifiesPicardClass representation (baseChangeHomMulEquiv group parameter point)
        picardClass →
      classifiesPicardClass extendedRepresentation (point ≫ extension.hom.hom.hom)
        (Scheme.Pic.map (pullbackIsoOfIsPullback
          (IsPullback.of_hasPullback curve.carrier.hom (identityFieldMap baseField))
          parameter).hom picardClass))
    (returnClassifies : ∀ (parameter : Over (Spec (.of baseField)))
      (point : parameter ⟶ extendedGroup.X)
      (picardClass : (pullback
        ((Curve.baseChange baseField baseField).obj curve).carrier.hom parameter.hom).Pic),
      classifiesPicardClass extendedRepresentation point picardClass →
      classifiesPicardClass representation (point ≫ returnMap.hom.hom.hom)
        (Scheme.Pic.map
          (picardFamilyMap ((Curve.baseChange.idIso baseField).app curve).inv parameter)
          picardClass)) :
    extension ≫ returnMap =
      (Functor.mapCommGrpNatIso comparison).hom.app group ≫
        (Functor.mapCommGrpIdIso (C := Over (Spec (.of baseField)))).hom.app group := by
  apply mapCommGrp_identity_of_underlying (baseChange baseField baseField) comparison
  exact hom_comp_eq_of_class_observations
    (fun parameter morphism ↦
      (picardFunctorDegreeι curve.carrier.hom 0).hom.app (.op parameter)
        (representation.homEquiv morphism))
    (fun parameter point picardClass ↦ classifiesPicardClass representation
      (baseChangeHomMulEquiv group parameter point) picardClass)
    (picardClass_hom_ext curve representation)
    extension.hom.hom.hom returnMap.hom.hom.hom (comparison.app group.X).hom
    (by
      intro parameter point picardClass classifies
      have extendedClass := extensionClassifies parameter point picardClass classifies
      have returnedClass := returnClassifies parameter (point ≫ extension.hom.hom.hom)
        _ extendedClass
      have canonicalClass := classifiesPicardClass_restrict representation
        (baseChange.restrictionId baseField parameter)
        (baseChangeHomMulEquiv group parameter point) picardClass classifies
      unfold classifiesPicardClass at returnedClass canonicalClass
      rw [returnedClass, identityFamilyClass, adjunction]
      exact canonicalClass.symm)

/-- Identity field extension, followed by the inverse curve comparison, is the
canonical identity comparison of represented Picard group schemes. -/
theorem baseChangeIso_id
    (compatibility : PicardTensorCompatible curve.carrier.hom group representation)
    (extendedCompatibility : PicardTensorCompatible
      ((Curve.baseChange baseField baseField).obj curve).carrier.hom extendedGroup
      extendedRepresentation) :
    (baseChangeIso compatibility extendedCompatibility).hom ≫
        representedPullback compatibility extendedCompatibility
          ((Curve.baseChange.idIso baseField).app curve).inv =
      ((Functor.mapCommGrpNatIso (baseChange.idIso baseField)).app group ≪≫
        (Functor.mapCommGrpIdIso (C := Over (Spec (.of baseField)))).app group).hom := by
  exact baseChange_identity_of_classes
    (representation := representation) (extendedRepresentation := extendedRepresentation)
    (baseChange.idIso baseField) (baseChangeHomMulEquiv_id group)
    (baseChangeIso compatibility extendedCompatibility).hom
    (representedPullback compatibility extendedCompatibility
      ((Curve.baseChange.idIso baseField).app curve).inv)
    (by
      intro parameter point picardClass classifies
      obtain ⟨lineBundle, invertible, rfl⟩ := Scheme.Pic.exists_mk_eq picardClass
      letI := invertible
      simpa only [classifiesPicardClass, Scheme.Pic.map_mk] using
        baseChangeIso_class compatibility extendedCompatibility parameter point lineBundle
          classifies)
    (by
      intro parameter point picardClass classifies
      exact representedPullback_picardClass compatibility extendedCompatibility
        ((Curve.baseChange.idIso baseField).app curve).inv parameter point picardClass classifies)

end PicardTensorCompatible

end AlgebraicGeometry
