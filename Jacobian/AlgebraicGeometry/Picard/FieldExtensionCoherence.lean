import Jacobian.AlgebraicGeometry.Picard.FieldExtensionNaturality
import Jacobian.AlgebraicGeometry.Curve.BaseChange

/-!
# Tower coherence for represented Picard field extension

Direct and iterated extension of scalars induce the same morphism between
tensor-compatible representations of the degree-zero Picard sheaves, after the
canonical comparisons of curves and group schemes. The proof compares actual
line-bundle families through their Cartesian pullback maps.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

attribute [local irreducible] baseChange.compIso Curve.baseChange.compIso
  PicardTensorCompatible.baseChangeIso PicardTensorCompatible.representedPullback

private abbrev fieldMap (baseField extensionField : Type u)
    [Field baseField] [Field extensionField] [Algebra baseField extensionField] :=
  Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))

private abbrev familyMap {baseField extensionField : Type u}
    [Field baseField] [Field extensionField] [Algebra baseField extensionField]
    (curve : Curve baseField) (parameter : Over (Spec (.of extensionField))) :=
  (pullbackIsoOfIsPullback
    (IsPullback.of_hasPullback curve.carrier.hom (fieldMap baseField extensionField))
    parameter).hom

private theorem familyMap_composite (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField] [IsScalarTower baseField middleField extensionField]
    (source : Over (Spec (.of baseField))) (parameter : Over (Spec (.of extensionField)))
    (comparison : (baseChange baseField extensionField).obj source ≅
      (baseChange middleField extensionField).obj ((baseChange baseField middleField).obj source))
    (projection : comparison.inv.left ≫
      pullback.fst source.hom (fieldMap baseField extensionField) =
        pullback.fst (pullback.snd source.hom (fieldMap baseField middleField))
            (fieldMap middleField extensionField) ≫
          pullback.fst source.hom (fieldMap baseField middleField)) :
    picardFamilyMap comparison.inv parameter ≫
        (pullbackIsoOfIsPullback
          (IsPullback.of_hasPullback source.hom (fieldMap baseField extensionField)) parameter).hom =
      (pullbackIsoOfIsPullback (IsPullback.of_hasPullback
        ((baseChange baseField middleField).obj source).hom (fieldMap middleField extensionField))
          parameter).hom ≫
        (pullbackIsoOfIsPullback
          (IsPullback.of_hasPullback source.hom (fieldMap baseField middleField))
            ((Over.map (fieldMap middleField extensionField)).obj parameter)).hom ≫
          baseChangeMap source.hom
            (baseChange.restrictionComp baseField middleField extensionField parameter) := by
  have firstFst := pullbackIsoOfIsPullback_hom_fst
    (IsPullback.of_hasPullback ((baseChange baseField middleField).obj source).hom
      (fieldMap middleField extensionField)) parameter
  have secondFst := pullbackIsoOfIsPullback_hom_fst
    (IsPullback.of_hasPullback source.hom (fieldMap baseField middleField))
      ((Over.map (fieldMap middleField extensionField)).obj parameter)
  have firstSnd := pullbackIsoOfIsPullback_hom_snd
    (IsPullback.of_hasPullback ((baseChange baseField middleField).obj source).hom
      (fieldMap middleField extensionField)) parameter
  have secondSnd := pullbackIsoOfIsPullback_hom_snd
    (IsPullback.of_hasPullback source.hom (fieldMap baseField middleField))
      ((Over.map (fieldMap middleField extensionField)).obj parameter)
  have firstFstWithTail := congrArg
    (fun morphism ↦ morphism ≫ pullback.fst source.hom (fieldMap baseField middleField)) firstFst
  simp only [Category.assoc] at firstFstWithTail
  apply pullback.hom_ext
  · simp only [picardFamilyMap, baseChangeMap, Category.assoc,
      Over.pullback_obj_hom, Over.map_obj_hom,
      pullbackIsoOfIsPullback_hom_fst, pullbackIsoOfIsPullback_hom_fst_assoc,
      pullback.lift_fst, pullback.lift_fst_assoc]
    erw [secondFst, firstFstWithTail]
    simpa only [Category.assoc, Over.pullback_obj_hom] using
      congrArg (fun morphism ↦ pullback.fst
        ((baseChange middleField extensionField).obj
          ((baseChange baseField middleField).obj source)).hom parameter.hom ≫ morphism) projection
  · simp only [picardFamilyMap, baseChangeMap, baseChange.restrictionComp,
      Over.pullback_obj_hom, Over.map_obj_hom, Over.homMk, CostructuredArrow.homMk_left,
      Category.assoc, pullbackIsoOfIsPullback_hom_snd, pullbackIsoOfIsPullback_hom_snd_assoc,
      pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
    erw [Category.comp_id, secondSnd, firstSnd]
    rfl

private theorem inverse_projection {source target base : Scheme.{u}}
    (comparison : source ≅ target) (firstProjection : source ⟶ base)
    (secondProjection : target ⟶ base)
    (projection : comparison.hom ≫ secondProjection = firstProjection) :
    comparison.inv ≫ firstProjection = secondProjection := by
  calc
    _ = comparison.inv ≫ (comparison.hom ≫ secondProjection) :=
      congrArg (fun morphism ↦ comparison.inv ≫ morphism) projection.symm
    _ = _ := by rw [← Category.assoc, comparison.inv_hom_id, Category.id_comp]

private theorem familyMap_comp_over (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField] [IsScalarTower baseField middleField extensionField]
    (source : Over (Spec (.of baseField))) (parameter : Over (Spec (.of extensionField))) :
    picardFamilyMap
        ((baseChange.compIso baseField middleField extensionField).app source).inv parameter ≫
        (pullbackIsoOfIsPullback
          (IsPullback.of_hasPullback source.hom (fieldMap baseField extensionField)) parameter).hom =
      (pullbackIsoOfIsPullback (IsPullback.of_hasPullback
        ((baseChange baseField middleField).obj source).hom (fieldMap middleField extensionField))
          parameter).hom ≫
        (pullbackIsoOfIsPullback
          (IsPullback.of_hasPullback source.hom (fieldMap baseField middleField))
            ((Over.map (fieldMap middleField extensionField)).obj parameter)).hom ≫
          baseChangeMap source.hom
            (baseChange.restrictionComp baseField middleField extensionField parameter) := by
  apply familyMap_composite baseField middleField extensionField source parameter
    ((baseChange.compIso baseField middleField extensionField).app source)
  exact inverse_projection
    ((Over.forget (Spec (.of extensionField))).mapIso
      ((baseChange.compIso baseField middleField extensionField).app source))
    _ _ (baseChange.compIso_hom_app_left_fst_fst baseField middleField extensionField source)

private theorem picardMap_comp_of_eq
    {source firstMiddle secondMiddle thirdMiddle target : Scheme.{u}}
    {firstMorphism : source ⟶ firstMiddle} {secondMorphism : firstMiddle ⟶ target}
    {thirdMorphism : source ⟶ secondMiddle} {fourthMorphism : secondMiddle ⟶ thirdMiddle}
    {fifthMorphism : thirdMiddle ⟶ target}
    (equation : firstMorphism ≫ secondMorphism = thirdMorphism ≫ fourthMorphism ≫ fifthMorphism)
    (picardClass : target.Pic) :
    Scheme.Pic.map firstMorphism (Scheme.Pic.map secondMorphism picardClass) =
      Scheme.Pic.map thirdMorphism
        (Scheme.Pic.map fourthMorphism (Scheme.Pic.map fifthMorphism picardClass)) := by
  calc
    _ = Scheme.Pic.map (firstMorphism ≫ secondMorphism) picardClass :=
      (Scheme.Pic.map_comp firstMorphism secondMorphism picardClass).symm
    _ = Scheme.Pic.map (thirdMorphism ≫ fourthMorphism ≫ fifthMorphism) picardClass :=
      congrArg (fun morphism ↦ Scheme.Pic.map morphism picardClass) equation
    _ = _ := by rw [Scheme.Pic.map_comp, Scheme.Pic.map_comp]

private theorem familyClass_comp (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField] [IsScalarTower baseField middleField extensionField]
    (curve : Curve baseField) (parameter : Over (Spec (.of extensionField)))
    (picardClass : (pullback curve.carrier.hom
      ((Over.map (fieldMap baseField extensionField)).obj parameter).hom).Pic) :
    Scheme.Pic.map
      (picardFamilyMap
        ((Curve.baseChange.compIso baseField middleField extensionField).app curve).inv
          parameter) (Scheme.Pic.map (familyMap curve parameter) picardClass) =
      Scheme.Pic.map (familyMap ((Curve.baseChange baseField middleField).obj curve) parameter)
        (Scheme.Pic.map
          (familyMap curve ((Over.map (fieldMap middleField extensionField)).obj parameter))
          (Scheme.Pic.map (baseChangeMap curve.carrier.hom
            (baseChange.restrictionComp baseField middleField extensionField parameter))
            picardClass)) := by
  rw [Curve.baseChange_compIso_inv_app]
  exact picardMap_comp_of_eq
    (familyMap_comp_over baseField middleField extensionField curve.carrier parameter) picardClass

private theorem observation_comp {category : Type*} [Category category]
    {parameter source direct firstMiddle secondMiddle target : category} {result : Sort*}
    (observe : (parameter ⟶ target) → result) (point : parameter ⟶ source)
    (directMap : source ⟶ direct) (returnMap : direct ⟶ target)
    (canonicalMap : source ⟶ firstMiddle) (middleMap : firstMiddle ⟶ secondMiddle)
    (finalMap : secondMiddle ⟶ target)
    (comparison : observe ((point ≫ directMap) ≫ returnMap) =
      observe (((point ≫ canonicalMap) ≫ middleMap) ≫ finalMap)) :
    observe (point ≫ directMap ≫ returnMap) =
      observe (point ≫ canonicalMap ≫ middleMap ≫ finalMap) := by
  simpa only [Category.assoc] using comparison

private theorem hom_comp_eq_of_class_observations
    {category : Type*} [Category category]
    {source direct firstMiddle secondMiddle target : category}
    {classes : category → Type*} {result : category → Sort*}
    (observe : ∀ parameter, (parameter ⟶ target) → result parameter)
    (classifies : ∀ parameter, (parameter ⟶ source) → classes parameter → Prop)
    (separates : ∀ firstMorphism secondMorphism : source ⟶ target,
      (∀ parameter point picardClass, classifies parameter point picardClass →
        observe parameter (point ≫ firstMorphism) =
          observe parameter (point ≫ secondMorphism)) → firstMorphism = secondMorphism)
    (directMap : source ⟶ direct) (returnMap : direct ⟶ target)
    (canonicalMap : source ⟶ firstMiddle) (middleMap : firstMiddle ⟶ secondMiddle)
    (finalMap : secondMiddle ⟶ target)
    (agreement : ∀ parameter point picardClass, classifies parameter point picardClass →
      observe parameter ((point ≫ directMap) ≫ returnMap) =
        observe parameter (((point ≫ canonicalMap) ≫ middleMap) ≫ finalMap)) :
    directMap ≫ returnMap = canonicalMap ≫ middleMap ≫ finalMap := by
  apply separates
  intro parameter point picardClass classified
  exact observation_comp (observe parameter) point directMap returnMap canonicalMap middleMap
    finalMap (agreement parameter point picardClass classified)

private theorem mapCommGrp_comp_of_underlying
    {sourceCategory middleCategory targetCategory : Type*}
    [Category sourceCategory] [CartesianMonoidalCategory sourceCategory]
    [BraidedCategory sourceCategory]
    [Category middleCategory] [CartesianMonoidalCategory middleCategory]
    [BraidedCategory middleCategory]
    [Category targetCategory] [CartesianMonoidalCategory targetCategory]
    [BraidedCategory targetCategory]
    (firstFunctor : sourceCategory ⥤ middleCategory) [firstFunctor.Braided]
    (finalFunctor : middleCategory ⥤ targetCategory) [finalFunctor.Braided]
    (directFunctor : sourceCategory ⥤ targetCategory) [directFunctor.Braided]
    (comparison : directFunctor ≅ firstFunctor ⋙ finalFunctor)
    {sourceGroup : CommGrp sourceCategory} {middleGroup : CommGrp middleCategory}
    {directGroup finalGroup : CommGrp targetCategory}
    (firstMap : firstFunctor.mapCommGrp.obj sourceGroup ⟶ middleGroup)
    (finalMap : finalFunctor.mapCommGrp.obj middleGroup ⟶ finalGroup)
    (directMap : directFunctor.mapCommGrp.obj sourceGroup ⟶ directGroup)
    (returnMap : directGroup ⟶ finalGroup)
    (underlying : directMap.hom.hom.hom ≫ returnMap.hom.hom.hom =
      (comparison.app sourceGroup.X).hom ≫ finalFunctor.map firstMap.hom.hom.hom ≫
        finalMap.hom.hom.hom) :
    directMap ≫ returnMap =
      (Functor.mapCommGrpNatIso comparison).hom.app sourceGroup ≫
      (Functor.mapCommGrpCompIso (F := firstFunctor) (G := finalFunctor)).hom.app sourceGroup ≫
      finalFunctor.mapCommGrp.map firstMap ≫ finalMap := by
  apply CommGrp.hom_ext
  change directMap.hom.hom.hom ≫ returnMap.hom.hom.hom =
    (comparison.app sourceGroup.X).hom ≫
      𝟙 (finalFunctor.obj (firstFunctor.obj sourceGroup.X)) ≫
      finalFunctor.map firstMap.hom.hom.hom ≫ finalMap.hom.hom.hom
  exact underlying.trans (congrArg
    (fun morphism : finalFunctor.obj (firstFunctor.obj sourceGroup.X) ⟶ finalGroup.X ↦
      (comparison.app sourceGroup.X).hom ≫ morphism)
    (CategoryTheory.Category.id_comp
      (finalFunctor.map firstMap.hom.hom.hom ≫ finalMap.hom.hom.hom))).symm

private theorem iterated_class_action
    {sourceCategory targetCategory : Type*}
    [Category sourceCategory] [Category targetCategory]
    (extensionFunctor : sourceCategory ⥤ targetCategory)
    {source middle restrictedParameter : sourceCategory}
    {parameter target : targetCategory}
    {sourceClasses middleClasses targetClasses : Type*}
    (sourceClassifies : (restrictedParameter ⟶ source) → sourceClasses → Prop)
    (middleClassifies : (restrictedParameter ⟶ middle) → middleClasses → Prop)
    (targetClassifies : (parameter ⟶ target) → targetClasses → Prop)
    (sourcePoint : (parameter ⟶ extensionFunctor.obj source) → (restrictedParameter ⟶ source))
    (middlePoint : (parameter ⟶ extensionFunctor.obj middle) → (restrictedParameter ⟶ middle))
    (firstMap : source ⟶ middle) (finalMap : extensionFunctor.obj middle ⟶ target)
    (firstFamily : sourceClasses → middleClasses) (finalFamily : middleClasses → targetClasses)
    (firstAction : ∀ point picardClass, sourceClassifies point picardClass →
      middleClassifies (point ≫ firstMap) (firstFamily picardClass))
    (finalAction : ∀ point picardClass, middleClassifies (middlePoint point) picardClass →
      targetClassifies (point ≫ finalMap) (finalFamily picardClass))
    (point : parameter ⟶ extensionFunctor.obj source) (picardClass : sourceClasses)
    (classifies : sourceClassifies (sourcePoint point) picardClass)
    (naturality : middlePoint (point ≫ extensionFunctor.map firstMap) =
      sourcePoint point ≫ firstMap) :
    targetClassifies ((point ≫ extensionFunctor.map firstMap) ≫ finalMap)
      (finalFamily (firstFamily picardClass)) := by
  apply finalAction
  rw [naturality]
  exact firstAction _ _ classifies

private theorem representedClass_restrict
    {baseField : Type u} [Field baseField] {curve : Curve baseField}
    {group : CommGrp (Over (Spec (.of baseField)))}
    (representation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy group.X)
    {source target : Over (Spec (.of baseField))} (restriction : source ⟶ target)
    (point : target ⟶ group.X)
    (picardClass : (pullback curve.carrier.hom target.hom).Pic)
    (classifies : (picardFunctorDegreeι curve.carrier.hom 0).hom.app (.op target)
      (representation.homEquiv point) =
        (toPicardFunctor curve.carrier.hom).app (.op target) picardClass) :
    (picardFunctorDegreeι curve.carrier.hom 0).hom.app (.op source)
      (representation.homEquiv (restriction ≫ point)) =
      (toPicardFunctor curve.carrier.hom).app (.op source)
        (Scheme.Pic.map (baseChangeMap curve.carrier.hom restriction) picardClass) := by
  rw [representation.homEquiv_comp]
  have inclusionNaturality := ConcreteCategory.congr_hom
    ((picardFunctorDegreeι curve.carrier.hom 0).hom.naturality restriction.op)
    (representation.homEquiv point)
  have classNaturality := ConcreteCategory.congr_hom
    ((toPicardFunctor curve.carrier.hom).naturality restriction.op) picardClass
  simp only [ConcreteCategory.comp_apply] at inclusionNaturality classNaturality
  rw [inclusionNaturality, classifies]
  exact classNaturality.symm

private def classifiesClass {field : Type u} [Field field] {curve : Curve field}
    {group : CommGrp (Over (Spec (.of field)))}
    (representation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy group.X)
    {parameter : Over (Spec (.of field))} (point : parameter ⟶ group.X)
    (picardClass : (pullback curve.carrier.hom parameter.hom).Pic) : Prop :=
  (picardFunctorDegreeι curve.carrier.hom 0).hom.app (.op parameter)
      (representation.homEquiv point) =
    (toPicardFunctor curve.carrier.hom).app (.op parameter) picardClass

private theorem picardClass_hom_ext {baseField extensionField : Type u}
    [Field baseField] [Field extensionField] [Algebra baseField extensionField]
    (curve : Curve baseField) (targetCurve : Curve extensionField)
    {group : CommGrp (Over (Spec (.of baseField)))}
    {targetGroup : CommGrp (Over (Spec (.of extensionField)))}
    (representation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy group.X)
    (targetRepresentation : (picardFunctorDegree targetCurve.carrier.hom 0).obj.RepresentableBy
      targetGroup.X)
    (firstMorphism secondMorphism :
      (baseChange baseField extensionField).obj group.X ⟶ targetGroup.X)
    (agreement : ∀ (parameter : Over (Spec (.of extensionField)))
      (point : parameter ⟶ (baseChange baseField extensionField).obj group.X)
      (picardClass : (pullback curve.carrier.hom
        ((Over.map (fieldMap baseField extensionField)).obj parameter).hom).Pic),
      classifiesClass representation (baseChangeHomMulEquiv group parameter point) picardClass →
        (picardFunctorDegreeι targetCurve.carrier.hom 0).hom.app (.op parameter)
            (targetRepresentation.homEquiv (point ≫ firstMorphism)) =
          (picardFunctorDegreeι targetCurve.carrier.hom 0).hom.app (.op parameter)
            (targetRepresentation.homEquiv (point ≫ secondMorphism))) :
    firstMorphism = secondMorphism := by
  apply picardBaseChange_hom_ext curve representation targetRepresentation
  intro parameter point lineBundle invertible classifies
  exact agreement parameter point (Scheme.Pic.mk lineBundle) classifies

private def extensionClassAction {baseField extensionField : Type u}
    [Field baseField] [Field extensionField] [Algebra baseField extensionField]
    {curve : Curve baseField}
    {group : CommGrp (Over (Spec (.of baseField)))}
    {extendedGroup : CommGrp (Over (Spec (.of extensionField)))}
    (representation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy group.X)
    (extendedRepresentation : (picardFunctorDegree
      ((Curve.baseChange baseField extensionField).obj curve).carrier.hom 0).obj.RepresentableBy
        extendedGroup.X)
    (comparison : (baseChange baseField extensionField).mapCommGrp.obj group ⟶ extendedGroup) :
    Prop :=
  ∀ (parameter : Over (Spec (.of extensionField)))
    (point : parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj group).X)
    (picardClass : (pullback curve.carrier.hom
      ((Over.map (fieldMap baseField extensionField)).obj parameter).hom).Pic),
    classifiesClass representation (baseChangeHomMulEquiv group parameter point) picardClass →
      classifiesClass extendedRepresentation (point ≫ comparison.hom.hom.hom)
        (Scheme.Pic.map (familyMap curve parameter) picardClass)

private def pullbackClassAction {baseField middleField extensionField : Type u}
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField] [IsScalarTower baseField middleField extensionField]
    {curve : Curve baseField}
    {directGroup iteratedGroup : CommGrp (Over (Spec (.of extensionField)))}
    {directRepresentation : (picardFunctorDegree
      ((Curve.baseChange baseField extensionField).obj curve).carrier.hom 0).obj.RepresentableBy
        directGroup.X}
    {iteratedRepresentation : (picardFunctorDegree
      ((Curve.baseChange middleField extensionField).obj
        ((Curve.baseChange baseField middleField).obj curve)).carrier.hom 0).obj.RepresentableBy
          iteratedGroup.X}
    (returnMap : directGroup ⟶ iteratedGroup) : Prop :=
  ∀ (parameter : Over (Spec (.of extensionField)))
    (point : parameter ⟶ directGroup.X)
    (picardClass : (pullback
      ((Curve.baseChange baseField extensionField).obj curve).carrier.hom parameter.hom).Pic),
    classifiesClass directRepresentation point picardClass →
      classifiesClass iteratedRepresentation (point ≫ returnMap.hom.hom.hom)
        (Scheme.Pic.map (picardFamilyMap
          ((Curve.baseChange.compIso baseField middleField extensionField).app curve).inv
            parameter) picardClass)

namespace PicardTensorCompatible

variable {baseField middleField extensionField : Type u}
  [Field baseField] [Field middleField] [Field extensionField]
  [Algebra baseField middleField] [Algebra middleField extensionField]
  [Algebra baseField extensionField] [IsScalarTower baseField middleField extensionField]
  {curve : Curve baseField}
  {group : CommGrp (Over (Spec (.of baseField)))}
  {middleGroup : CommGrp (Over (Spec (.of middleField)))}
  {directGroup iteratedGroup : CommGrp (Over (Spec (.of extensionField)))}
  {representation : (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy group.X}
  {middleRepresentation : (picardFunctorDegree
    ((Curve.baseChange baseField middleField).obj curve).carrier.hom 0).obj.RepresentableBy
      middleGroup.X}
  {directRepresentation : (picardFunctorDegree
    ((Curve.baseChange baseField extensionField).obj curve).carrier.hom 0).obj.RepresentableBy
      directGroup.X}
  {iteratedRepresentation : (picardFunctorDegree
    ((Curve.baseChange middleField extensionField).obj
      ((Curve.baseChange baseField middleField).obj curve)).carrier.hom 0).obj.RepresentableBy
        iteratedGroup.X}

private theorem restrictedClass_tower
    (parameter : Over (Spec (.of extensionField)))
    (point : parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj group).X)
    (iteratedPoint : parameter ⟶ ((baseChange middleField extensionField).mapCommGrp.obj
      ((baseChange baseField middleField).mapCommGrp.obj group)).X)
    (adjunction : baseChangeHomMulEquiv (extensionField := middleField) group
        ((Over.map (fieldMap middleField extensionField)).obj parameter)
        (baseChangeHomMulEquiv (extensionField := extensionField)
          ((baseChange baseField middleField).mapCommGrp.obj group) parameter iteratedPoint) =
      baseChange.restrictionComp baseField middleField extensionField parameter ≫
        baseChangeHomMulEquiv group parameter point)
    (picardClass : (pullback curve.carrier.hom
      ((Over.map (fieldMap baseField extensionField)).obj parameter).hom).Pic)
    (classifies : classifiesClass representation
      (baseChangeHomMulEquiv group parameter point) picardClass) :
    classifiesClass representation
      (baseChangeHomMulEquiv (extensionField := middleField) group
        ((Over.map (fieldMap middleField extensionField)).obj parameter)
        (baseChangeHomMulEquiv (extensionField := extensionField)
          ((baseChange baseField middleField).mapCommGrp.obj group) parameter iteratedPoint))
      (Scheme.Pic.map (baseChangeMap curve.carrier.hom
        (baseChange.restrictionComp baseField middleField extensionField parameter))
          picardClass) := by
  have restrictedClass := representedClass_restrict representation
    (baseChange.restrictionComp baseField middleField extensionField parameter)
    (baseChangeHomMulEquiv group parameter point) picardClass classifies
  exact (congrArg (fun morphism ↦
    (picardFunctorDegreeι curve.carrier.hom 0).hom.app
      (.op ((Over.map (fieldMap baseField middleField)).obj
        ((Over.map (fieldMap middleField extensionField)).obj parameter)))
          (representation.homEquiv morphism)) adjunction).trans restrictedClass

private theorem direct_baseChange_return_class
    (directExtension : (baseChange baseField extensionField).mapCommGrp.obj group ⟶ directGroup)
    (returnMap : directGroup ⟶ iteratedGroup)
    (directClassifies : extensionClassAction representation directRepresentation directExtension)
    (returnClassifies : pullbackClassAction (curve := curve)
      (directRepresentation := directRepresentation)
      (iteratedRepresentation := iteratedRepresentation) returnMap)
    (parameter : Over (Spec (.of extensionField)))
    (point : parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj group).X)
    (picardClass : (pullback curve.carrier.hom
      ((Over.map (fieldMap baseField extensionField)).obj parameter).hom).Pic)
    (classifies : classifiesClass representation
      (baseChangeHomMulEquiv group parameter point) picardClass) :
    (picardFunctorDegreeι ((Curve.baseChange middleField extensionField).obj
      ((Curve.baseChange baseField middleField).obj curve)).carrier.hom 0).hom.app (.op parameter)
        (iteratedRepresentation.homEquiv
          ((point ≫ directExtension.hom.hom.hom) ≫ returnMap.hom.hom.hom)) =
      (toPicardFunctor ((Curve.baseChange middleField extensionField).obj
        ((Curve.baseChange baseField middleField).obj curve)).carrier.hom).app (.op parameter)
          (Scheme.Pic.map
            (picardFamilyMap
              ((Curve.baseChange.compIso baseField middleField extensionField).app curve).inv
              parameter) (Scheme.Pic.map (familyMap curve parameter) picardClass)) := by
  exact returnClassifies parameter (point ≫ directExtension.hom.hom.hom)
    (Scheme.Pic.map (familyMap curve parameter) picardClass)
    (directClassifies parameter point picardClass classifies)

private theorem baseChange_comp_class
    (comparison : ((baseChange baseField extensionField).mapCommGrp.obj group).X ⟶
      ((baseChange middleField extensionField).mapCommGrp.obj
        ((baseChange baseField middleField).mapCommGrp.obj group)).X)
    (adjunction : ∀ (parameter : Over (Spec (.of extensionField)))
      (point : parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj group).X),
      baseChangeHomMulEquiv (extensionField := middleField) group
          ((Over.map (fieldMap middleField extensionField)).obj parameter)
          (baseChangeHomMulEquiv (extensionField := extensionField)
            ((baseChange baseField middleField).mapCommGrp.obj group) parameter
            (point ≫ comparison)) =
        baseChange.restrictionComp baseField middleField extensionField parameter ≫
          baseChangeHomMulEquiv group parameter point)
    (middleExtension : (baseChange baseField middleField).mapCommGrp.obj group ⟶ middleGroup)
    (iteratedExtension : (baseChange middleField extensionField).mapCommGrp.obj middleGroup ⟶
      iteratedGroup)
    (directExtension : (baseChange baseField extensionField).mapCommGrp.obj group ⟶ directGroup)
    (returnMap : directGroup ⟶ iteratedGroup)
    (middleClassifies : extensionClassAction representation middleRepresentation middleExtension)
    (iteratedClassifies : extensionClassAction middleRepresentation iteratedRepresentation
      iteratedExtension)
    (directClassifies : extensionClassAction representation directRepresentation directExtension)
    (returnClassifies : pullbackClassAction (curve := curve)
      (directRepresentation := directRepresentation)
      (iteratedRepresentation := iteratedRepresentation) returnMap)
    (parameter : Over (Spec (.of extensionField)))
    (point : parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj group).X)
    (picardClass : (pullback curve.carrier.hom
      ((Over.map (fieldMap baseField extensionField)).obj parameter).hom).Pic)
    (classifies : classifiesClass representation
      (baseChangeHomMulEquiv group parameter point) picardClass) :
    (picardFunctorDegreeι ((Curve.baseChange middleField extensionField).obj
      ((Curve.baseChange baseField middleField).obj curve)).carrier.hom 0).hom.app (.op parameter)
        (iteratedRepresentation.homEquiv
          ((point ≫ directExtension.hom.hom.hom) ≫ returnMap.hom.hom.hom)) =
      (picardFunctorDegreeι ((Curve.baseChange middleField extensionField).obj
        ((Curve.baseChange baseField middleField).obj curve)).carrier.hom 0).hom.app (.op parameter)
          (iteratedRepresentation.homEquiv
            (((point ≫ comparison) ≫
                (baseChange middleField extensionField).map middleExtension.hom.hom.hom) ≫
                  iteratedExtension.hom.hom.hom)) := by
  have leftClass := direct_baseChange_return_class directExtension returnMap
    directClassifies returnClassifies parameter point picardClass classifies
  let restrictedParameter := (Over.map (fieldMap middleField extensionField)).obj parameter
  let restrictedPicardClass := Scheme.Pic.map (baseChangeMap curve.carrier.hom
    (baseChange.restrictionComp baseField middleField extensionField parameter)) picardClass
  let adjustedPoint := point ≫ comparison
  have rightClass := iterated_class_action (baseChange middleField extensionField)
    (source := (baseChange baseField middleField).obj group.X)
    (middle := middleGroup.X) (restrictedParameter := restrictedParameter)
    (parameter := parameter) (target := iteratedGroup.X)
    (fun middlePoint picardClass ↦ classifiesClass representation
      (baseChangeHomMulEquiv group restrictedParameter middlePoint) picardClass)
    (classifiesClass middleRepresentation) (classifiesClass iteratedRepresentation)
    (baseChangeHomMulEquiv ((baseChange baseField middleField).mapCommGrp.obj group) parameter)
    (baseChangeHomMulEquiv middleGroup parameter)
    middleExtension.hom.hom.hom iteratedExtension.hom.hom.hom
    (Scheme.Pic.map (familyMap curve restrictedParameter))
    (Scheme.Pic.map (familyMap ((Curve.baseChange baseField middleField).obj curve) parameter))
    (middleClassifies restrictedParameter) (iteratedClassifies parameter)
    adjustedPoint restrictedPicardClass
    (restrictedClass_tower parameter point adjustedPoint (adjunction parameter point)
      picardClass classifies)
    (baseChangeHomMulEquiv_postcomp middleExtension parameter adjustedPoint)
  exact leftClass.trans
    ((congrArg ((toPicardFunctor
      ((Curve.baseChange middleField extensionField).obj
        ((Curve.baseChange baseField middleField).obj curve)).carrier.hom).app (.op parameter))
      (familyClass_comp baseField middleField extensionField curve parameter picardClass)).trans
        rightClass.symm)

private theorem baseChange_comp_of_classes
    (comparison : baseChange baseField extensionField ≅
      baseChange baseField middleField ⋙ baseChange middleField extensionField)
    (adjunction : ∀ (parameter : Over (Spec (.of extensionField)))
      (point : parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj group).X),
      baseChangeHomMulEquiv (extensionField := middleField) group
          ((Over.map (fieldMap middleField extensionField)).obj parameter)
          (baseChangeHomMulEquiv (extensionField := extensionField)
            ((baseChange baseField middleField).mapCommGrp.obj group) parameter
            (point ≫ (comparison.app group.X).hom)) =
        baseChange.restrictionComp baseField middleField extensionField parameter ≫
          baseChangeHomMulEquiv group parameter point)
    (middleExtension : (baseChange baseField middleField).mapCommGrp.obj group ⟶ middleGroup)
    (iteratedExtension : (baseChange middleField extensionField).mapCommGrp.obj middleGroup ⟶
      iteratedGroup)
    (directExtension : (baseChange baseField extensionField).mapCommGrp.obj group ⟶ directGroup)
    (returnMap : directGroup ⟶ iteratedGroup)
    (middleClassifies : extensionClassAction representation middleRepresentation middleExtension)
    (iteratedClassifies : extensionClassAction middleRepresentation iteratedRepresentation
      iteratedExtension)
    (directClassifies : extensionClassAction representation directRepresentation directExtension)
    (returnClassifies : pullbackClassAction (curve := curve)
      (directRepresentation := directRepresentation)
      (iteratedRepresentation := iteratedRepresentation) returnMap) :
    directExtension ≫ returnMap =
      (Functor.mapCommGrpNatIso comparison).hom.app group ≫
      (Functor.mapCommGrpCompIso (F := baseChange baseField middleField)
        (G := baseChange middleField extensionField)).hom.app group ≫
      (baseChange middleField extensionField).mapCommGrp.map middleExtension ≫
        iteratedExtension := by
  apply mapCommGrp_comp_of_underlying (baseChange baseField middleField)
    (baseChange middleField extensionField) (baseChange baseField extensionField)
    comparison
    middleExtension iteratedExtension directExtension returnMap
  exact hom_comp_eq_of_class_observations
    (fun parameter morphism ↦
      (picardFunctorDegreeι ((Curve.baseChange middleField extensionField).obj
        ((Curve.baseChange baseField middleField).obj curve)).carrier.hom 0).hom.app (.op parameter)
          (iteratedRepresentation.homEquiv morphism))
    (fun parameter point picardClass ↦ classifiesClass representation
      (baseChangeHomMulEquiv group parameter point) picardClass)
    (picardClass_hom_ext curve ((Curve.baseChange middleField extensionField).obj
      ((Curve.baseChange baseField middleField).obj curve)) representation iteratedRepresentation)
    directExtension.hom.hom.hom returnMap.hom.hom.hom
    (comparison.app group.X).hom
    ((baseChange middleField extensionField).map middleExtension.hom.hom.hom)
    iteratedExtension.hom.hom.hom
    (baseChange_comp_class
      (comparison.app group.X).hom adjunction
      middleExtension iteratedExtension directExtension returnMap
      middleClassifies iteratedClassifies directClassifies returnClassifies)

/-- Direct and iterated field extension agree after the canonical group and curve
tower comparisons, for arbitrary supplied tensor-compatible representations. -/
theorem baseChangeIso_comp
    (compatibility : PicardTensorCompatible curve.carrier.hom group representation)
    (middleCompatibility : PicardTensorCompatible
      ((Curve.baseChange baseField middleField).obj curve).carrier.hom middleGroup
        middleRepresentation)
    (directCompatibility : PicardTensorCompatible
      ((Curve.baseChange baseField extensionField).obj curve).carrier.hom directGroup
        directRepresentation)
    (iteratedCompatibility : PicardTensorCompatible
      ((Curve.baseChange middleField extensionField).obj
        ((Curve.baseChange baseField middleField).obj curve)).carrier.hom iteratedGroup
          iteratedRepresentation) :
    (baseChangeIso compatibility directCompatibility).hom ≫
        representedPullback iteratedCompatibility directCompatibility
          ((Curve.baseChange.compIso baseField middleField extensionField).app curve).inv =
      ((Functor.mapCommGrpNatIso
          (baseChange.compIso baseField middleField extensionField)).app group ≪≫
        (Functor.mapCommGrpCompIso (F := baseChange baseField middleField)
          (G := baseChange middleField extensionField)).app group ≪≫
        (baseChange middleField extensionField).mapCommGrp.mapIso
          (baseChangeIso compatibility middleCompatibility) ≪≫
        baseChangeIso middleCompatibility iteratedCompatibility).hom := by
  exact baseChange_comp_of_classes
    (curve := curve) (representation := representation)
    (middleRepresentation := middleRepresentation) (directRepresentation := directRepresentation)
    (iteratedRepresentation := iteratedRepresentation)
    (baseChange.compIso baseField middleField extensionField)
    (baseChangeHomMulEquiv_comp baseField middleField extensionField group)
    (baseChangeIso compatibility middleCompatibility).hom
    (baseChangeIso middleCompatibility iteratedCompatibility).hom
    (baseChangeIso compatibility directCompatibility).hom
    (representedPullback iteratedCompatibility directCompatibility
      ((Curve.baseChange.compIso baseField middleField extensionField).app curve).inv)
    (by
      intro parameter point picardClass classifies
      obtain ⟨lineBundle, invertible, rfl⟩ := Scheme.Pic.exists_mk_eq picardClass
      letI := invertible
      simpa only [classifiesClass, Scheme.Pic.map_mk] using
        baseChangeIso_class compatibility middleCompatibility parameter point lineBundle classifies)
    (by
      intro parameter point picardClass classifies
      obtain ⟨lineBundle, invertible, rfl⟩ := Scheme.Pic.exists_mk_eq picardClass
      letI := invertible
      simpa only [classifiesClass, Scheme.Pic.map_mk] using
        baseChangeIso_class middleCompatibility iteratedCompatibility parameter point lineBundle
          classifies)
    (by
      intro parameter point picardClass classifies
      obtain ⟨lineBundle, invertible, rfl⟩ := Scheme.Pic.exists_mk_eq picardClass
      letI := invertible
      simpa only [classifiesClass, Scheme.Pic.map_mk] using
        baseChangeIso_class compatibility directCompatibility parameter point lineBundle classifies)
    (by
      intro parameter point picardClass classifies
      obtain ⟨lineBundle, invertible, rfl⟩ := Scheme.Pic.exists_mk_eq picardClass
      letI := invertible
      simpa only [classifiesClass, Scheme.Pic.map_mk] using
        representedPullback_class iteratedCompatibility directCompatibility
          ((Curve.baseChange.compIso baseField middleField extensionField).app curve).inv
          parameter point lineBundle classifies)

end PicardTensorCompatible

end AlgebraicGeometry
