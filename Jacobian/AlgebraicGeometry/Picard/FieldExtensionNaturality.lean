import Jacobian.AlgebraicGeometry.Picard.RepresentedBaseChange
import Jacobian.AlgebraicGeometry.Picard.RepresentedFunctor

/-!
# Naturality of represented Picard field extension

The actual Cartesian maps of line-bundle families commute with curve morphisms.
Consequently the field-extension isomorphisms of supplied tensor-compatible
Picard representations commute with their contravariant pullback homomorphisms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {baseField extensionField : Type u} [Field baseField] [Field extensionField]
  [Algebra baseField extensionField]

private abbrev fieldMap : Spec (.of extensionField) ⟶ Spec (.of baseField) :=
  Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))

/-- The actual maps on Picard families commute with Cartesian field extension. -/
theorem picardFamilyMap_baseChange
    {source target : Over (Spec (.of baseField))} (morphism : source ⟶ target)
    (parameter : Over (Spec (.of extensionField))) :
    picardFamilyMap ((baseChange baseField extensionField).map morphism) parameter ≫
        (pullbackIsoOfIsPullback (IsPullback.of_hasPullback target.hom fieldMap) parameter).hom =
      (pullbackIsoOfIsPullback (IsPullback.of_hasPullback source.hom fieldMap) parameter).hom ≫
        picardFamilyMap morphism ((Over.map fieldMap).obj parameter) := by
  apply pullback.hom_ext <;>
    simp [picardFamilyMap, Category.assoc, pullbackIsoOfIsPullback_hom_fst,
      pullbackIsoOfIsPullback_hom_snd, Over.pullback_map_left]

namespace PicardTensorCompatible

variable {source target : Curve baseField}
  {sourceGroup targetGroup : CommGrp (Over (Spec (.of baseField)))}
  {extendedSourceGroup extendedTargetGroup : CommGrp (Over (Spec (.of extensionField)))}
  {sourceRepresentation : (picardFunctorDegree source.carrier.hom 0).obj.RepresentableBy
    sourceGroup.X}
  {targetRepresentation : (picardFunctorDegree target.carrier.hom 0).obj.RepresentableBy
    targetGroup.X}
  {extendedSourceRepresentation : (picardFunctorDegree
    ((Curve.baseChange baseField extensionField).obj source).carrier.hom 0).obj.RepresentableBy
      extendedSourceGroup.X}
  {extendedTargetRepresentation : (picardFunctorDegree
    ((Curve.baseChange baseField extensionField).obj target).carrier.hom 0).obj.RepresentableBy
      extendedTargetGroup.X}

/-- The characterized group comparison commutes with every curve pullback. -/
theorem baseChangeIso_naturality
    (sourceCompatibility : PicardTensorCompatible source.carrier.hom sourceGroup
      sourceRepresentation)
    (targetCompatibility : PicardTensorCompatible target.carrier.hom targetGroup
      targetRepresentation)
    (extendedSourceCompatibility : PicardTensorCompatible
      ((Curve.baseChange baseField extensionField).obj source).carrier.hom extendedSourceGroup
        extendedSourceRepresentation)
    (extendedTargetCompatibility : PicardTensorCompatible
      ((Curve.baseChange baseField extensionField).obj target).carrier.hom extendedTargetGroup
        extendedTargetRepresentation)
    (morphism : source ⟶ target) :
    (baseChange baseField extensionField).mapCommGrp.map
        (representedPullback sourceCompatibility targetCompatibility morphism) ≫
        (baseChangeIso sourceCompatibility extendedSourceCompatibility).hom =
      (baseChangeIso targetCompatibility extendedTargetCompatibility).hom ≫
        representedPullback extendedSourceCompatibility extendedTargetCompatibility
          ((Curve.baseChange baseField extensionField).map morphism) := by
  apply CommGrp.hom_ext
  apply picardBaseChange_hom_ext target targetRepresentation extendedSourceRepresentation
  intro parameter point lineBundle invertible classifies
  let originalPullback := representedPullback sourceCompatibility targetCompatibility morphism
  let targetComparison := baseChangeIso targetCompatibility extendedTargetCompatibility
  let restrictedParameter := (Over.map (fieldMap (baseField := baseField)
    (extensionField := extensionField))).obj parameter
  let sourceFamilyMap := (pullbackIsoOfIsPullback
    (IsPullback.of_hasPullback source.carrier.hom
      (fieldMap (extensionField := extensionField))) parameter).hom
  let targetFamilyMap := (pullbackIsoOfIsPullback
    (IsPullback.of_hasPullback target.carrier.hom
      (fieldMap (extensionField := extensionField))) parameter).hom
  have originalClass := representedPullback_class sourceCompatibility targetCompatibility
    morphism restrictedParameter (baseChangeHomMulEquiv targetGroup parameter point)
      lineBundle classifies
  have firstClass := baseChangeIso_class sourceCompatibility extendedSourceCompatibility parameter
    (point ≫ ((baseChange baseField extensionField).mapCommGrp.map originalPullback).hom.hom.hom)
    ((Scheme.Modules.pullback (picardFamilyMap morphism restrictedParameter)).obj lineBundle)
    (by
      rw [baseChangeHomMulEquiv_postcomp]
      exact originalClass)
  have extendedClass := baseChangeIso_class targetCompatibility extendedTargetCompatibility
    parameter point lineBundle classifies
  have secondClass := representedPullback_class extendedSourceCompatibility
    extendedTargetCompatibility ((Curve.baseChange baseField extensionField).map morphism)
    parameter (point ≫ targetComparison.hom.hom.hom.hom)
    ((Scheme.Modules.pullback targetFamilyMap).obj lineBundle) extendedClass
  have classEquality : Scheme.Pic.map sourceFamilyMap
      (Scheme.Pic.map (picardFamilyMap morphism restrictedParameter) (Scheme.Pic.mk lineBundle)) =
    Scheme.Pic.map (picardFamilyMap ((Curve.baseChange baseField extensionField).map morphism)
      parameter) (Scheme.Pic.map targetFamilyMap (Scheme.Pic.mk lineBundle)) := by
    rw [← Scheme.Pic.map_comp, ← Scheme.Pic.map_comp]
    exact congrArg (fun familyMap ↦ Scheme.Pic.map familyMap (Scheme.Pic.mk lineBundle))
      (picardFamilyMap_baseChange morphism parameter).symm
  have bundleEquality := congrArg
    ((toPicardFunctor ((Curve.baseChange baseField extensionField).obj source).carrier.hom).app
      (.op parameter)) classEquality
  simp only [Scheme.Pic.map_mk] at bundleEquality
  simpa only [CommGrp.comp_hom, Grp.comp_hom_hom, Category.assoc] using
    firstClass.trans (bundleEquality.trans secondClass.symm)

section Functor

variable (groups : Curve baseField → CommGrp (Over (Spec (.of baseField))))
  (representations : ∀ curve : Curve baseField,
    (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy (groups curve).X)
  (compatibilities : ∀ curve : Curve baseField,
    PicardTensorCompatible curve.carrier.hom (groups curve) (representations curve))
  (extendedGroups : Curve extensionField → CommGrp (Over (Spec (.of extensionField))))
  (extendedRepresentations : ∀ curve : Curve extensionField,
    (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy (extendedGroups curve).X)
  (extendedCompatibilities : ∀ curve : Curve extensionField,
    PicardTensorCompatible curve.carrier.hom (extendedGroups curve)
      (extendedRepresentations curve))

/-- The characterized field comparisons assemble into a natural isomorphism of
the supplied represented Picard functors. -/
def representedFunctorBaseChangeIso :
    representedFunctor groups representations compatibilities ⋙
        (baseChange baseField extensionField).mapCommGrp ≅
      (Curve.baseChange baseField extensionField).op ⋙
        representedFunctor extendedGroups extendedRepresentations extendedCompatibilities :=
  NatIso.ofComponents
    (fun curve ↦ baseChangeIso (compatibilities curve.unop)
      (extendedCompatibilities ((Curve.baseChange baseField extensionField).obj curve.unop)))
    (fun morphism ↦ baseChangeIso_naturality
      (compatibilities _) (compatibilities _)
      (extendedCompatibilities _) (extendedCompatibilities _) morphism.unop)

/-- Each component is the actual bundle-characterized comparison. -/
@[simp]
theorem representedFunctorBaseChangeIso_app (curve : (Curve baseField)ᵒᵖ) :
    (representedFunctorBaseChangeIso groups representations compatibilities
      extendedGroups extendedRepresentations extendedCompatibilities).app curve =
      baseChangeIso (compatibilities curve.unop)
        (extendedCompatibilities ((Curve.baseChange baseField extensionField).obj curve.unop)) :=
  rfl

end Functor

end PicardTensorCompatible

end AlgebraicGeometry
