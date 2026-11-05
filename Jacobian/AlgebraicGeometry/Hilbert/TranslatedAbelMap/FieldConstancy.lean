import Jacobian.AlgebraicGeometry.Curve.CanonicalDegree
import Jacobian.AlgebraicGeometry.Curve.BaseChange
import Jacobian.AlgebraicGeometry.Cohomology.FieldExtension
import Jacobian.AlgebraicGeometry.Cohomology.Sections
import Jacobian.AlgebraicGeometry.Hilbert.DivisorSections
import Jacobian.AlgebraicGeometry.Hilbert.OrderedDivisors.AbelJacobi
import Jacobian.AlgebraicGeometry.Hilbert.OrderedDivisors.KernelPair
import Jacobian.AlgebraicGeometry.Hilbert.SectionPencil.Family
import Jacobian.AlgebraicGeometry.Picard.Field
import Jacobian.AlgebraicGeometry.Picard.RationalPoint
import Jacobian.LinearAlgebra.LinearIndependent.Companion

/-!
# Abelian-valued maps on field fibres of the translated Abel map

Linearly equivalent effective divisors of degree twice the genus plus one
are joined by two pencils through a common independent section. The pencils
are classified in the original Hilbert functor, including after extension of
the ground field. Constancy of maps from the projective line to abelian
varieties therefore gives equality of the entire field-valued morphisms.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Hilbert

open Scheme

variable {baseField extensionField : Type u} [Field baseField] [Field extensionField]
  [Algebra baseField extensionField]

private abbrev fieldMap : Spec (.of extensionField) ⟶ Spec (.of baseField) :=
  Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))

private theorem hilbertCondition_comap_iso {source target parameter : Scheme.{u}}
    (sourceProjection : source ⟶ parameter) (targetProjection : target ⟶ parameter)
    (comparison : source ≅ target)
    (projectionEquation : comparison.hom ≫ targetProjection = sourceProjection)
    (degree : ℕ) (ideal : target.IdealSheafData)
    (condition : IsFinite (ideal.subschemeι ≫ targetProjection) ∧
      Flat (ideal.subschemeι ≫ targetProjection) ∧
      LocallyOfFinitePresentation (ideal.subschemeι ≫ targetProjection) ∧
        ∀ point, (ideal.subschemeι ≫ targetProjection).finrank point = degree) :
    IsFinite ((ideal.comap comparison.hom).subschemeι ≫ sourceProjection) ∧
      Flat ((ideal.comap comparison.hom).subschemeι ≫ sourceProjection) ∧
      LocallyOfFinitePresentation ((ideal.comap comparison.hom).subschemeι ≫ sourceProjection) ∧
        ∀ point, ((ideal.comap comparison.hom).subschemeι ≫ sourceProjection).finrank point =
          degree := by
  have baseSquare : IsPullback comparison.hom sourceProjection targetProjection (𝟙 parameter) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using projectionEquation⟩
  have divisorSquare : IsPullback
      ((ideal.comapIso comparison.hom).hom ≫ pullback.snd comparison.hom ideal.subschemeι)
      ((ideal.comap comparison.hom).subschemeι ≫ sourceProjection)
      (ideal.subschemeι ≫ targetProjection) (𝟙 parameter) :=
    ((IsPullback.of_hasPullback comparison.hom ideal.subschemeι).flip.paste_vert
      baseSquare).of_iso' (ideal.comapIso _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp) (by simp) (by simp)
  obtain ⟨finite, flat, finitePresentation, rank⟩ := condition
  refine ⟨MorphismProperty.of_isPullback divisorSquare finite,
    MorphismProperty.of_isPullback divisorSquare flat,
    MorphismProperty.of_isPullback divisorSquare finitePresentation, fun point ↦ ?_⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ divisorSquare]
  exact rank point

section FieldPencil

variable (curve : Curve baseField)

private abbrev extendedCurve : Curve extensionField :=
  (Curve.baseChange baseField extensionField).obj curve

local instance extendedOver :
    (extendedCurve (extensionField := extensionField) curve).carrier.left.Over
      (Spec (.of extensionField)) :=
  ⟨(extendedCurve (extensionField := extensionField) curve).carrier.hom⟩

local instance extendedProper :
    IsProper ((extendedCurve (extensionField := extensionField) curve).carrier.left ↘
      Spec (.of extensionField)) :=
  inferInstanceAs (IsProper (extendedCurve (extensionField := extensionField) curve).carrier.hom)

local instance extendedSmooth :
    SmoothOfRelativeDimension 1
      ((extendedCurve (extensionField := extensionField) curve).carrier.left ↘
        Spec (.of extensionField)) :=
  inferInstanceAs (SmoothOfRelativeDimension 1
    (extendedCurve (extensionField := extensionField) curve).carrier.hom)

local instance extendedGeometricallyIrreducible :
    GeometricallyIrreducible
      ((extendedCurve (extensionField := extensionField) curve).carrier.left ↘
        Spec (.of extensionField)) :=
  (extendedCurve (extensionField := extensionField) curve).geometricallyIrreducible

local instance extendedIntegral :
    GeometricallyIntegral ((extendedCurve (extensionField := extensionField) curve).carrier.left ↘
      Spec (.of extensionField)) := by
  letI : Smooth
      ((extendedCurve (extensionField := extensionField) curve).carrier.left ↘
        Spec (.of extensionField)) := SmoothOfRelativeDimension.smooth 1 _
  exact Smooth.geometricallyIntegral _

private def fieldProductIso (parameter : Over (Spec (.of extensionField))) :
    pullback (extendedCurve (extensionField := extensionField) curve).carrier.hom parameter.hom ≅
      pullback curve.carrier.hom ((Over.map fieldMap).obj parameter).hom :=
  pullbackIsoOfIsPullback (IsPullback.of_hasPullback curve.carrier.hom fieldMap) parameter

private def fieldHilbertPoint (degree : ℕ) (parameter : Over (Spec (.of extensionField)))
    (divisor : (hilbertPresheaf
      (extendedCurve (extensionField := extensionField) curve).carrier.hom degree).obj
        (op parameter)) :
    (hilbertPresheaf curve.carrier.hom degree).obj
      (op ((Over.map fieldMap).obj parameter)) := by
  let comparison := fieldProductIso curve parameter
  let sourceProjection := pullback.snd
    (extendedCurve (extensionField := extensionField) curve).carrier.hom parameter.hom
  let targetProjection := pullback.snd curve.carrier.hom ((Over.map fieldMap).obj parameter).hom
  have projectionEquation : comparison.inv ≫ sourceProjection = targetProjection := by
    have equation : comparison.hom ≫ targetProjection = sourceProjection :=
      pullbackIsoOfIsPullback_hom_snd
        (IsPullback.of_hasPullback curve.carrier.hom fieldMap) parameter
    rw [← equation, comparison.inv_hom_id_assoc]
  exact ⟨divisor.1.comap comparison.inv,
    hilbertCondition_comap_iso targetProjection sourceProjection comparison.symm
      projectionEquation degree divisor.1 divisor.2⟩

private def fieldPencilPoint (degree : ℕ)
    (lineBundle : (extendedCurve (extensionField := extensionField) curve).carrier.left.Modules)
    [lineBundle.IsInvertible]
    (firstSection secondSection :
      unit (extendedCurve (extensionField := extensionField) curve).carrier.left ⟶ lineBundle)
    (independent : LinearIndependent extensionField
      ![H.unitHomAddEquiv lineBundle firstSection, H.unitHomAddEquiv lineBundle secondSection])
    (degreeEquation : lineBundle.degree extensionField = degree) :
    (hilbertPresheaf curve.carrier.hom degree).obj
      (op ((Over.map fieldMap).obj (ProjectiveLine.relativeLineOver extensionField))) :=
  fieldHilbertPoint curve degree (ProjectiveLine.relativeLineOver extensionField)
    (SectionPencil.pencilPoint degree lineBundle firstSection secondSection independent
      degreeEquation)

private def fieldEndpoint (coordinate : ULift.{u} (Fin 2)) :
    Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField)) ⟶
      (Over.map fieldMap).obj (ProjectiveLine.relativeLineOver extensionField) :=
  Over.homMk (SectionPencil.endpoint coordinate) (by
    change SectionPencil.endpoint coordinate ≫
      (ProjectiveLine.relativeLine (Spec (.of extensionField)) ↘
        Spec (.of extensionField)) ≫ fieldMap = fieldMap
    rw [← Category.assoc, SectionPencil.endpoint_over, Category.id_comp])

private theorem fieldEndpoint_baseChangeMap (coordinate : ULift.{u} (Fin 2)) :
    baseChangeMap curve.carrier.hom (fieldEndpoint coordinate) ≫
        (fieldProductIso curve (ProjectiveLine.relativeLineOver extensionField)).inv =
      SectionPencil.endpointInclusion
        (extendedCurve (extensionField := extensionField) curve).carrier.hom coordinate := by
  change baseChangeMap curve.carrier.hom (fieldEndpoint coordinate) ≫
      (pullbackIsoOfIsPullback (IsPullback.of_hasPullback curve.carrier.hom fieldMap)
        (ProjectiveLine.relativeLineOver extensionField)).inv =
    SectionPencil.endpointInclusion (pullback.snd curve.carrier.hom fieldMap) coordinate
  have firstProjection := pullbackIsoOfIsPullback_hom_fst
    (IsPullback.of_hasPullback curve.carrier.hom fieldMap)
    (ProjectiveLine.relativeLineOver extensionField)
  have secondProjection := pullbackIsoOfIsPullback_hom_snd
    (IsPullback.of_hasPullback curve.carrier.hom fieldMap)
    (ProjectiveLine.relativeLineOver extensionField)
  have endpointFirst :
      SectionPencil.endpointInclusion (pullback.snd curve.carrier.hom fieldMap) coordinate ≫
        pullback.fst (pullback.snd curve.carrier.hom fieldMap)
          (ProjectiveLine.relativeLineOver extensionField).hom =
        𝟙 (pullback curve.carrier.hom fieldMap) :=
    SectionPencil.endpointInclusion_curve _ coordinate
  have endpointSecond :
      SectionPencil.endpointInclusion (pullback.snd curve.carrier.hom fieldMap) coordinate ≫
        pullback.snd (pullback.snd curve.carrier.hom fieldMap)
          (ProjectiveLine.relativeLineOver extensionField).hom =
        pullback.snd curve.carrier.hom fieldMap ≫ SectionPencil.endpoint coordinate :=
    SectionPencil.endpointInclusion_parameter _ coordinate
  apply (cancel_mono (pullbackIsoOfIsPullback
    (IsPullback.of_hasPullback curve.carrier.hom fieldMap)
      (ProjectiveLine.relativeLineOver extensionField)).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · change baseChangeMap curve.carrier.hom (fieldEndpoint coordinate) ≫
        pullback.fst curve.carrier.hom
          ((ProjectiveLine.relativeLineOver extensionField).hom ≫ fieldMap) =
      SectionPencil.endpointInclusion (pullback.snd curve.carrier.hom fieldMap) coordinate ≫
        (pullbackIsoOfIsPullback (IsPullback.of_hasPullback curve.carrier.hom fieldMap)
          (ProjectiveLine.relativeLineOver extensionField)).hom ≫
            pullback.fst curve.carrier.hom
              ((ProjectiveLine.relativeLineOver extensionField).hom ≫ fieldMap)
    rw [firstProjection, ← Category.assoc, endpointFirst, Category.id_comp]
    simp [baseChangeMap]
  · change baseChangeMap curve.carrier.hom (fieldEndpoint coordinate) ≫
        pullback.snd curve.carrier.hom
          ((ProjectiveLine.relativeLineOver extensionField).hom ≫ fieldMap) =
      SectionPencil.endpointInclusion (pullback.snd curve.carrier.hom fieldMap) coordinate ≫
        (pullbackIsoOfIsPullback (IsPullback.of_hasPullback curve.carrier.hom fieldMap)
          (ProjectiveLine.relativeLineOver extensionField)).hom ≫
            pullback.snd curve.carrier.hom
              ((ProjectiveLine.relativeLineOver extensionField).hom ≫ fieldMap)
    rw [secondProjection, endpointSecond]
    dsimp only [baseChangeMap, fieldEndpoint, Over.homMk_left]
    exact pullback.lift_snd _ _ _

private theorem fieldPencilPoint_endpoint_val (degree : ℕ)
    (lineBundle : (extendedCurve (extensionField := extensionField) curve).carrier.left.Modules)
    [lineBundle.IsInvertible]
    (firstSection secondSection :
      unit (extendedCurve (extensionField := extensionField) curve).carrier.left ⟶ lineBundle)
    (independent : LinearIndependent extensionField
      ![H.unitHomAddEquiv lineBundle firstSection, H.unitHomAddEquiv lineBundle secondSection])
    (degreeEquation : lineBundle.degree extensionField = degree)
    (coordinate : ULift.{u} (Fin 2)) :
    ((hilbertPresheaf curve.carrier.hom degree).map (fieldEndpoint coordinate).op
      (fieldPencilPoint curve degree lineBundle firstSection secondSection independent
        degreeEquation)).val =
      (SectionPencil.projectiveLineIdeal
        (extendedCurve (extensionField := extensionField) curve).carrier.hom
        firstSection secondSection).comap
          (SectionPencil.endpointInclusion
            (extendedCurve (extensionField := extensionField) curve).carrier.hom coordinate) := by
  change ((SectionPencil.projectiveLineIdeal
    (extendedCurve (extensionField := extensionField) curve).carrier.hom
      firstSection secondSection).comap
      (fieldProductIso curve (ProjectiveLine.relativeLineOver extensionField)).inv).comap
        (baseChangeMap curve.carrier.hom (fieldEndpoint coordinate)) = _
  rw [← IdealSheafData.comap_comp, fieldEndpoint_baseChangeMap]

private theorem field_endpoints_image_eq (variety : AbelianVariety baseField)
    (morphism : (Over.map fieldMap).obj (ProjectiveLine.relativeLineOver extensionField) ⟶
      variety.group.X) (first second : ULift.{u} (Fin 2)) :
    fieldEndpoint first ≫ morphism = fieldEndpoint second ≫ morphism := by
  let extendedVariety := (AbelianVariety.baseChange baseField extensionField).obj variety
  let extendedMorphism : ProjectiveLine.relativeLineOver extensionField ⟶ extendedVariety.group.X :=
    Over.homMk (pullback.lift morphism.left
      (ProjectiveLine.relativeLineOver extensionField).hom (by simpa using Over.w morphism))
      (pullback.lift_snd ..)
  let firstPoint := SectionPencil.endpointOver (baseField := extensionField) first
  let secondPoint := SectionPencil.endpointOver (baseField := extensionField) second
  obtain ⟨constant, constantEquation, -⟩ :=
    AbelianVariety.RationalCurves.existsUnique_constant extendedVariety extendedMorphism
  have extendedEquality : firstPoint ≫ extendedMorphism = secondPoint ≫ extendedMorphism := by
    rw [constantEquation]
    simp only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  have projectedEquality := congrArg
    (fun arrow : 𝟙_ (Over (Spec (.of extensionField))) ⟶ extendedVariety.group.X ↦
      arrow.left ≫ pullback.fst variety.group.X.hom fieldMap) extendedEquality
  apply Over.OverMorphism.ext
  change SectionPencil.endpoint first ≫ morphism.left =
    SectionPencil.endpoint second ≫ morphism.left
  simpa only [firstPoint, secondPoint, SectionPencil.endpointOver, extendedMorphism,
    Over.comp_left, Over.homMk_left, Category.assoc, pullback.lift_fst] using projectedEquality

private theorem independent_field_sections_image_eq (degree : ℕ)
    {representative : Over (Spec (.of baseField))}
    (representation : (hilbertPresheaf curve.carrier.hom degree).RepresentableBy representative)
    (variety : AbelianVariety baseField) (morphism : representative ⟶ variety.group.X)
    (lineBundle : (extendedCurve (extensionField := extensionField) curve).carrier.left.Modules)
    [lineBundle.IsInvertible]
    (firstSection secondSection :
      unit (extendedCurve (extensionField := extensionField) curve).carrier.left ⟶ lineBundle)
    (independent : LinearIndependent extensionField
      ![H.unitHomAddEquiv lineBundle firstSection, H.unitHomAddEquiv lineBundle secondSection])
    (degreeEquation : lineBundle.degree extensionField = degree)
    (firstDivisor secondDivisor : (hilbertPresheaf curve.carrier.hom degree).obj
      (op (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField)))))
    (firstIdeal : firstDivisor.val = Scheme.Modules.Hom.zeroLocus firstSection)
    (secondIdeal : secondDivisor.val = Scheme.Modules.Hom.zeroLocus secondSection) :
    representation.homEquiv.symm firstDivisor ≫ morphism =
      representation.homEquiv.symm secondDivisor ≫ morphism := by
  let pencil := fieldPencilPoint curve degree lineBundle firstSection secondSection
    independent degreeEquation
  let pencilMap := representation.homEquiv.symm pencil
  have firstPoint : (hilbertPresheaf curve.carrier.hom degree).map
      (fieldEndpoint ⟨0⟩).op pencil = firstDivisor := by
    apply Subtype.ext
    rw [fieldPencilPoint_endpoint_val, SectionPencil.projectiveLineIdeal_first, firstIdeal]
  have secondPoint : (hilbertPresheaf curve.carrier.hom degree).map
      (fieldEndpoint ⟨1⟩).op pencil = secondDivisor := by
    apply Subtype.ext
    rw [fieldPencilPoint_endpoint_val, SectionPencil.projectiveLineIdeal_second, secondIdeal]
  have firstMap : fieldEndpoint ⟨0⟩ ≫ pencilMap =
      representation.homEquiv.symm firstDivisor := by
    rw [Functor.RepresentableBy.comp_homEquiv_symm, firstPoint]
  have secondMap : fieldEndpoint ⟨1⟩ ≫ pencilMap =
      representation.homEquiv.symm secondDivisor := by
    rw [Functor.RepresentableBy.comp_homEquiv_symm, secondPoint]
  simpa only [← Category.assoc, firstMap, secondMap] using
    field_endpoints_image_eq variety (pencilMap ≫ morphism) ⟨0⟩ ⟨1⟩

end FieldPencil

section FieldConstancy

variable (curve : PointedCurve baseField)

local instance curveOver : curve.curve.carrier.left.Over (Spec (.of baseField)) :=
  ⟨curve.curve.carrier.hom⟩

local instance curveProper : IsProper (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  curve.curve.isProper

local instance curveSmooth : SmoothOfRelativeDimension 1
    (curve.curve.carrier.left ↘ Spec (.of baseField)) := curve.curve.smoothOfRelativeDimension

local instance curveGeometricallyIntegralHom :
    GeometricallyIntegral curve.curve.carrier.hom := by
  letI : Smooth curve.curve.carrier.hom := SmoothOfRelativeDimension.smooth 1 _
  exact Smooth.geometricallyIntegral curve.curve.carrier.hom

local instance curveGeometricallyIntegral :
    GeometricallyIntegral (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  inferInstanceAs (GeometricallyIntegral curve.curve.carrier.hom)

local instance fieldProductOver :
    (pullback curve.curve.carrier.hom
      (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))).hom).Over
        (Spec (.of extensionField)) :=
  ⟨pullback.snd curve.curve.carrier.hom (Over.mk fieldMap).hom⟩

local instance fieldProductProper :
    IsProper (pullback.snd curve.curve.carrier.hom
      (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))).hom) :=
  MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance

local instance fieldProductSmooth :
    SmoothOfRelativeDimension 1 (pullback.snd curve.curve.carrier.hom
      (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))).hom) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (IsPullback.of_hasPullback curve.curve.carrier.hom (Over.mk fieldMap).hom) inferInstance

local instance fieldProductGeometricallyIntegral :
    GeometricallyIntegral (pullback.snd curve.curve.carrier.hom
      (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))).hom) :=
  MorphismProperty.pullback_snd (P := @GeometricallyIntegral) _ _ inferInstance

local instance fieldProductProperOver :
    IsProper ((pullback curve.curve.carrier.hom
      (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))).hom) ↘
        Spec (.of extensionField)) :=
  inferInstanceAs (IsProper (pullback.snd curve.curve.carrier.hom (Over.mk fieldMap).hom))

local instance fieldProductSmoothOver :
    SmoothOfRelativeDimension 1 ((pullback curve.curve.carrier.hom
      (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))).hom) ↘
        Spec (.of extensionField)) :=
  inferInstanceAs (SmoothOfRelativeDimension 1
    (pullback.snd curve.curve.carrier.hom (Over.mk fieldMap).hom))

local instance fieldProductGeometricallyIntegralOver :
    GeometricallyIntegral ((pullback curve.curve.carrier.hom
      (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))).hom) ↘
        Spec (.of extensionField)) :=
  inferInstanceAs (GeometricallyIntegral
    (pullback.snd curve.curve.carrier.hom (Over.mk fieldMap).hom))

local instance fieldBaseSubsingleton :
    Subsingleton (Over.mk (fieldMap (baseField := baseField)
      (extensionField := extensionField))).left :=
  inferInstanceAs (Subsingleton (PrimeSpectrum extensionField))

local instance fieldBaseIntegral :
    IsIntegral (Over.mk (fieldMap (baseField := baseField)
      (extensionField := extensionField))).left :=
  inferInstanceAs (IsIntegral (Spec (.of extensionField)))

local instance fieldProductIntegral : IsIntegral (pullback curve.curve.carrier.hom
    (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))).hom) :=
  GeometricallyIntegral.isIntegral_of_subsingleton
    (pullback.snd curve.curve.carrier.hom (Over.mk fieldMap).hom)

private theorem toPicardFunctor_field_injective : Function.Injective
    ((toPicardFunctor curve.curve.carrier.hom).app
      (op (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))))) := by
  intro firstClass secondClass equality
  let parameter : Over (Spec (.of baseField)) :=
    Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))
  letI : Subsingleton parameter.left.Pic :=
    inferInstanceAs (Subsingleton (Spec (.of extensionField)).Pic)
  let comparison := normalizedPicardIso curve.point.left (by simpa using Over.w curve.point)
  let firstNormalized : (picardFunctorNormalized curve.curve.carrier.hom curve.point.left
      (by simpa using Over.w curve.point)).toFunctor.obj (op parameter) :=
    ⟨firstClass, Subsingleton.elim _ _⟩
  let secondNormalized : (picardFunctorNormalized curve.curve.carrier.hom curve.point.left
      (by simpa using Over.w curve.point)).toFunctor.obj (op parameter) :=
    ⟨secondClass, Subsingleton.elim _ _⟩
  have normalizedEquality : comparison.hom.app (op parameter) firstNormalized =
      comparison.hom.app (op parameter) secondNormalized := equality
  exact congrArg Subtype.val
    ((ConcreteCategory.bijective_of_isIso (comparison.hom.app (op parameter))).injective
      normalizedEquality)

private theorem fieldDivisor_degree (degree : ℕ)
    (divisor : (hilbertPresheaf curve.curve.carrier.hom degree).obj
      (op (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))))) :
    divisor.1.toModulesᵛ.degree extensionField = degree := by
  have degreeAtPoint := (abelClass_mem curve.curve.carrier.hom divisor) extensionField
    (𝟙 (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))))
  rw [picardFibreDegree, baseChangeMap_id, Pic.map_id] at degreeAtPoint
  exact (degree_congr extensionField (abelClassIso curve.curve.carrier.hom divisor)).symm.trans
    degreeAtPoint

private theorem fieldDivisor_h0_one_lt
    (divisor : (hilbertPresheaf curve.curve.carrier.hom
      (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)).obj
        (op (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))))) :
    1 < Module.finrank extensionField (divisor.1.toModulesᵛ.H 0) := by
  letI := divisor.2.isInvertible.isInvertible_dual_toModules
  have degreeEquation := fieldDivisor_degree curve _ divisor
  have genusEquation : (pullback curve.curve.carrier.hom
      (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))).hom).arithmeticGenus
        extensionField = curve.curve.carrier.left.arithmeticGenus baseField :=
    arithmeticGenus_pullback extensionField
  have canonicalBound : 2 * ((pullback curve.curve.carrier.hom
      (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))).hom).arithmeticGenus
        extensionField : ℤ) - 2 < divisor.1.toModulesᵛ.degree extensionField := by
    rw [genusEquation, degreeEquation]
    omega
  have dimensions := finrankH_zero_eq_degree_add_one_sub_genus
    divisor.1.toModulesᵛ canonicalBound
  rw [degreeEquation, genusEquation] at dimensions
  change 1 < divisor.1.toModulesᵛ.finrankH extensionField 0
  omega

private theorem fieldMap_image_eq
    {hilbertScheme picardScheme : Over (Spec (.of baseField))}
    (hilbertRepresentation : (hilbertPresheaf curve.curve.carrier.hom
      (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)).RepresentableBy hilbertScheme)
    (picardRepresentation : (picardFunctorDegree curve.curve.carrier.hom 0).obj.RepresentableBy
      picardScheme)
    (variety : AbelianVariety baseField) (morphism : hilbertScheme ⟶ variety.group.X)
    (first second : Over.mk (fieldMap (baseField := baseField)
      (extensionField := extensionField)) ⟶ hilbertScheme)
    (sameFibre : first ≫ translatedAbelMap curve.curve
        (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)
        (curve.pointIdealClass ^ (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))
        (curve.degreeHom_pointIdealClass_pow _) hilbertRepresentation picardRepresentation =
      second ≫ translatedAbelMap curve.curve
        (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)
        (curve.pointIdealClass ^ (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))
        (curve.degreeHom_pointIdealClass_pow _) hilbertRepresentation picardRepresentation) :
    first ≫ morphism = second ≫ morphism := by
  let degree := 2 * curve.curve.carrier.left.arithmeticGenus baseField + 1
  let firstDivisor := hilbertRepresentation.homEquiv first
  let secondDivisor := hilbertRepresentation.homEquiv second
  have fullClassEquality := congrArg
    (fun point ↦ (picardFunctorDegreeι curve.curve.carrier.hom 0).hom.app
      (op (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))))
        (picardRepresentation.homEquiv point)) sameFibre
  rw [translatedAbelMap_classifies, translatedAbelMap_classifies] at fullClassEquality
  have divisorClasses : abelClass curve.curve.carrier.hom firstDivisor =
      abelClass curve.curve.carrier.hom secondDivisor :=
    mul_right_cancel (toPicardFunctor_field_injective curve fullClassEquality)
  obtain ⟨firstSection, secondSection, firstIdeal, secondIdeal, _, _, firstNonzero,
      secondNonzero⟩ := exists_nonzero_sections_of_abelClass_eq
        curve.curve.carrier.hom firstDivisor secondDivisor divisorClasses
  let lineBundle := firstDivisor.1.toModulesᵛ
  letI : lineBundle.IsInvertible := firstDivisor.2.isInvertible.isInvertible_dual_toModules
  obtain ⟨companion, firstIndependent, secondIndependent⟩ :=
    Module.exists_linearIndependent_pair_companion (fieldDivisor_h0_one_lt curve firstDivisor)
      firstNonzero secondNonzero
  let companionSection : unit (pullback curve.curve.carrier.hom
      (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField))).hom) ⟶ lineBundle :=
    (H.unitHomAddEquiv lineBundle).symm companion
  have companionClass : H.unitHomAddEquiv lineBundle companionSection = companion :=
    (H.unitHomAddEquiv lineBundle).apply_symm_apply companion
  have firstCompanion : LinearIndependent extensionField
      ![H.unitHomAddEquiv lineBundle firstSection,
        H.unitHomAddEquiv lineBundle companionSection] := by
    rw [companionClass]
    exact firstIndependent
  have secondCompanion : LinearIndependent extensionField
      ![H.unitHomAddEquiv lineBundle secondSection,
        H.unitHomAddEquiv lineBundle companionSection] := by
    rw [companionClass]
    exact secondIndependent
  have degreeEquation : lineBundle.degree extensionField = degree :=
    fieldDivisor_degree curve degree firstDivisor
  let companionDivisor : (hilbertPresheaf curve.curve.carrier.hom degree).obj
      (op (Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField)))) :=
    (hilbertPresheaf curve.curve.carrier.hom degree).map (fieldEndpoint ⟨1⟩).op
      (fieldPencilPoint curve.curve degree lineBundle firstSection companionSection
        firstCompanion degreeEquation)
  have companionIdeal : companionDivisor.val = Scheme.Modules.Hom.zeroLocus companionSection := by
    dsimp only [companionDivisor]
    rw [fieldPencilPoint_endpoint_val, SectionPencil.projectiveLineIdeal_second]
  have firstEquality := independent_field_sections_image_eq curve.curve degree
    hilbertRepresentation variety morphism lineBundle firstSection companionSection firstCompanion
    degreeEquation firstDivisor companionDivisor firstIdeal.symm companionIdeal
  have secondEquality := independent_field_sections_image_eq curve.curve degree
    hilbertRepresentation variety morphism lineBundle secondSection companionSection secondCompanion
    degreeEquation secondDivisor companionDivisor secondIdeal.symm companionIdeal
  let pointEquivalence := hilbertRepresentation.homEquiv
    (X := Over.mk (fieldMap (baseField := baseField) (extensionField := extensionField)))
  exact (congrArg (fun point ↦ point ≫ morphism)
    (pointEquivalence.symm_apply_apply first)).symm.trans
      ((firstEquality.trans secondEquality.symm).trans
        (congrArg (fun point ↦ point ≫ morphism) (pointEquivalence.symm_apply_apply second)))

/-- Every abelian-valued morphism on the degree-`2g+1` Hilbert scheme is constant
on each translated-Abel fibre at every field-valued test, as equality of morphisms. -/
theorem translatedAbelMap_field_image_eq
    {hilbertScheme picardScheme : Over (Spec (.of baseField))}
    (hilbertRepresentation : (hilbertPresheaf curve.curve.carrier.hom
      (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)).RepresentableBy hilbertScheme)
    (picardRepresentation : (picardFunctorDegree curve.curve.carrier.hom 0).obj.RepresentableBy
      picardScheme)
    (variety : AbelianVariety baseField) (morphism : hilbertScheme ⟶ variety.group.X)
    (testField : Type u) [Field testField]
    (baseMap : Spec (.of testField) ⟶ Spec (.of baseField))
    (first second : Over.mk baseMap ⟶ hilbertScheme)
    (sameFibre : first ≫ translatedAbelMap curve.curve
        (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)
        (curve.pointIdealClass ^ (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))
        (curve.degreeHom_pointIdealClass_pow _) hilbertRepresentation picardRepresentation =
      second ≫ translatedAbelMap curve.curve
        (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)
        (curve.pointIdealClass ^ (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))
        (curve.degreeHom_pointIdealClass_pow _) hilbertRepresentation picardRepresentation) :
    first ≫ morphism = second ≫ morphism := by
  letI : Algebra baseField testField := (Spec.preimage baseMap).hom.toAlgebra
  have baseMapEquation : (fieldMap (baseField := baseField) (extensionField := testField)) =
      baseMap := Spec.map_preimage baseMap
  have canonical : ∀ mapToBase : Spec (.of testField) ⟶ Spec (.of baseField),
      mapToBase = (fieldMap (baseField := baseField) (extensionField := testField)) →
        ∀ firstPoint secondPoint : Over.mk mapToBase ⟶ hilbertScheme,
          firstPoint ≫ translatedAbelMap curve.curve
              (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)
              (curve.pointIdealClass ^ (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))
              (curve.degreeHom_pointIdealClass_pow _) hilbertRepresentation picardRepresentation =
            secondPoint ≫ translatedAbelMap curve.curve
              (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)
              (curve.pointIdealClass ^ (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))
              (curve.degreeHom_pointIdealClass_pow _) hilbertRepresentation picardRepresentation →
          firstPoint ≫ morphism = secondPoint ≫ morphism := by
    intro mapToBase equation
    subst mapToBase
    exact fieldMap_image_eq (extensionField := testField) curve hilbertRepresentation
      picardRepresentation variety morphism
  exact canonical baseMap baseMapEquation.symm first second sameFibre

/-- The actual ordered sum descends to the Hilbert scheme, and its descent is constant
on every translated-Abel field fibre. No fibre-constancy condition is an input. -/
theorem exists_abelianSum_descent_fieldConstancy
    {hilbertScheme picardScheme : Over (Spec (.of baseField))}
    (hilbertRepresentation : (hilbertPresheaf curve.curve.carrier.hom
      (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)).RepresentableBy hilbertScheme)
    (picardRepresentation : (picardFunctorDegree curve.curve.carrier.hom 0).obj.RepresentableBy
      picardScheme)
    (variety : AbelianVariety baseField) (curveMap : curve.curve.carrier ⟶ variety.group.X) :
    ∃ morphism : hilbertScheme ⟶ variety.group.X,
      OrderedDivisors.map curve.curve.carrier.hom hilbertRepresentation ≫ morphism =
        OrderedDivisors.abelianSum curve.curve variety.group curveMap
          (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1) ∧
      ∀ (testField : Type u) [Field testField]
        (baseMap : Spec (.of testField) ⟶ Spec (.of baseField))
        (first second : Over.mk baseMap ⟶ hilbertScheme),
        first ≫ translatedAbelMap curve.curve
            (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)
            (curve.pointIdealClass ^ (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))
            (curve.degreeHom_pointIdealClass_pow _) hilbertRepresentation picardRepresentation =
          second ≫ translatedAbelMap curve.curve
            (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)
            (curve.pointIdealClass ^ (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))
            (curve.degreeHom_pointIdealClass_pow _) hilbertRepresentation picardRepresentation →
          first ≫ morphism = second ≫ morphism := by
  obtain ⟨morphism, orderedEquation, -⟩ := OrderedDivisors.existsUnique_abelianSum_descent
    curve.curve curve.point (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)
    hilbertRepresentation variety.group curveMap
  exact ⟨morphism, orderedEquation, translatedAbelMap_field_image_eq curve
    hilbertRepresentation picardRepresentation variety morphism⟩

end FieldConstancy

end AlgebraicGeometry.Hilbert
