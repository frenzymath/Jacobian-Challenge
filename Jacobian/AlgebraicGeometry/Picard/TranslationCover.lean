import Jacobian.AlgebraicGeometry.Curve.CohomologyRank
import Jacobian.AlgebraicGeometry.Curve.Twisting
import Jacobian.AlgebraicGeometry.Picard.CohomologyChart
import Jacobian.AlgebraicGeometry.Picard.Field

/-!
# Translates of the Picard cohomology chart

Over a separably closed field, every normalized Picard class over a field
extension can be translated into the cohomology chart by a class over the
ground field. The translating class comes from a line bundle on the original
curve, and its normalization follows from the triviality of the Picard group
of the ground field.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme

variable {baseField : Type schemeUniverse} [Field baseField]
  {sourceScheme : Scheme.{schemeUniverse}}

local instance translationCoverSmooth (structureMap : sourceScheme ⟶ Spec (.of baseField))
    [SmoothOfRelativeDimension 1 structureMap] : Smooth structureMap :=
  SmoothOfRelativeDimension.smooth 1 structureMap

/-- Every field-valued normalized Picard class can be translated into the
cohomology chart by a normalized class defined over the ground field. -/
theorem exists_mul_mem_picardFunctorInvertibleDirectImage
    [sourceScheme.Over (Spec (.of baseField))]
    [SmoothOfRelativeDimension 1 (sourceScheme ↘ Spec (.of baseField))]
    [IsProper (sourceScheme ↘ Spec (.of baseField))]
    [GeometricallyIntegral (sourceScheme ↘ Spec (.of baseField))]
    [IsSepClosed baseField]
    [∀ parameter : Over (Spec (.of baseField)),
      HasInjectiveResolutions
        (Limits.pullback (sourceScheme ↘ Spec (.of baseField)) parameter.hom).Modules]
    (sectionMorphism : Spec (.of baseField) ⟶ sourceScheme)
    (sectionCondition : sectionMorphism ≫ sourceScheme ↘ Spec (.of baseField) = 𝟙 _)
    (extensionField : Type schemeUniverse) [Field extensionField]
    [Algebra baseField extensionField]
    (coefficientClass :
      (picardFunctorNormalizedGrp (sourceScheme ↘ Spec (.of baseField))
        sectionMorphism sectionCondition).obj
          (.op (Over.mk (Spec.map (CommRingCat.ofHom
            (algebraMap baseField extensionField)))))) :
    ∃ groundClass :
        (picardFunctorNormalizedGrp (sourceScheme ↘ Spec (.of baseField))
          sectionMorphism sectionCondition).obj (.op (Over.mk (𝟙 (Spec (.of baseField))))),
      ((picardFunctorNormalizedGrp (sourceScheme ↘ Spec (.of baseField))
          sectionMorphism sectionCondition).map
        (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))
          (Category.comp_id _) :
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) ⟶
              Over.mk (𝟙 (Spec (.of baseField)))).op).hom groundClass * coefficientClass ∈
        (picardFunctorInvertibleDirectImage (sourceScheme ↘ Spec (.of baseField))
          sectionMorphism sectionCondition).obj
            (.op (Over.mk (Spec.map (CommRingCat.ofHom
              (algebraMap baseField extensionField))))) := by
  let projection := sourceScheme ↘ Spec (.of baseField)
  let fieldMap := Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))
  let fieldParameter := Over.mk fieldMap
  let groundParameter := Over.mk (𝟙 (Spec (.of baseField)))
  let restriction : fieldParameter ⟶ groundParameter :=
    Over.homMk fieldMap (Category.comp_id _)
  let normalizedGroup := picardFunctorNormalizedGrp projection sectionMorphism sectionCondition
  obtain ⟨twist, twistInvertible, dimensionZero, dimensionOne⟩ :=
    Modules.exists_isInvertible_twist extensionField
      ((fromSkeleton _).obj coefficientClass.1.val)
  letI := twistInvertible
  let translatingClass :=
    Pic.mk ((Modules.pullback (Limits.pullback.fst projection groundParameter.hom)).obj twist)
  have normalized :
      Pic.mapHom (sectionBaseChange projection sectionMorphism sectionCondition groundParameter)
        translatingClass = 1 := by
    haveI : Subsingleton groundParameter.left.Pic := by
      change Subsingleton (Spec (.of baseField)).Pic
      exact Pic.subsingleton_spec_field baseField
    exact Subsingleton.elim _ _
  let groundClass : normalizedGroup.obj (.op groundParameter) := ⟨translatingClass, normalized⟩
  refine ⟨groundClass, ?_⟩
  change IsInvertibleDirectImage projection fieldParameter
    (Pic.map (baseChangeMap projection restriction) translatingClass * coefficientClass.1)
  have projectionCondition :
      baseChangeMap projection restriction ≫ Limits.pullback.fst projection groundParameter.hom =
        Limits.pullback.fst projection fieldParameter.hom :=
    Limits.pullback.lift_fst _ _ _
  let pullbackComparison :
      (fromSkeleton _).obj
          (Pic.map (baseChangeMap projection restriction) translatingClass).val ≅
        (Modules.pullback (Limits.pullback.fst projection fieldParameter.hom)).obj twist :=
    Pic.mkIso _ ≪≫
      (Modules.pullback _).mapIso (Pic.mkIso _) ≪≫
      (Modules.pullbackComp _ _).app twist ≪≫
      (Modules.pullbackCongr projectionCondition).app twist
  let tensorComparison :
      (fromSkeleton _).obj
          (Pic.map (baseChangeMap projection restriction) translatingClass *
            coefficientClass.1).val ≅
        (fromSkeleton _).obj coefficientClass.1.val ⊗
          (Modules.pullback (Limits.pullback.fst projection fieldParameter.hom)).obj twist :=
    Pic.mulIso _ _ ≪≫ (pullbackComparison ⊗ᵢ Iso.refl _) ≪≫ β_ _ _
  letI : (Limits.pullback projection fieldParameter.hom).Over (Spec (.of extensionField)) :=
    ⟨Limits.pullback.snd projection fieldParameter.hom⟩
  letI : SmoothOfRelativeDimension 1
      (Limits.pullback projection fieldParameter.hom ↘ Spec (.of extensionField)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback projection fieldParameter.hom) inferInstance
  letI : IsProper
      (Limits.pullback projection fieldParameter.hom ↘ Spec (.of extensionField)) :=
    MorphismProperty.pullback_snd projection fieldParameter.hom inferInstance
  letI : GeometricallyIrreducible
      (Limits.pullback projection fieldParameter.hom ↘ Spec (.of extensionField)) :=
    MorphismProperty.pullback_snd projection fieldParameter.hom inferInstance
  have singleDegree := Modules.isFiniteLocallyFreeInDegree_higherDirectImage_of_finrankH
    (baseField := extensionField) (source := Limits.pullback projection fieldParameter.hom)
    ((fromSkeleton _).obj
      (Pic.map (baseChangeMap projection restriction) translatingClass * coefficientClass.1).val)
    ((Modules.finrankH_congr extensionField tensorComparison 0).trans dimensionZero)
    ((Modules.finrankH_congr extensionField tensorComparison 1).trans dimensionOne)
  obtain ⟨vanishing, invertible⟩ :=
    (Modules.isFiniteLocallyFreeInDegree_zero_one_iff _).mp singleDegree
  exact ⟨invertible, fun degree positive ↦ vanishing degree positive.ne'⟩

end AlgebraicGeometry
