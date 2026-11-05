import Jacobian.AlgebraicGeometry.Picard.ChartRepresentability
import Jacobian.AlgebraicGeometry.Hilbert.CurveGeometry
import Jacobian.AlgebraicGeometry.Picard.RationalPoint
import Jacobian.AlgebraicGeometry.Picard.TranslationCover
import Jacobian.AlgebraicGeometry.Group.Representability
import Jacobian.AlgebraicGeometry.Curve.Twisting

/-!
# Smoothness of the Picard scheme of a curve

The cohomology chart is an open subscheme of the smooth genus Hilbert scheme.
Translations of this chart cover every representative of the Picard sheaf, so
that representative is smooth of relative dimension equal to the genus.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {baseField : Type u} [Field baseField] [IsSepClosed baseField]
  {source : Scheme.{u}} [source.Over (Spec (.of baseField))]
  [IsProper (source ↘ Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
  [GeometricallyIntegral (source ↘ Spec (.of baseField))]

/-- A representative of the Picard sheaf of a smooth proper geometrically
integral curve over a separably closed field is smooth of genus dimension. -/
theorem smoothOfRelativeDimension_of_representableBy_picardFunctor
    (representative : Over (Spec (.of baseField)))
    (representation : (picardFunctor (source ↘ Spec (.of baseField))).obj.RepresentableBy
      representative) :
    SmoothOfRelativeDimension (source.arithmeticGenus baseField) representative.hom := by
  let structureMap : source ⟶ Spec (.of baseField) := source ↘ Spec (.of baseField)
  letI : ∀ parameter : Over (Spec (.of baseField)),
      HasInjectiveResolutions (pullback structureMap parameter.hom).Modules :=
    fun parameter ↦ by
      have := Modules.isGrothendieckAbelian (pullback structureMap parameter.hom)
      infer_instance
  letI : Smooth structureMap := SmoothOfRelativeDimension.smooth 1 structureMap
  letI : IsIntegral source := GeometricallyIntegral.isIntegral_of_subsingleton structureMap
  obtain ⟨sectionMap, sectionEquation⟩ := structureMap.exists_section_of_isSepClosed
  obtain ⟨hilbertScheme, hilbertProjection, hilbertSmooth, _, _, ⟨hilbertRepresentation⟩⟩ :=
    hilbertPresheaf_curve_representable structureMap (source.arithmeticGenus baseField)
  letI := hilbertSmooth
  obtain ⟨chartScheme, chartInclusion, chartOpen, ⟨chartRepresentation⟩⟩ :=
    isRepresentable_picardFunctorInvertibleDirectImage sectionMap sectionEquation
      (Over.mk hilbertProjection) hilbertRepresentation
  letI := chartOpen
  let normalizedRepresentation :
      (picardFunctorNormalizedGrp structureMap sectionMap sectionEquation ⋙
        forget GrpCat.{u + 1}).RepresentableBy representative :=
    representation.ofIso (normalizedPicardIso sectionMap sectionEquation).symm
  choose chartMap chartMapOpen point_mem using fun point : representative.left ↦
    exists_isOpenImmersion_of_representable_open_subfunctor _ _ chartRepresentation
      (isOpenImmersion_picardFunctorInvertibleDirectImage_ι structureMap
        sectionMap sectionEquation)
      (exists_mul_mem_picardFunctorInvertibleDirectImage sectionMap sectionEquation)
      normalizedRepresentation point
  letI : ∀ point, IsOpenImmersion (chartMap point).left := chartMapOpen
  let chartCover : representative.left.OpenCover :=
    { I₀ := representative.left
      X _ := chartScheme
      f point := (chartMap point).left
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun point ↦ ⟨point, point_mem point⟩, inferInstance⟩ }
  refine IsZariskiLocalAtSource.of_openCover chartCover fun point ↦ ?_
  change SmoothOfRelativeDimension (source.arithmeticGenus baseField)
    ((chartMap point).left ≫ representative.hom)
  rw [Over.w (chartMap point)]
  have chartSmooth := smoothOfRelativeDimension_comp
    (n := 0) (m := source.arithmeticGenus baseField) chartInclusion hilbertProjection
  rwa [zero_add] at chartSmooth

end AlgebraicGeometry
