import Jacobian.AlgebraicGeometry.Cohomology.FiberBaseChange
import Jacobian.AlgebraicGeometry.Cohomology.FiberField
import Jacobian.AlgebraicGeometry.Curve.DivisorDegree
import Jacobian.AlgebraicGeometry.Curve.LineBundleDegree
import Jacobian.AlgebraicGeometry.IdealSheaf.FiniteFlat
import Jacobian.AlgebraicGeometry.Modules.Discrete
import Jacobian.AlgebraicGeometry.Picard.CohomologyChart
import Jacobian.AlgebraicGeometry.Picard.ZeroScheme

/-!
# The evaluation divisor of the Picard cohomology chart

On a proper smooth geometrically integral curve, evaluation of a line bundle
in the cohomology chart cuts out a finite flat divisor whose rank is the genus.
For normalized classes, this construction gives a natural componentwise
injective map into the genus Hilbert presheaf. The normalized Abel map recovers
the original class from its evaluation divisor.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme

local instance hilbertChartSmooth {source target : Scheme.{u}} (structureMap : source ⟶ target)
    [SmoothOfRelativeDimension 1 structureMap] : Smooth structureMap :=
  SmoothOfRelativeDimension.smooth 1 structureMap

variable {baseField : Type u} [Field baseField] {sourceScheme : Scheme.{u}}
  [sourceScheme.Over (Spec (.of baseField))]
  [IsProper (sourceScheme ↘ Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (sourceScheme ↘ Spec (.of baseField))]
  [GeometricallyIntegral (sourceScheme ↘ Spec (.of baseField))]
  [∀ parameter : Over (Spec (.of baseField)),
    HasInjectiveResolutions (pullback (sourceScheme ↘ Spec (.of baseField)) parameter.hom).Modules]

/-- The evaluation divisor of a cohomology-chart class has genus rank on every
residue-field fibre of its parameter scheme. -/
theorem IsInvertibleDirectImage.finrank_zeroLocus_directImageCounit
    (parameter : Over (Spec (.of baseField)))
    (lineBundle : (pullback (sourceScheme ↘ Spec (.of baseField)) parameter.hom).Pic)
    (membership : IsInvertibleDirectImage (sourceScheme ↘ Spec (.of baseField))
      parameter lineBundle) (point : parameter.left) :
    letI := IsInvertibleDirectImage.isInvertible_pushforward
      (sourceScheme ↘ Spec (.of baseField)) parameter lineBundle membership
    ((Pic.directImageCounit (sourceScheme ↘ Spec (.of baseField))
      parameter lineBundle).zeroLocus.subschemeι ≫
        pullback.snd (sourceScheme ↘ Spec (.of baseField)) parameter.hom).finrank point =
      sourceScheme.arithmeticGenus baseField := by
  let structureMap := sourceScheme ↘ Spec (.of baseField)
  let projection := pullback.snd structureMap parameter.hom
  let representative := (fromSkeleton _).obj lineBundle.val
  letI : representative.IsInvertible := lineBundle.isInvertible
  let directImage := (Modules.pushforward projection).obj representative
  letI : directImage.IsInvertible :=
    IsInvertibleDirectImage.isInvertible_pushforward structureMap parameter lineBundle membership
  let evaluation := Pic.directImageCounit structureMap parameter lineBundle
  let divisor := evaluation.zeroLocus
  let residueField := parameter.left.residueField point
  let fibreMap := projection.fiberι point
  letI := projection.fiberOverSpecResidueField point
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  letI : SmoothOfRelativeDimension 1 projection :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  letI : IsProper projection :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  letI : GeometricallyIntegral projection := inferInstance
  letI : SmoothOfRelativeDimension 1 (projection.fiber point ↘ Spec (.of residueField)) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  letI : IsProper (projection.fiber point ↘ Spec (.of residueField)) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  letI : GeometricallyIntegral (projection.fiber point ↘ Spec (.of residueField)) :=
    MorphismProperty.pullback_snd (P := @GeometricallyIntegral) _ _ inferInstance
  obtain ⟨_, finite, flat, _⟩ :=
    IsInvertibleDirectImage.isInvertible_zeroLocus_directImageCounit_and_isFinite
      structureMap parameter lineBundle membership
  letI : IsFinite (divisor.subschemeι ≫ projection) := finite
  letI : Flat (divisor.subschemeι ≫ projection) := flat
  have fibreRegular : (divisor.comap fibreMap).IsInvertible := by
    rw [Modules.Hom.comap_zeroLocus]
    exact Modules.Hom.isInvertible_zeroLocus
      (IsInvertibleDirectImage.pullback_fiberι_directImageCounit_ne_zero
        structureMap parameter lineBundle membership point)
  letI : (divisor.comap fibreMap).toModules.IsInvertible := fibreRegular.isInvertible_toModules
  letI : IsFinite ((divisor.comap fibreMap).subschemeι ≫
      (projection.fiber point ↘ Spec (.of residueField))) :=
    divisor.isFinite_comap_fiberι projection point
  have divisorDegree := fibreRegular.degree_dual_toModules (baseField := residueField)
  have zeroLocusEquation : ((Modules.pullback fibreMap).map evaluation).zeroLocus =
      divisor.comap fibreMap := (Modules.Hom.comap_zeroLocus fibreMap evaluation).symm
  obtain ⟨comparison⟩ := Modules.Hom.nonempty_iso_dual_toModules_tensorObj
    ((Modules.pullback fibreMap).map evaluation)
      (by rwa [← Modules.Hom.comap_zeroLocus])
  rw [zeroLocusEquation] at comparison
  have degreeAdditivity := Modules.degree_tensorObj (k := residueField)
    (divisor.comap fibreMap).toModulesᵛ
    ((Modules.pullback fibreMap).obj ((Modules.pullback projection).obj directImage))
  rw [← Modules.degree_congr residueField comparison] at degreeAdditivity
  have baseDegree : ((Modules.pullback fibreMap).obj
      ((Modules.pullback projection).obj directImage)).degree residueField = 0 := by
    obtain ⟨unitIso⟩ := Modules.nonempty_iso_unit_of_discrete
      ((Modules.pullback (parameter.left.fromSpecResidueField point)).obj directImage)
    exact (Modules.degree_congr residueField
      ((Modules.pullbackComp fibreMap projection).app directImage ≪≫
        (Modules.pullbackCongr (projection.fiber_fac point)).app directImage ≪≫
        ((Modules.pullbackComp _ _).app directImage).symm ≪≫
        (Modules.pullback _).mapIso unitIso ≪≫ Modules.pullbackObjUnitIso _)).trans
      (Modules.degree_unit residueField)
  obtain ⟨rankOpen, rankOpen_eq, universal⟩ :=
    Modules.exists_opens_range_subset_iff_isFiniteLocallyFreeInDegree projection representative
      (Modules.isFlatOver_of_isInvertible projection representative) 0 1
  have singleDegree : Modules.IsFiniteLocallyFreeInDegree
      (fun degree ↦ (Modules.higherDirectImage projection degree).obj representative) 0 1 :=
    (Modules.isFiniteLocallyFreeInDegree_zero_one_iff _).2
      ⟨fun degree nonzero ↦ membership.2 degree (Nat.pos_of_ne_zero nonzero), membership.1⟩
  have identityCondition := singleDegree.of_iso fun degree ↦
    (Modules.higherDirectImage projection degree).mapIso
      ((Modules.pullbackId _).app representative).symm
  have rangeSubset := (universal (𝟙 parameter.left) (𝟙 _) projection
    (IsPullback.id_horiz projection)).2 identityCondition
  have fibreRanks : (∀ degree ≠ 0, representative.hFiber projection degree point = 0) ∧
      representative.hFiber projection 0 point = 1 := by
    have member := rangeSubset ⟨point, rfl⟩
    rw [rankOpen_eq] at member
    exact member
  have fibreEuler : ((Modules.pullback fibreMap).obj representative).eulerChar residueField =
      1 := by
    change representative.eulerCharFiber projection point = 1
    rw [Modules.eulerCharFiber, finsum_eq_single _ 0
      (fun degree nonzero ↦ by simp [fibreRanks.1 degree nonzero])]
    simp [fibreRanks.2]
  let curve : Curve baseField :=
    { carrier := Over.mk structureMap
      isProper := inferInstanceAs (IsProper structureMap)
      smoothOfRelativeDimension := inferInstanceAs (SmoothOfRelativeDimension 1 structureMap)
      geometricallyIrreducible := inferInstanceAs (GeometricallyIrreducible structureMap) }
  have unitEuler : (Modules.unit (projection.fiber point)).eulerChar residueField =
      1 - (sourceScheme.arithmeticGenus baseField : ℤ) := by
    calc
      _ = ((Modules.pullback fibreMap).obj
          (Modules.unit (pullback structureMap parameter.hom))).eulerChar residueField :=
        (Modules.eulerChar_congr residueField (Modules.pullbackObjUnitIso fibreMap)).symm
      _ = (Modules.unit (pullback structureMap parameter.hom)).eulerCharFiber
          projection point := rfl
      _ = ((Modules.pullback (pullback.fst structureMap parameter.hom)).obj
          (Modules.unit sourceScheme)).eulerCharFiber projection point :=
        (congrFun (Modules.eulerCharFiber_congr
          (Modules.pullbackObjUnitIso (pullback.fst structureMap parameter.hom)) projection)
            point).symm
      _ = (Modules.unit sourceScheme).eulerCharFiber structureMap (parameter.hom point) :=
        Modules.eulerCharFiber_pullback_of_isPullback structureMap (Modules.unit sourceScheme)
          parameter.hom (pullback.fst structureMap parameter.hom) projection
          (IsPullback.of_hasPullback structureMap parameter.hom) point
      _ = (Modules.unit sourceScheme).eulerChar baseField :=
        Modules.eulerCharFiber_eq_eulerChar structureMap _ _
      _ = _ := Modules.eulerChar_unit_eq_one_sub_genus (k := baseField)
        (fun degree larger ↦ curve.subsingleton_H _ larger)
  have fibreDegree : ((Modules.pullback fibreMap).obj representative).degree residueField =
      (sourceScheme.arithmeticGenus baseField : ℤ) := by
    rw [Modules.degree, fibreEuler, unitEuler]
    ring
  change (divisor.subschemeι ≫ projection).finrank point = _
  rw [Scheme.IdealSheafData.finrank_subschemeι_comp_eq_finrankΓ]
  have rankEquality :
      (((divisor.comap fibreMap).subschemeι ≫
        (projection.fiber point ↘ Spec (.of residueField))).finrankΓ : ℤ) =
      (sourceScheme.arithmeticGenus baseField : ℤ) := by
    linarith
  exact_mod_cast rankEquality

/-- The canonical evaluation divisor of a cohomology-chart class is a point
of the genus Hilbert presheaf. -/
theorem IsInvertibleDirectImage.isHilbertSubscheme_zeroLocus_directImageCounit
    (parameter : Over (Spec (.of baseField)))
    (lineBundle : (pullback (sourceScheme ↘ Spec (.of baseField)) parameter.hom).Pic)
    (membership : IsInvertibleDirectImage (sourceScheme ↘ Spec (.of baseField))
      parameter lineBundle) :
    letI := IsInvertibleDirectImage.isInvertible_pushforward
      (sourceScheme ↘ Spec (.of baseField)) parameter lineBundle membership
    IsHilbertSubscheme (sourceScheme ↘ Spec (.of baseField))
      (sourceScheme.arithmeticGenus baseField) parameter
      (Pic.directImageCounit (sourceScheme ↘ Spec (.of baseField)) parameter lineBundle).zeroLocus := by
  letI := IsInvertibleDirectImage.isInvertible_pushforward
    (sourceScheme ↘ Spec (.of baseField)) parameter lineBundle membership
  obtain ⟨_, finite, flat, finitePresentation⟩ :=
    IsInvertibleDirectImage.isInvertible_zeroLocus_directImageCounit_and_isFinite
      (sourceScheme ↘ Spec (.of baseField)) parameter lineBundle membership
  exact ⟨finite, flat, finitePresentation,
    IsInvertibleDirectImage.finrank_zeroLocus_directImageCounit parameter lineBundle membership⟩

variable (sectionMap : Spec (.of baseField) ⟶ sourceScheme)
  (sectionEquation : sectionMap ≫ sourceScheme ↘ Spec (.of baseField) = 𝟙 _)

/-- Send a normalized cohomology-chart class to its canonical genus-degree
evaluation divisor. -/
def invertibleDirectImageToHilbert :
    (picardFunctorInvertibleDirectImage (sourceScheme ↘ Spec (.of baseField))
      sectionMap sectionEquation).toFunctor ⟶
      hilbertPresheaf (sourceScheme ↘ Spec (.of baseField))
        (sourceScheme.arithmeticGenus baseField) ⋙ uliftFunctor.{u + 1, u} where
  app parameter := TypeCat.ofHom fun coefficient ↦ by
    letI := IsInvertibleDirectImage.isInvertible_pushforward
      (sourceScheme ↘ Spec (.of baseField)) parameter.unop coefficient.1.1 coefficient.2
    exact ULift.up ⟨_,
      IsInvertibleDirectImage.isHilbertSubscheme_zeroLocus_directImageCounit
        parameter.unop coefficient.1.1 coefficient.2⟩
  naturality parameter targetParameter restriction := by
    ext coefficient
    letI := IsInvertibleDirectImage.isInvertible_pushforward
      (sourceScheme ↘ Spec (.of baseField)) parameter.unop coefficient.1.1 coefficient.2
    letI := IsInvertibleDirectImage.isInvertible_pushforward
      (sourceScheme ↘ Spec (.of baseField)) targetParameter.unop
      (Pic.map (baseChangeMap (sourceScheme ↘ Spec (.of baseField)) restriction.unop)
        coefficient.1.1)
      (IsInvertibleDirectImage.map_of_isProper (sourceScheme ↘ Spec (.of baseField))
        restriction.unop coefficient.2)
    letI := IsInvertibleDirectImage.isIso_pushforwardBaseChange
      (sourceScheme ↘ Spec (.of baseField)) restriction.unop coefficient.2
    exact ULift.ext (Subtype.ext
      (comap_zeroLocus_directImageCounit (sourceScheme ↘ Spec (.of baseField))
        restriction.unop coefficient.1.1).symm)

/-- The dictionary uses the actual zero locus of the canonical evaluation map. -/
@[simp]
lemma invertibleDirectImageToHilbert_app_down_val
    (parameter : Over (Spec (.of baseField)))
    (coefficient : (picardFunctorInvertibleDirectImage (sourceScheme ↘ Spec (.of baseField))
      sectionMap sectionEquation).toFunctor.obj (op parameter)) :
    letI := IsInvertibleDirectImage.isInvertible_pushforward
      (sourceScheme ↘ Spec (.of baseField)) parameter coefficient.1.1 coefficient.2
    (((invertibleDirectImageToHilbert sectionMap sectionEquation).app
      (op parameter) coefficient).down).1 =
      (Pic.directImageCounit (sourceScheme ↘ Spec (.of baseField))
        parameter coefficient.1.1).zeroLocus := rfl

/-- The normalized Abel map recovers a chart class from its evaluation divisor. -/
theorem hilbertToPicardNormalized_invertibleDirectImageToHilbert
    (parameter : Over (Spec (.of baseField)))
    (coefficient : (picardFunctorInvertibleDirectImage (sourceScheme ↘ Spec (.of baseField))
      sectionMap sectionEquation).toFunctor.obj (op parameter)) :
    hilbertToPicardNormalized (sourceScheme ↘ Spec (.of baseField)) sectionMap sectionEquation
      (sourceScheme.arithmeticGenus baseField) parameter
      (((invertibleDirectImageToHilbert sectionMap sectionEquation).app
        (op parameter) coefficient).down) = coefficient.1 := by
  letI := IsInvertibleDirectImage.isInvertible_pushforward
    (sourceScheme ↘ Spec (.of baseField)) parameter coefficient.1.1 coefficient.2
  exact hilbertToPicardNormalized_zeroLocus (sourceScheme ↘ Spec (.of baseField))
    sectionMap sectionEquation (sourceScheme.arithmeticGenus baseField) parameter
    coefficient.1 _ rfl

/-- Evaluation divisors distinguish normalized cohomology-chart classes. -/
theorem injective_invertibleDirectImageToHilbert_app
    (parameter : (Over (Spec (.of baseField)))ᵒᵖ) :
    Function.Injective ((invertibleDirectImageToHilbert sectionMap sectionEquation).app
      parameter) := by
  intro firstClass secondClass equality
  apply Subtype.ext
  have normalizedEquality := congrArg
    (fun divisor : ULift.{u + 1, u}
        ((hilbertPresheaf (sourceScheme ↘ Spec (.of baseField))
          (sourceScheme.arithmeticGenus baseField)).obj parameter) ↦
      hilbertToPicardNormalized (sourceScheme ↘ Spec (.of baseField)) sectionMap sectionEquation
        (sourceScheme.arithmeticGenus baseField) parameter.unop divisor.down) equality
  have firstRecovery := hilbertToPicardNormalized_invertibleDirectImageToHilbert
    sectionMap sectionEquation parameter.unop firstClass
  have secondRecovery := hilbertToPicardNormalized_invertibleDirectImageToHilbert
    sectionMap sectionEquation parameter.unop secondClass
  exact firstRecovery.symm.trans (normalizedEquality.trans secondRecovery)

end AlgebraicGeometry
