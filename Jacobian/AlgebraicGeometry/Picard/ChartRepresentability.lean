import Jacobian.AlgebraicGeometry.IdealSheaf.CanonicalSection
import Jacobian.AlgebraicGeometry.Picard.HilbertChart
import Mathlib.RingTheory.Flat.LocallyFree

/-!
# Representing the Picard cohomology chart by a Hilbert open

The evaluation divisor and the normalized divisor class are inverse on the
cohomology chart. A closed inclusion between finite flat families of the same
rank is an isomorphism, so the evaluation divisor recovers each genus-degree
divisor whose normalized class lies in the chart. Consequently the chart is
represented by an open subscheme of any genus Hilbert scheme.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme

private theorem isIso_closedImmersion_of_equal_rank
    {smaller larger base : Scheme.{u}} (inclusion : smaller ⟶ larger)
    (projection : larger ⟶ base) [IsClosedImmersion inclusion] [IsFinite projection]
    [Flat projection] [Flat (inclusion ≫ projection)]
    (rankEquality : ∀ point, (inclusion ≫ projection).finrank point =
      projection.finrank point) : IsIso inclusion := by
  wlog baseIsSpec : ∃ baseRing, base = Spec baseRing with inductionHypothesis
  · rw [← MorphismProperty.isomorphisms.iff,
      IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms Scheme)
        (base.affineCover.pullback₁ projection)]
    intro chart
    let chartMap := base.affineCover.f chart
    change IsIso (pullback.snd inclusion (pullback.fst projection chartMap))
    have square : IsPullback (pullback.fst inclusion (pullback.fst projection chartMap))
        (pullback.snd inclusion (pullback.fst projection chartMap) ≫
          pullback.snd projection chartMap) (inclusion ≫ projection) chartMap :=
      (IsPullback.of_hasPullback inclusion (pullback.fst projection chartMap)).paste_vert
        (IsPullback.of_hasPullback projection chartMap)
    letI : Flat (pullback.snd inclusion (pullback.fst projection chartMap) ≫
        pullback.snd projection chartMap) := MorphismProperty.of_isPullback square inferInstance
    refine inductionHypothesis _ (pullback.snd projection chartMap)
      (fun point ↦ ?_) ⟨_, rfl⟩
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ square, rankEquality,
      Scheme.Hom.finrank_pullback_snd]
  obtain ⟨baseRing, rfl⟩ := baseIsSpec
  wlog largerIsSpec : ∃ largerRing, larger = Spec largerRing with inductionHypothesis
  · letI : IsAffine larger := isAffine_of_isAffineHom projection
    have equation : (inclusion ≫ larger.isoSpec.hom) ≫ larger.isoSpec.inv ≫ projection =
        inclusion ≫ projection := by simp
    letI : Flat ((inclusion ≫ larger.isoSpec.hom) ≫ larger.isoSpec.inv ≫ projection) := by
      rw [equation]
      infer_instance
    letI : IsIso (inclusion ≫ larger.isoSpec.hom) :=
      inductionHypothesis (baseRing := baseRing) (inclusion := inclusion ≫ larger.isoSpec.hom)
        (projection := larger.isoSpec.inv ≫ projection)
        (by
          rw [equation, Scheme.Hom.finrank_comp_left_of_isIso larger.isoSpec.inv]
          exact rankEquality) ⟨_, rfl⟩
    exact IsIso.of_isIso_comp_right inclusion larger.isoSpec.hom
  obtain ⟨largerRing, rfl⟩ := largerIsSpec
  wlog smallerIsSpec : ∃ smallerRing, smaller = Spec smallerRing with inductionHypothesis
  · letI : IsAffine smaller := isAffine_of_isAffineHom (inclusion ≫ projection)
    have equation : (smaller.isoSpec.inv ≫ inclusion) ≫ projection =
        smaller.isoSpec.inv ≫ inclusion ≫ projection := by simp
    letI : Flat ((smaller.isoSpec.inv ≫ inclusion) ≫ projection) := by
      rw [equation]
      infer_instance
    letI : IsIso (smaller.isoSpec.inv ≫ inclusion) :=
      inductionHypothesis (baseRing := baseRing) (largerRing := largerRing)
        (inclusion := smaller.isoSpec.inv ≫ inclusion) (projection := projection)
        (by
          rw [equation, Scheme.Hom.finrank_comp_left_of_isIso smaller.isoSpec.inv]
          exact rankEquality) ⟨_, rfl⟩
    exact IsIso.of_isIso_comp_left smaller.isoSpec.inv inclusion
  obtain ⟨smallerRing, rfl⟩ := smallerIsSpec
  obtain ⟨scalarMap, rfl⟩ := Spec.map_surjective projection
  obtain ⟨quotientMap, rfl⟩ := Spec.map_surjective inclusion
  rw [← Spec.map_comp] at rankEquality
  have quotientSurjective : Function.Surjective quotientMap := by
    obtain ⟨_, sectionsSurjective⟩ :=
      IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map quotientMap)
    intro sectionValue
    obtain ⟨preimage, preimageEquation⟩ :=
      sectionsSurjective ((Scheme.ΓSpecIso smallerRing).inv sectionValue)
    refine ⟨(Scheme.ΓSpecIso largerRing).hom preimage, ?_⟩
    have naturality := DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_naturality quotientMap)) preimage
    exact naturality.symm.trans (by
      rw [CommRingCat.comp_apply, preimageEquation]
      simp)
  letI : Flat (Spec.map (scalarMap ≫ quotientMap)) := by
    rw [Spec.map_comp]
    infer_instance
  have scalarFinite : scalarMap.hom.Finite :=
    (IsFinite.SpecMap_iff scalarMap).mp inferInstance
  have scalarFlat : scalarMap.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  have compositeFlat : (scalarMap ≫ quotientMap).hom.Flat :=
    Flat.SpecMap_iff.mp inferInstance
  have finiteComposite : (scalarMap ≫ quotientMap).hom.Finite := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Finite.comp (.of_surjective _ quotientSurjective) scalarFinite
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank finiteComposite compositeFlat,
    Scheme.Hom.finrank_SpecMap_eq_finrank scalarFinite scalarFlat] at rankEquality
  algebraize [scalarMap.hom, quotientMap.hom, (scalarMap ≫ quotientMap).hom]
  letI : IsScalarTower baseRing largerRing smallerRing := .of_algebraMap_eq' rfl
  have bijective := Module.bijective_of_surjective_of_rankAtStalk_eq (R := baseRing)
    (φ := (IsScalarTower.toAlgHom baseRing largerRing smallerRing).toLinearMap)
    quotientSurjective fun maximalIdeal _ ↦ ?_
  · letI : IsIso quotientMap := (ConcreteCategory.isIso_iff_bijective quotientMap).mpr bijective
    infer_instance
  · have rankAtPrime := rankEquality ⟨maximalIdeal, inferInstance⟩
    rw [← RingHom.algebraMap_toAlgebra scalarMap.hom,
      ← RingHom.algebraMap_toAlgebra (scalarMap ≫ quotientMap).hom,
      RingHom.finrank_algebraMap, RingHom.finrank_algebraMap] at rankAtPrime
    exact rankAtPrime.symm

private theorem hilbertSubscheme_eq_of_le {source base : Scheme.{u}}
    {structureMap : source ⟶ base} {degree : ℕ} {parameter : Over base}
    {first second : (pullback structureMap parameter.hom).IdealSheafData}
    (firstHilbert : IsHilbertSubscheme structureMap degree parameter first)
    (secondHilbert : IsHilbertSubscheme structureMap degree parameter second)
    (containment : first ≤ second) : first = second := by
  obtain ⟨firstFinite, firstFlat, _, firstRank⟩ := firstHilbert
  obtain ⟨_, secondFlat, _, secondRank⟩ := secondHilbert
  let inclusion := IdealSheafData.inclusion containment
  let projection := first.subschemeι ≫ pullback.snd structureMap parameter.hom
  have equation : inclusion ≫ projection =
      second.subschemeι ≫ pullback.snd structureMap parameter.hom :=
    IdealSheafData.inclusion_subschemeι_assoc containment _
  letI : IsFinite projection := firstFinite
  letI : Flat projection := firstFlat
  letI : IsClosedImmersion inclusion := .of_comp_isClosedImmersion _ first.subschemeι
  letI : Flat (inclusion ≫ projection) := by rw [equation]; exact secondFlat
  letI : IsIso inclusion := isIso_closedImmersion_of_equal_rank inclusion projection
    (fun point ↦ by rw [equation, firstRank, secondRank])
  rw [← first.ker_subschemeι, ← second.ker_subschemeι,
    ← IdealSheafData.inclusion_subschemeι containment, Scheme.Hom.ker_comp_of_isIso]

local instance {source target : Scheme.{u}} (structureMap : source ⟶ target)
    [SmoothOfRelativeDimension 1 structureMap] : Smooth structureMap :=
  SmoothOfRelativeDimension.smooth 1 structureMap

variable {baseField : Type u} [Field baseField] {sourceScheme : Scheme.{u}}
  [sourceScheme.Over (Spec (.of baseField))]
  [IsProper (sourceScheme ↘ Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (sourceScheme ↘ Spec (.of baseField))]
  [GeometricallyIntegral (sourceScheme ↘ Spec (.of baseField))]
  [∀ parameter : Over (Spec (.of baseField)),
    HasInjectiveResolutions (pullback (sourceScheme ↘ Spec (.of baseField)) parameter.hom).Modules]

variable (sectionMap : Spec (.of baseField) ⟶ sourceScheme)
  (sectionEquation : sectionMap ≫ sourceScheme ↘ Spec (.of baseField) = 𝟙 _)

/-- A genus-degree divisor recovers the evaluation zero scheme of any chart
class represented by its divisor line bundle tensored with a line from the base. -/
theorem zeroLocus_directImageCounit_eq_of_iso
    (parameter : Over (Spec (.of baseField)))
    (coefficient : (picardFunctorInvertibleDirectImage (sourceScheme ↘ Spec (.of baseField))
      sectionMap sectionEquation).toFunctor.obj (op parameter))
    {divisor : (pullback (sourceScheme ↘ Spec (.of baseField)) parameter.hom).IdealSheafData}
    (divisorHilbert : IsHilbertSubscheme (sourceScheme ↘ Spec (.of baseField))
      (sourceScheme.arithmeticGenus baseField) parameter divisor)
    (baseLine : parameter.left.Modules) [baseLine.IsInvertible]
    (comparison : (fromSkeleton _).obj coefficient.1.1.val ≅ divisor.toModulesᵛ ⊗
      (Modules.pullback (pullback.snd (sourceScheme ↘ Spec (.of baseField))
        parameter.hom)).obj baseLine) :
    letI := coefficient.1.1.isInvertible
    letI := IsInvertibleDirectImage.isInvertible_pushforward
      (sourceScheme ↘ Spec (.of baseField)) parameter coefficient.1.1 coefficient.2
    (Pic.directImageCounit (sourceScheme ↘ Spec (.of baseField))
      parameter coefficient.1.1).zeroLocus = divisor := by
  let structureMap := sourceScheme ↘ Spec (.of baseField)
  let projection := pullback.snd structureMap parameter.hom
  let representative := (fromSkeleton _).obj coefficient.1.1.val
  letI : representative.IsInvertible := coefficient.1.1.isInvertible
  letI := IsInvertibleDirectImage.isInvertible_pushforward
    structureMap parameter coefficient.1.1 coefficient.2
  letI := divisorHilbert.isInvertible.isInvertible_toModules
  obtain ⟨canonicalSection, canonicalZero⟩ := divisorHilbert.isInvertible.exists_zeroLocus_eq
  let sectionMorphism : (Modules.pullback projection).obj baseLine ⟶ representative :=
    (λ_ _).inv ≫ (canonicalSection ▷ _) ≫ comparison.inv
  have sectionZero : sectionMorphism.zeroLocus = divisor := by
    rw [← canonicalZero,
      ← Modules.Hom.zeroLocus_whiskerRight canonicalSection
        ((Modules.pullback projection).obj baseLine)]
    exact Modules.Hom.zeroLocus_eq_of_arrowIso _ _
      (Arrow.isoMk (λ_ _).symm comparison (by simp [sectionMorphism]))
  let adjunction := Modules.pullbackPushforwardAdjunction projection
  let adjoint := adjunction.homEquiv _ _ sectionMorphism
  have factorization : (Modules.pullback projection).map adjoint ≫
      Pic.directImageCounit structureMap parameter coefficient.1.1 = sectionMorphism := by
    have equation := adjunction.homEquiv_counit (g := adjoint)
    rw [Equiv.symm_apply_apply] at equation
    exact equation.symm
  have containment := Modules.Hom.zeroLocus_comp_le
    ((Modules.pullback projection).map adjoint)
    (Pic.directImageCounit structureMap parameter coefficient.1.1)
  rw [factorization, sectionZero] at containment
  exact (hilbertSubscheme_eq_of_le divisorHilbert
    (IsInvertibleDirectImage.isHilbertSubscheme_zeroLocus_directImageCounit
      parameter coefficient.1.1 coefficient.2) containment).symm

/-- A genus Hilbert point whose normalized class lies in the cohomology chart
is the evaluation divisor of that class. -/
theorem invertibleDirectImageToHilbert_hilbertToPicardNormalized
    (parameter : Over (Spec (.of baseField)))
    (divisor : (hilbertPresheaf (sourceScheme ↘ Spec (.of baseField))
      (sourceScheme.arithmeticGenus baseField)).obj (op parameter))
    (membership : IsInvertibleDirectImage (sourceScheme ↘ Spec (.of baseField)) parameter
      (hilbertToPicardNormalized (sourceScheme ↘ Spec (.of baseField)) sectionMap sectionEquation
        (sourceScheme.arithmeticGenus baseField) parameter divisor).1) :
    (invertibleDirectImageToHilbert sectionMap sectionEquation).app (op parameter)
      ⟨hilbertToPicardNormalized (sourceScheme ↘ Spec (.of baseField)) sectionMap sectionEquation
        (sourceScheme.arithmeticGenus baseField) parameter divisor, membership⟩ =
      ULift.up divisor := by
  let structureMap := sourceScheme ↘ Spec (.of baseField)
  let normalizedClass := hilbertToPicardNormalized structureMap sectionMap sectionEquation
    (sourceScheme.arithmeticGenus baseField) parameter divisor
  let coefficient : (picardFunctorInvertibleDirectImage structureMap
      sectionMap sectionEquation).toFunctor.obj (op parameter) := ⟨normalizedClass, membership⟩
  letI := divisor.2.isInvertible.isInvertible_toModules
  let divisorLine := divisor.1.toModulesᵛ
  let baseLine := ((Modules.pullback (sectionBaseChange structureMap sectionMap
    sectionEquation parameter)).obj divisorLine)ᵛ
  letI : divisorLine.IsInvertible := inferInstance
  letI : baseLine.IsInvertible := inferInstance
  have classEquation : normalizedClass.1 =
      Pic.mk (divisorLine ⊗ (Modules.pullback (pullback.snd structureMap parameter.hom)).obj
        baseLine) := by
    change (normalizePicardClass structureMap sectionMap sectionEquation parameter
      (Pic.mk divisorLine)).1 = _
    change Pic.mk divisorLine * Pic.map (pullback.snd structureMap parameter.hom)
      ((Pic.map (sectionBaseChange structureMap sectionMap sectionEquation parameter)
        (Pic.mk divisorLine))⁻¹) = _
    rw [Pic.mk_tensorObj]
    congr 1
    have dualClassEquation :
        (Pic.map (sectionBaseChange structureMap sectionMap sectionEquation parameter)
          (Pic.mk divisorLine))⁻¹ = Pic.mk baseLine :=
      (congrArg Inv.inv (Pic.map_mk
        (sectionBaseChange structureMap sectionMap sectionEquation parameter)
        divisorLine)).trans
          (Pic.mk_dual ((Modules.pullback
            (sectionBaseChange structureMap sectionMap sectionEquation parameter)).obj
              divisorLine)).symm
    exact (congrArg (Pic.map (pullback.snd structureMap parameter.hom))
      dualClassEquation).trans (Pic.map_mk (pullback.snd structureMap parameter.hom) baseLine)
  have representativeEquation : Pic.mk ((fromSkeleton _).obj normalizedClass.1.val) =
      Pic.mk (divisorLine ⊗ (Modules.pullback (pullback.snd structureMap parameter.hom)).obj
        baseLine) := by
    rw [Pic.mk_fromSkeleton]
    exact classEquation
  obtain ⟨comparison⟩ := (Pic.mk_eq_mk_iff _ _).mp representativeEquation
  apply ULift.ext
  apply Subtype.ext
  exact zeroLocus_directImageCounit_eq_of_iso sectionMap sectionEquation parameter
    coefficient divisor.2 baseLine comparison

/-- The cohomology chart is represented by an actual open of a genus Hilbert
scheme, compatibly with the canonical evaluation-divisor map. -/
theorem exists_representableBy_invertibleDirectImageToHilbert [IsSepClosed baseField]
    (hilbertScheme : Over (Spec (.of baseField)))
    (hilbertRepresentation : (hilbertPresheaf (sourceScheme ↘ Spec (.of baseField))
      (sourceScheme.arithmeticGenus baseField)).RepresentableBy hilbertScheme) :
    ∃ (chartScheme : Scheme.{u}) (inclusion : chartScheme ⟶ hilbertScheme.left)
      (_ : IsOpenImmersion inclusion)
      (representation : (picardFunctorInvertibleDirectImage
        (sourceScheme ↘ Spec (.of baseField)) sectionMap sectionEquation).toFunctor
          |>.RepresentableBy (Over.mk (inclusion ≫ hilbertScheme.hom))),
      ∀ {parameter : Over (Spec (.of baseField))}
        (parameterMap : parameter ⟶ Over.mk (inclusion ≫ hilbertScheme.hom)),
        (invertibleDirectImageToHilbert sectionMap sectionEquation).app (op parameter)
            (representation.homEquiv parameterMap) =
          ULift.up (hilbertRepresentation.homEquiv (parameterMap ≫ Over.homMk inclusion)) := by
  let structureMap := sourceScheme ↘ Spec (.of baseField)
  let chart := picardFunctorInvertibleDirectImage structureMap sectionMap sectionEquation
  let normalized := (picardFunctorNormalized structureMap sectionMap sectionEquation).toFunctor
  let dictionary := invertibleDirectImageToHilbert sectionMap sectionEquation
  let abel (parameter : Over (Spec (.of baseField)))
      (divisor : (hilbertPresheaf structureMap
        (sourceScheme.arithmeticGenus baseField)).obj (op parameter)) :=
    hilbertToPicardNormalized structureMap sectionMap sectionEquation
      (sourceScheme.arithmeticGenus baseField) parameter divisor
  obtain ⟨openSubset, universal⟩ := exists_opens_hilbertToPicardNormalized_mem_iff
    structureMap sectionMap sectionEquation (sourceScheme.arithmeticGenus baseField)
    hilbertScheme hilbertRepresentation
  let inclusion : Over.mk (openSubset.ι ≫ hilbertScheme.hom) ⟶ hilbertScheme :=
    Over.homMk openSubset.ι
  have inChart {parameter : Over (Spec (.of baseField))}
      (parameterMap : parameter ⟶ Over.mk (openSubset.ι ≫ hilbertScheme.hom)) :
      abel parameter (hilbertRepresentation.homEquiv (parameterMap ≫ inclusion)) ∈
        chart.obj (op parameter) := by
    apply (universal parameter (parameterMap ≫ inclusion)).2
    rintro _ ⟨point, rfl⟩
    rw [← openSubset.range_ι]
    exact ⟨parameterMap.left point, rfl⟩
  let divisorOf {parameter : Over (Spec (.of baseField))}
      (coefficient : chart.toFunctor.obj (op parameter)) :=
    (dictionary.app (op parameter) coefficient).down
  have rangeSubset {parameter : Over (Spec (.of baseField))}
      (coefficient : chart.toFunctor.obj (op parameter)) :
      Set.range (hilbertRepresentation.homEquiv.symm (divisorOf coefficient)).left ⊆
        Set.range openSubset.ι := by
    rw [openSubset.range_ι]
    apply (universal parameter _).1
    rw [hilbertRepresentation.homEquiv.apply_symm_apply]
    change abel parameter (divisorOf coefficient) ∈ chart.obj (op parameter)
    have recovered := hilbertToPicardNormalized_invertibleDirectImageToHilbert
      sectionMap sectionEquation parameter coefficient
    change abel parameter (divisorOf coefficient) = coefficient.1 at recovered
    rw [recovered]
    exact coefficient.2
  let lift {parameter : Over (Spec (.of baseField))}
      (coefficient : chart.toFunctor.obj (op parameter)) :
      parameter ⟶ Over.mk (openSubset.ι ≫ hilbertScheme.hom) :=
    Over.homMk (IsOpenImmersion.lift openSubset.ι _ (rangeSubset coefficient)) (by
      simp only [Over.mk_left, Over.mk_hom]
      rw [IsOpenImmersion.lift_fac_assoc, Over.w])
  have liftEquation {parameter : Over (Spec (.of baseField))}
      (coefficient : chart.toFunctor.obj (op parameter)) :
      lift coefficient ≫ inclusion = hilbertRepresentation.homEquiv.symm
        (divisorOf coefficient) := by
    ext
    exact IsOpenImmersion.lift_fac _ _ _
  refine ⟨openSubset, openSubset.ι, inferInstance, {
    homEquiv {parameter} := {
      toFun parameterMap :=
        ⟨abel parameter (hilbertRepresentation.homEquiv (parameterMap ≫ inclusion)),
          inChart parameterMap⟩
      invFun := lift
      left_inv parameterMap := ?_
      right_inv coefficient := ?_ }
    homEquiv_comp restriction parameterMap := ?_ }, fun parameterMap ↦ ?_⟩
  · rw [← cancel_mono inclusion]
    refine (liftEquation _).trans (hilbertRepresentation.homEquiv.symm_apply_eq.2 ?_)
    have recovered := invertibleDirectImageToHilbert_hilbertToPicardNormalized
      sectionMap sectionEquation _ _ (inChart parameterMap)
    exact congrArg ULift.down recovered
  · apply Subtype.ext
    change abel _ (hilbertRepresentation.homEquiv (lift coefficient ≫ inclusion)) = coefficient.1
    rw [liftEquation, hilbertRepresentation.homEquiv.apply_symm_apply]
    exact hilbertToPicardNormalized_invertibleDirectImageToHilbert
      sectionMap sectionEquation _ coefficient
  · apply Subtype.ext
    change abel _ (hilbertRepresentation.homEquiv ((restriction ≫ parameterMap) ≫ inclusion)) =
      normalized.map restriction.op
        (abel _ (hilbertRepresentation.homEquiv (parameterMap ≫ inclusion)))
    rw [Category.assoc, hilbertRepresentation.homEquiv_comp]
    exact (hilbertToPicardNormalized_naturality structureMap sectionMap sectionEquation
      (sourceScheme.arithmeticGenus baseField) restriction _).symm
  · exact invertibleDirectImageToHilbert_hilbertToPicardNormalized sectionMap sectionEquation
      _ _ (inChart parameterMap)

/-- In particular, the normalized Picard cohomology chart is representable
whenever the genus Hilbert functor has a supplied scheme representative. -/
theorem isRepresentable_picardFunctorInvertibleDirectImage [IsSepClosed baseField]
    (hilbertScheme : Over (Spec (.of baseField)))
    (hilbertRepresentation : (hilbertPresheaf (sourceScheme ↘ Spec (.of baseField))
      (sourceScheme.arithmeticGenus baseField)).RepresentableBy hilbertScheme) :
    ∃ (chartScheme : Scheme.{u}) (inclusion : chartScheme ⟶ hilbertScheme.left),
      IsOpenImmersion inclusion ∧
        Nonempty ((picardFunctorInvertibleDirectImage (sourceScheme ↘ Spec (.of baseField))
          sectionMap sectionEquation).toFunctor.RepresentableBy
          (Over.mk (inclusion ≫ hilbertScheme.hom))) := by
  obtain ⟨chartScheme, inclusion, openImmersion, representation, _⟩ :=
    exists_representableBy_invertibleDirectImageToHilbert sectionMap sectionEquation
      hilbertScheme hilbertRepresentation
  exact ⟨chartScheme, inclusion, openImmersion, ⟨representation⟩⟩

end AlgebraicGeometry
