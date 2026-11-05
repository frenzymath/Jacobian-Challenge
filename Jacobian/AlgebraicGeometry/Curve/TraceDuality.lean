import Jacobian.AlgebraicGeometry.Curve.FiniteTraceSections
import Jacobian.AlgebraicGeometry.Geometrically.Smooth
import Jacobian.AlgebraicGeometry.ProjectiveLine.Differentials
import Jacobian.AlgebraicGeometry.ProjectiveLine.Geometry

/-!
# Local duality for differential traces on smooth curves

For a finite flat, generically unramified map from a smooth curve to the projective
line, the trace pairing identifies differentials over each polynomial basic open
with linear maps from the finite algebra of sections to differentials on the base.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe curveUniverse

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

open ProjectiveLine Polynomial

attribute [local instance] Algebra.precompModule Algebra.precompModule_isScalarTower

variable {baseField : Type curveUniverse} [Field baseField] {source : Scheme.{curveUniverse}}
  [source.Over (Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
  {morphism : source ⟶ projectiveLine baseField} [morphism.IsOver (Spec (.of baseField))]
  [IsFinite morphism] [Flat morphism]
  (genericUnramified : ∀ point : source, IsField (source.presheaf.stalk point) →
    (morphism.stalkMap point).hom.FormallyUnramified)
  (coordinate : Fin 2) {polynomial : baseField[X]} (nonzero : polynomial ≠ 0)

include genericUnramified nonzero in
/-- The differential trace pairing is perfect over polynomial basic opens. -/
lemma traceSections_smul_duality :
    (∀ differential : Γ((source ↘ Spec (.of baseField)).relativeDifferentials,
      morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial),
      (∀ algebraSection : Γ(source, morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial),
        morphism.traceSections _
          ((isAffineOpen_chartBasicOpen baseField coordinate polynomial).preimage morphism)
          (morphism.free_finite_chartBasicOpen coordinate polynomial).1
          (morphism.free_finite_chartBasicOpen coordinate polynomial).2
          (algebraSection • differential) = 0) → differential = 0) ∧
    ∀ linearMap : Γ(source, morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial) →+
        Γ((projectiveLineToSpec baseField).relativeDifferentials,
          chartBasicOpen baseField coordinate polynomial),
      (∀ (scalar : Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial))
        (algebraSection : Γ(source, morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial)),
        linearMap (morphism.app _ scalar * algebraSection) = scalar • linearMap algebraSection) →
      ∃ differential : Γ((source ↘ Spec (.of baseField)).relativeDifferentials,
          morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial),
        ∀ algebraSection, morphism.traceSections _
          ((isAffineOpen_chartBasicOpen baseField coordinate polynomial).preimage morphism)
          (morphism.free_finite_chartBasicOpen coordinate polynomial).1
          (morphism.free_finite_chartBasicOpen coordinate polynomial).2
          (algebraSection • differential) = linearMap algebraSection := by
  have targetAffine := isAffineOpen_chartBasicOpen baseField coordinate polynomial
  have sourceAffine := targetAffine.preimage morphism
  have := SmoothOfRelativeDimension.smooth (n := 1) (f := source ↘ Spec (.of baseField))
  have := Smooth.isReduced_of_field (source ↘ Spec (.of baseField))
  obtain ⟨free, finite⟩ := morphism.free_finite_chartBasicOpen coordinate polynomial
  let := (morphism.app (chartBasicOpen baseField coordinate polynomial)).hom.toAlgebra
  let : Algebra baseField Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial) :=
    ((projectiveLineToSpec baseField).specStructureMap _).hom.toAlgebra
  let : Algebra baseField Γ(source, morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial) :=
    ((source ↘ Spec (.of baseField)).specStructureMap _).hom.toAlgebra
  have : IsScalarTower baseField
      Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial)
      Γ(source, morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial) :=
    .of_algebraMap_eq' <| (congrArg CommRingCat.Hom.hom
      (specStructureMap_comp_app morphism (chartBasicOpen baseField coordinate polynomial))).symm
  let : Module baseField Γ((projectiveLineToSpec baseField).relativeDifferentials,
      chartBasicOpen baseField coordinate polynomial) :=
    Module.compHom _
      (algebraMap baseField Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial))
  have : IsScalarTower baseField
      Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial)
      Γ((projectiveLineToSpec baseField).relativeDifferentials,
        chartBasicOpen baseField coordinate polynomial) :=
    ⟨fun coefficient scalar differential ↦
      mul_smul (algebraMap baseField Γ(projectiveLine baseField, _) coefficient) scalar differential⟩
  let : Algebra baseField[X]
      Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial) :=
    (polyToChartBasicOpen baseField coordinate polynomial).toAlgebra
  have : IsScalarTower baseField baseField[X]
      Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial) :=
    .of_algebraMap_eq fun coefficient ↦
      (polyToChartBasicOpen_C baseField coordinate polynomial coefficient).symm
  have := isLocalization_chartBasicOpen baseField coordinate polynomial
  have : Algebra.Smooth baseField
      Γ(source, morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial) :=
    smooth_sections sourceAffine rfl
  have bijective :=
    KaehlerDifferential.bijective_liftKaehlerDifferential_traceDerivation_of_isFreeGenerator
      polynomial nonzero _
      (isFreeGenerator_sectionsD_polyToChartBasicOpen_X baseField coordinate polynomial).bijective
      ((projectiveLineToSpec baseField).sectionsDerivation _ rfl)
      (sectionsDerivation_apply _ _ rfl _)
      (fun ideal maximal ↦
        have := maximal.isPrime
        exists_kaehlerDifferential_generator sourceAffine rfl ideal)
      (fun prime _ minimal ↦ morphism.formallyUnramified_localization_of_mem_minimalPrimes
        genericUnramified targetAffine sourceAffine prime minimal)
  have traceFormula
      (differential : Γ((source ↘ Spec (.of baseField)).relativeDifferentials,
        morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial))
      (algebraSection : Γ(source, morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial)) :
      morphism.traceSections _ sourceAffine free finite (algebraSection • differential) =
        (Algebra.traceDerivation
          (B := Γ(source, morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial))
          ((projectiveLineToSpec baseField).sectionsDerivation _ rfl)).liftKaehlerDifferential
          (((source ↘ Spec (.of baseField)).kaehlerSectionsEquiv _ rfl sourceAffine).symm
            differential) algebraSection := by
    rw [← KaehlerDifferential.traceLin_apply, ← LinearEquiv.map_smul]
    rfl
  refine ⟨fun differential vanishes ↦ ?_, fun linearMap linear ↦ ?_⟩
  · apply ((source ↘ Spec (.of baseField)).kaehlerSectionsEquiv _ rfl sourceAffine).symm.injective
    rw [map_zero]
    refine bijective.1 ?_
    rw [map_zero]
    refine LinearMap.ext fun algebraSection ↦ ?_
    rw [← traceFormula, vanishes, LinearMap.zero_apply]
  · let moduleMap :
        Γ(source, morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial) →ₗ[
          Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial)]
        Γ((projectiveLineToSpec baseField).relativeDifferentials,
          chartBasicOpen baseField coordinate polynomial) :=
      { toFun := linearMap
        map_add' := linearMap.map_add
        map_smul' := linear }
    obtain ⟨differential, mapsTo⟩ := bijective.2 moduleMap
    refine ⟨(source ↘ Spec (.of baseField)).kaehlerSectionsEquiv _ rfl sourceAffine differential,
      fun algebraSection ↦ ?_⟩
    rw [traceFormula, LinearEquiv.symm_apply_apply, mapsTo]
    rfl

include genericUnramified nonzero in
/-- Vanishing against every algebraSection forces a differential to vanish. -/
lemma traceSections_smul_eq_zero
    (differential : Γ((source ↘ Spec (.of baseField)).relativeDifferentials,
      morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial))
    (vanishes : ∀ algebraSection : Γ(source, morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial),
      morphism.traceSections _
        ((isAffineOpen_chartBasicOpen baseField coordinate polynomial).preimage morphism)
        (morphism.free_finite_chartBasicOpen coordinate polynomial).1
        (morphism.free_finite_chartBasicOpen coordinate polynomial).2 (algebraSection • differential) = 0) :
    differential = 0 :=
  (traceSections_smul_duality genericUnramified coordinate nonzero).1 differential vanishes

include genericUnramified nonzero in
/-- Every linear functional on the finite algebra is represented by the trace pairing. -/
lemma exists_traceSections_smul_eq
    (linearMap : Γ(source, morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial) →+
      Γ((projectiveLineToSpec baseField).relativeDifferentials,
        chartBasicOpen baseField coordinate polynomial))
    (linear : ∀ (scalar : Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial))
      (algebraSection : Γ(source, morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial)),
      linearMap (morphism.app _ scalar * algebraSection) = scalar • linearMap algebraSection) :
    ∃ differential : Γ((source ↘ Spec (.of baseField)).relativeDifferentials,
        morphism ⁻¹ᵁ chartBasicOpen baseField coordinate polynomial),
      ∀ algebraSection, morphism.traceSections _
        ((isAffineOpen_chartBasicOpen baseField coordinate polynomial).preimage morphism)
        (morphism.free_finite_chartBasicOpen coordinate polynomial).1
        (morphism.free_finite_chartBasicOpen coordinate polynomial).2
        (algebraSection • differential) = linearMap algebraSection :=
  (traceSections_smul_duality genericUnramified coordinate nonzero).2 linearMap linear

end AlgebraicGeometry.Scheme.Hom
