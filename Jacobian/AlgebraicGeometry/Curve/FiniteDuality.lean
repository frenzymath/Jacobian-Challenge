import Jacobian.AlgebraicGeometry.Curve.DifferentialTrace
import Jacobian.AlgebraicGeometry.Curve.TraceDuality
import Jacobian.AlgebraicGeometry.Modules.PushforwardHomAffine
import Jacobian.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit

/-!
# Finite trace duality for smooth curves

The differential trace for a finite flat, generically unramified map to the
projective line identifies the pushforward of the cotangent sheaf with the dual
of the finite algebra, valued in the cotangent sheaf of the projective line.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe curveUniverse

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

open ProjectiveLine Modules Polynomial

variable {baseField : Type curveUniverse} [Field baseField] {source : Scheme.{curveUniverse}}
  [source.Over (Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]

/-- The differential trace induces the finite duality comparison for the structure sheaf. -/
theorem exists_isIso_pushforwardHomObjComparison_unit (morphism : source ⟶ projectiveLine baseField)
    [morphism.IsOver (Spec (.of baseField))] [IsFinite morphism] [Flat morphism]
    (genericUnramified : ∀ point : source, IsField (source.presheaf.stalk point) →
      (morphism.stalkMap point).hom.FormallyUnramified) :
    ∃ trace : (Modules.pushforward morphism).obj
        (source ↘ Spec (.of baseField)).relativeDifferentials ⟶
          (projectiveLineToSpec baseField).relativeDifferentials,
      IsIso (Modules.pushforwardHomObjComparison morphism trace
        (SheafOfModules.unit source.ringCatSheaf)) := by
  obtain ⟨trace, traceFormula⟩ := exists_differentialTrace morphism
  let basisOpen : (Σ _ : Fin 2, {polynomial : baseField[X] // polynomial ≠ 0}) →
      (projectiveLine baseField).Opens :=
    fun index ↦ chartBasicOpen baseField index.1 index.2.1
  have basis : Opens.IsBasis (Set.range basisOpen) := isBasis_chartBasicOpen baseField
  have affine (index) : IsAffineOpen (basisOpen index) :=
    isAffineOpen_chartBasicOpen baseField index.1 index.2.1
  have affinePreimage (index) : IsAffineOpen (morphism ⁻¹ᵁ basisOpen index) :=
    (affine index).preimage morphism
  refine ⟨trace, isIso_of_bijective_app_of_basis basis _ fun index ↦ ?_⟩
  have pairingFormula
      (differential : Γ((source ↘ Spec (.of baseField)).relativeDifferentials,
        morphism ⁻¹ᵁ basisOpen index))
      (algebraSection : Γ(source, morphism ⁻¹ᵁ basisOpen index)) :
      ((pushforwardHomObjComparison morphism trace
        (SheafOfModules.unit source.ringCatSheaf)).app (basisOpen index)
          (PresheafOfModules.homObjUnitInvApp _ differential)).app
          (op (Over.mk (𝟙 (basisOpen index)))) algebraSection =
        morphism.traceSections _ (affinePreimage index)
          (morphism.free_finite_chartBasicOpen index.1 index.2.1).1
          (morphism.free_finite_chartBasicOpen index.1 index.2.1).2
          (algebraSection • differential) := by
    refine (traceFormula index.1 index.2.1 index.2.2 _).trans (congrArg
      (morphism.traceSections _ (affinePreimage index)
        (morphism.free_finite_chartBasicOpen index.1 index.2.1).1
        (morphism.free_finite_chartBasicOpen index.1 index.2.1).2) ?_)
    change ((PresheafOfModules.homObjUnitInvApp _ differential).app
      (op (Over.mk (𝟙 (morphism ⁻¹ᵁ basisOpen index))))).hom algebraSection = _
    rw [PresheafOfModules.homObjUnitInvApp_app_apply]
    exact congrArg (fun value ↦ algebraSection • value)
      (PresheafOfModules.map_id_apply' _ differential)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro homomorphism vanishes
    have roundTrip := ConcreteCategory.congr_hom (PresheafOfModules.homObjUnitIsoApp
      (source ↘ Spec (.of baseField)).relativeDifferentials.val
        (op (morphism ⁻¹ᵁ basisOpen index))).hom_inv_id homomorphism
    set differential := ConcreteCategory.hom (PresheafOfModules.homObjUnitIsoApp
      (source ↘ Spec (.of baseField)).relativeDifferentials.val
        (op (morphism ⁻¹ᵁ basisOpen index))).hom homomorphism
    have represented : homomorphism = PresheafOfModules.homObjUnitInvApp _ differential :=
      roundTrip.symm
    have differentialZero : differential = 0 := by
      refine Hom.traceSections_smul_eq_zero genericUnramified index.1 index.2.2 differential
        fun algebraSection ↦ ?_
      refine (pairingFormula differential algebraSection).symm.trans ?_
      rw [← represented, vanishes]
      rfl
    rw [represented, differentialZero]
    exact map_zero (ConcreteCategory.hom (PresheafOfModules.homObjUnitIsoApp
      (source ↘ Spec (.of baseField)).relativeDifferentials.val
        (op (morphism ⁻¹ᵁ basisOpen index))).inv)
  · intro functional
    let localFunctional : Γ(source, morphism ⁻¹ᵁ basisOpen index) →+
        Γ((projectiveLineToSpec baseField).relativeDifferentials, basisOpen index) :=
      (functional.app (op (Over.mk (𝟙 (basisOpen index))))).hom.toAddMonoidHom
    have linear (scalar : Γ(projectiveLine baseField, basisOpen index))
        (algebraSection : Γ(source, morphism ⁻¹ᵁ basisOpen index)) :
        localFunctional (morphism.app _ scalar * algebraSection) =
          scalar • localFunctional algebraSection :=
      (functional.app (op (Over.mk (𝟙 (basisOpen index))))).hom.map_smul scalar algebraSection
    obtain ⟨differential, represents⟩ :=
      Hom.exists_traceSections_smul_eq genericUnramified index.1 index.2.2 localFunctional linear
    refine ⟨PresheafOfModules.homObjUnitInvApp _ differential, ?_⟩
    refine restrictOver_pushforward_unit_hom_ext morphism (affine index) (affinePreimage index) ?_
    ext algebraSection
    exact (pairingFormula differential algebraSection).trans (represents algebraSection)

end AlgebraicGeometry.Scheme
