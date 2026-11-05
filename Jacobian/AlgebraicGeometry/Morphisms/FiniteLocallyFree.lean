import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Affine neighbourhoods for finite locally free morphisms

A finite flat morphism locally of finite presentation is free over an affine neighbourhood
of each target point. Freeness of sections on an affine open is preserved by affine base change.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

private theorem exists_free_localization {ringType moduleType : Type*} [CommRing ringType]
    [AddCommGroup moduleType] [Module ringType moduleType]
    [Module.FinitePresentation ringType moduleType] [Module.Flat ringType moduleType]
    (prime : Ideal ringType) [prime.IsPrime] :
    ∃ scalar ∉ prime,
      Module.Free (Localization.Away scalar) (LocalizedModule.Away scalar moduleType) ∧
        Module.Finite (Localization.Away scalar) (LocalizedModule.Away scalar moduleType) := by
  letI : Module.Free (Localization.AtPrime prime)
      (LocalizedModule prime.primeCompl moduleType) := Module.free_of_flat_of_isLocalRing
  obtain ⟨scalar, outsidePrime, free, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers prime.primeCompl
      (LocalizedModule.mkLinearMap prime.primeCompl moduleType) (Localization.AtPrime prime)
  exact ⟨scalar, outsidePrime, free,
    Module.Finite.of_isLocalizedModule (.powers scalar)
      (LocalizedModule.mkLinearMap (.powers scalar) moduleType)⟩

private theorem free_localization_of_dvd {baseRing moduleType : Type*} [CommRing baseRing]
    [AddCommGroup moduleType] [Module baseRing moduleType] {denominator multiple : baseRing} (divides : denominator ∣ multiple)
    [Module.Free (Localization.Away denominator) (LocalizedModule.Away denominator moduleType)]
    (localizedRing : Type*) [CommRing localizedRing] [Algebra baseRing localizedRing] [IsLocalization.Away multiple localizedRing]
    {localizedModule : Type*} [AddCommGroup localizedModule] [Module baseRing localizedModule] [Module localizedRing localizedModule] [IsScalarTower baseRing localizedRing localizedModule]
    (localizationMap : moduleType →ₗ[baseRing] localizedModule) [IsLocalizedModule (.powers multiple) localizationMap] : Module.Free localizedRing localizedModule := by
  have denominator_isUnit : IsUnit (algebraMap baseRing localizedRing denominator) :=
    isUnit_of_dvd_unit (map_dvd _ divides) (IsLocalization.Away.algebraMap_isUnit multiple)
  let : Algebra (Localization.Away denominator) localizedRing := (IsLocalization.Away.lift denominator denominator_isUnit).toAlgebra
  have : IsScalarTower baseRing (Localization.Away denominator) localizedRing :=
    .of_algebraMap_eq fun scalar ↦ (IsLocalization.Away.lift_eq denominator denominator_isUnit scalar).symm
  let canonicalBaseChange := ((isLocalizedModule_iff_isBaseChange (.powers denominator) (Localization.Away denominator)
    (LocalizedModule.mkLinearMap (.powers denominator) moduleType)).mp inferInstance).equiv
  let actualBaseChange := ((isLocalizedModule_iff_isBaseChange (.powers multiple) localizedRing localizationMap).mp inferInstance).equiv
  exact .of_equiv (TensorProduct.AlgebraTensorModule.congr (.refl localizedRing localizedRing) canonicalBaseChange.symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange baseRing (Localization.Away denominator) localizedRing localizedRing moduleType ≪≫ₗ actualBaseChange)

/-- A finite flat morphism locally of finite presentation is free near each target point. -/
lemma Scheme.Hom.exists_isAffineOpen_mem_free_app {source target : Scheme.{schemeUniverse}} (projection : source ⟶ target) [IsFinite projection]
    [Flat projection] [LocallyOfFinitePresentation projection] (point : target) :
    ∃ openSubset : target.Opens, IsAffineOpen openSubset ∧ point ∈ openSubset ∧
      letI := (projection.app openSubset).hom.toAlgebra
      Module.Free Γ(target, openSubset) Γ(source, projection ⁻¹ᵁ openSubset) := by
  obtain ⟨initialOpen, initialAffine, point_mem, -⟩ := exists_isAffineOpen_mem_and_subset (x := point) (U := ⊤) trivial
  have preimageAffine : IsAffineOpen (projection ⁻¹ᵁ initialOpen) := initialAffine.preimage projection
  let : Algebra Γ(target, initialOpen) Γ(source, projection ⁻¹ᵁ initialOpen) := (projection.app initialOpen).hom.toAlgebra
  have : Module.Finite Γ(target, initialOpen) Γ(source, projection ⁻¹ᵁ initialOpen) := projection.finite_app initialOpen initialAffine
  have flat_sections : (projection.app initialOpen).hom.Flat := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE @Flat projection inferInstance ⟨initialOpen, initialAffine⟩ ⟨_, preimageAffine⟩ _
  have : Module.Flat Γ(target, initialOpen) Γ(source, projection ⁻¹ᵁ initialOpen) := flat_sections
  have finitePresentation : (projection.app initialOpen).hom.FinitePresentation := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE @LocallyOfFinitePresentation projection inferInstance ⟨initialOpen, initialAffine⟩
      ⟨_, preimageAffine⟩ _
  have : Algebra.FinitePresentation Γ(target, initialOpen) Γ(source, projection ⁻¹ᵁ initialOpen) := finitePresentation
  have : Module.FinitePresentation Γ(target, initialOpen) Γ(source, projection ⁻¹ᵁ initialOpen) :=
    .of_finite_of_finitePresentation _ _
  obtain ⟨prime, rfl⟩ : point ∈ Set.range initialAffine.fromSpec := by rwa [initialAffine.range_fromSpec]
  obtain ⟨denominator, outsidePrime, hfree, -⟩ := exists_free_localization
    (ringType := Γ(target, initialOpen)) (moduleType := Γ(source, projection ⁻¹ᵁ initialOpen)) prime.asIdeal
  refine ⟨target.basicOpen denominator, initialAffine.basicOpen denominator, (by
    change prime ∈ initialAffine.fromSpec ⁻¹ᵁ target.basicOpen denominator
    rw [initialAffine.fromSpec_preimage_basicOpen]
    exact (PrimeSpectrum.mem_basicOpen denominator prime).mpr outsidePrime), ?_⟩
  have preimage_le : projection ⁻¹ᵁ target.basicOpen denominator ≤ projection ⁻¹ᵁ initialOpen := projection.preimage_mono (target.basicOpen_le denominator)
  let : Algebra Γ(target, target.basicOpen denominator) Γ(source, projection ⁻¹ᵁ target.basicOpen denominator) :=
    (projection.app (target.basicOpen denominator)).hom.toAlgebra
  let : Algebra Γ(source, projection ⁻¹ᵁ initialOpen) Γ(source, projection ⁻¹ᵁ target.basicOpen denominator) :=
    (source.presheaf.map (homOfLE preimage_le).op).hom.toAlgebra
  let : Algebra Γ(target, initialOpen) Γ(source, projection ⁻¹ᵁ target.basicOpen denominator) :=
    (projection.app initialOpen ≫ source.presheaf.map (homOfLE preimage_le).op).hom.toAlgebra
  have : IsScalarTower Γ(target, initialOpen) Γ(source, projection ⁻¹ᵁ initialOpen) Γ(source, projection ⁻¹ᵁ target.basicOpen denominator) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(target, initialOpen) Γ(target, target.basicOpen denominator) Γ(source, projection ⁻¹ᵁ target.basicOpen denominator) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra]
      exact congrArg CommRingCat.Hom.hom (projection.naturality _).symm)
  have : IsLocalization.Away denominator Γ(target, target.basicOpen denominator) := initialAffine.isLocalization_basicOpen denominator
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(source, projection ⁻¹ᵁ initialOpen) (Submonoid.powers denominator))
      Γ(source, projection ⁻¹ᵁ target.basicOpen denominator) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    have preimage_eq : projection ⁻¹ᵁ target.basicOpen denominator = source.basicOpen (projection.app initialOpen denominator) := Scheme.preimage_basicOpen projection denominator
    have := preimageAffine.isLocalization_basicOpen (projection.app initialOpen denominator)
    let restrictionEquiv := (source.presheaf.mapIso (eqToIso preimage_eq).op).commRingCatIsoToRingEquiv
    refine IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (projection.app initialOpen denominator))
      { restrictionEquiv with commutes' := fun element ↦ ?_ }
    change (source.presheaf.map _ ≫ source.presheaf.map _) element = source.presheaf.map _ element
    rw [← Functor.map_comp]
    rfl
  exact free_localization_of_dvd (dvd_refl denominator) Γ(target, target.basicOpen denominator)
    (IsScalarTower.toAlgHom Γ(target, initialOpen) Γ(source, projection ⁻¹ᵁ initialOpen) Γ(source, projection ⁻¹ᵁ target.basicOpen denominator)).toLinearMap

/-- Freeness of sections over an affine open is preserved by an affine base change. -/
lemma free_app_of_isPullback {source target base baseChange : Scheme.{schemeUniverse}} {baseMap : baseChange ⟶ base} {pullbackMap : target ⟶ source} {structureMap : source ⟶ base}
    {changedStructureMap : target ⟶ baseChange} (cartesian : IsPullback pullbackMap changedStructureMap structureMap baseMap) {baseOpen : base.Opens} {sourceOpen : source.Opens}
    (baseAffine : IsAffineOpen baseOpen) (changedAffine : IsAffineOpen (baseMap ⁻¹ᵁ baseOpen)) (sourceAffine : IsAffineOpen sourceOpen)
    (source_le : sourceOpen ≤ structureMap ⁻¹ᵁ baseOpen)
    (hfree : letI := (baseMap.app baseOpen).hom.toAlgebra; Module.Free Γ(base, baseOpen) Γ(baseChange, baseMap ⁻¹ᵁ baseOpen)) :
    letI := (pullbackMap.app sourceOpen).hom.toAlgebra
    Module.Free Γ(source, sourceOpen) Γ(target, pullbackMap ⁻¹ᵁ sourceOpen) := by
  have preimage_inf : pullbackMap ⁻¹ᵁ sourceOpen = pullbackMap ⁻¹ᵁ sourceOpen ⊓ changedStructureMap ⁻¹ᵁ (baseMap ⁻¹ᵁ baseOpen) := by
    refine (inf_eq_left.mpr fun element hx ↦ ?_).symm
    have point_mem_base : structureMap (pullbackMap element) ∈ baseOpen := source_le hx
    rwa [← Scheme.Hom.comp_apply, cartesian.w, Scheme.Hom.comp_apply] at point_mem_base
  have := isIso_pushoutSection_of_isAffineOpen cartesian (UT := baseMap ⁻¹ᵁ baseOpen) le_rfl source_le preimage_inf baseAffine changedAffine sourceAffine
  have ringPushout := (isIso_pushoutSection_iff ..).mp this
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at ringPushout
  let : Algebra Γ(base, baseOpen) Γ(source, sourceOpen) := (structureMap.appLE baseOpen sourceOpen source_le).hom.toAlgebra
  let : Algebra Γ(base, baseOpen) Γ(baseChange, baseMap ⁻¹ᵁ baseOpen) := (baseMap.app baseOpen).hom.toAlgebra
  let : Algebra Γ(source, sourceOpen) Γ(target, pullbackMap ⁻¹ᵁ sourceOpen) := (pullbackMap.app sourceOpen).hom.toAlgebra
  let : Algebra Γ(baseChange, baseMap ⁻¹ᵁ baseOpen) Γ(target, pullbackMap ⁻¹ᵁ sourceOpen) :=
    (changedStructureMap.appLE (baseMap ⁻¹ᵁ baseOpen) (pullbackMap ⁻¹ᵁ sourceOpen) (preimage_inf.le.trans inf_le_right)).hom.toAlgebra
  let : Algebra Γ(base, baseOpen) Γ(target, pullbackMap ⁻¹ᵁ sourceOpen) := (structureMap.appLE baseOpen sourceOpen source_le ≫ pullbackMap.app sourceOpen).hom.toAlgebra
  have : IsScalarTower Γ(base, baseOpen) Γ(source, sourceOpen) Γ(target, pullbackMap ⁻¹ᵁ sourceOpen) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(base, baseOpen) Γ(baseChange, baseMap ⁻¹ᵁ baseOpen) Γ(target, pullbackMap ⁻¹ᵁ sourceOpen) :=
    .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom ringPushout.w)
  have algebraPushout : Algebra.IsPushout Γ(base, baseOpen) Γ(baseChange, baseMap ⁻¹ᵁ baseOpen) Γ(source, sourceOpen) Γ(target, pullbackMap ⁻¹ᵁ sourceOpen) :=
    CommRingCat.isPushout_iff_isPushout.mp ringPushout.flip
  exact .of_equiv algebraPushout.symm.equiv.toLinearEquiv

end AlgebraicGeometry
