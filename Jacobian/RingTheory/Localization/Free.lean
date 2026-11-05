import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Localization.Free

/-!
# Freeness after shrinking a principal localization
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

theorem Module.free_of_isLocalizedModule_away_of_dvd {ring module : Type*} [CommRing ring]
    [AddCommGroup module] [Module ring module] {localizer localSection : ring} (hrs : localizer ∣ localSection)
    [Module.Free (Localization.Away localizer) (LocalizedModule.Away localizer module)]
    (awayRing : Type*) [CommRing awayRing] [Algebra ring awayRing] [IsLocalization.Away localSection awayRing]
    {awayModule : Type*} [AddCommGroup awayModule] [Module ring awayModule] [Module awayRing awayModule] [IsScalarTower ring awayRing awayModule]
    (morphism : module →ₗ[ring] awayModule) [IsLocalizedModule (.powers localSection) morphism] : Module.Free awayRing awayModule := by
  have hr : IsUnit (algebraMap ring awayRing localizer) :=
    isUnit_of_dvd_unit (map_dvd _ hrs) (IsLocalization.Away.algebraMap_isUnit localSection)
  let : Algebra (Localization.Away localizer) awayRing := (IsLocalization.Away.lift localizer hr).toAlgebra
  have : IsScalarTower ring (Localization.Away localizer) awayRing :=
    .of_algebraMap_eq fun numerator ↦ (IsLocalization.Away.lift_eq localizer hr numerator).symm
  let firstEquivalence := ((isLocalizedModule_iff_isBaseChange (.powers localizer) (Localization.Away localizer)
    (LocalizedModule.mkLinearMap (.powers localizer) module)).mp inferInstance).equiv
  let secondEquivalence := ((isLocalizedModule_iff_isBaseChange (.powers localSection) awayRing morphism).mp inferInstance).equiv
  exact .of_equiv (TensorProduct.AlgebraTensorModule.congr (.refl awayRing awayRing) firstEquivalence.symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange ring (Localization.Away localizer) awayRing awayRing module ≪≫ₗ secondEquivalence)
