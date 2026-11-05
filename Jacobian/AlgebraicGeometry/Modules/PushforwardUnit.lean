import Jacobian.AlgebraicGeometry.Modules.Invertible
import Jacobian.AlgebraicGeometry.Modules.HomSection
import Mathlib.Tactic.Ring

/-!
# The canonical map to the pushforward of the structure module

The pullback-pushforward adjunction gives a canonical map from the structure
module on the base to the pushforward of the structure module on the source.
If this map is an isomorphism, pullback of global functions is bijective.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable {source base : Scheme.{schemeUniverse}}

/-- The adjunction unit followed by the pullback isomorphism for the structure module. -/
abbrev pushforwardUnitMap (morphism : source ⟶ base) :
    SheafOfModules.unit base.ringCatSheaf ⟶
      (Modules.pushforward morphism).obj (SheafOfModules.unit source.ringCatSheaf) :=
  (Modules.pullbackPushforwardAdjunction morphism).unit.app
      (SheafOfModules.unit base.ringCatSheaf) ≫
    (Modules.pushforward morphism).map (Modules.pullbackObjUnitIso morphism).hom

/-- On every open, the canonical structure-module map is pullback of functions. -/
lemma pushforwardUnitMap_app (morphism : source ⟶ base) (openSubset : base.Opens)
    (scalar : Γ(base, openSubset)) :
    Modules.Hom.app (pushforwardUnitMap morphism) openSubset scalar =
      morphism.app openSubset scalar := by
  let comparison := pushforwardUnitMap morphism
  have topOne : Modules.Hom.app comparison ⊤ (1 : Γ(base, ⊤)) = (1 : Γ(source, ⊤)) := by
    have unitSection := Modules.pullbackSection_app_one morphism (𝟙 (Modules.unit base))
    change Modules.Hom.app (Modules.pullbackObjUnitIso morphism).hom _
      (Modules.pullbackSection morphism (Modules.Hom.app (𝟙 _) ⊤ (1 : Γ(base, ⊤)))) =
        (1 : Γ(source, ⊤))
    rw [unitSection, CategoryTheory.Functor.map_id, Category.comp_id,
      ← ConcreteCategory.comp_apply, ← Modules.Hom.comp_app, Iso.inv_hom_id]
    rfl
  have openOne : Modules.Hom.app comparison openSubset (1 : Γ(base, openSubset)) =
      (1 : Γ(source, morphism ⁻¹ᵁ openSubset)) := by
    have naturality := Modules.Hom.app_presheaf_map comparison
      (homOfLE le_top : openSubset ⟶ ⊤) (1 : Γ(base, ⊤))
    have restrictOne : (Modules.unit base).presheaf.map
        (homOfLE le_top : openSubset ⟶ ⊤).op (1 : Γ(base, ⊤)) =
        (1 : Γ(base, openSubset)) :=
      map_one (base.presheaf.map (homOfLE le_top : openSubset ⟶ ⊤).op).hom
    rw [restrictOne, topOne] at naturality
    exact naturality.trans (map_one (source.presheaf.map
      (homOfLE (morphism.preimage_mono (le_top : openSubset ≤ ⊤))).op).hom)
  have scalarAction := Modules.Hom.app_smul comparison scalar (1 : Γ(base, openSubset))
  have scalarOne : scalar • (1 : Γ(base, openSubset)) = scalar := by
    rw [smul_eq_mul, mul_one]
  rw [scalarOne] at scalarAction
  rw [scalarAction, openOne]
  exact mul_one (morphism.app openSubset scalar)

/-- An isomorphism with the pushforward structure module implies surjectivity on global functions. -/
lemma surjective_appTop_of_isIso_pushforwardUnitMap (morphism : source ⟶ base)
    [IsIso (pushforwardUnitMap morphism)] : Function.Surjective morphism.appTop := by
  have functionEquation :
      (Modules.Hom.app (pushforwardUnitMap morphism) ⊤ : Γ(base, ⊤) → Γ(source, ⊤)) =
        morphism.appTop := funext (pushforwardUnitMap_app morphism ⊤)
  exact functionEquation ▸ (ConcreteCategory.bijective_of_isIso
    (Modules.Hom.app (pushforwardUnitMap morphism) ⊤)).2

/-- An isomorphism with the pushforward structure module implies bijectivity on global functions. -/
lemma bijective_appTop_of_isIso_pushforwardUnitMap (morphism : source ⟶ base)
    [IsIso (pushforwardUnitMap morphism)] : Function.Bijective morphism.appTop := by
  have functionEquation :
      (Modules.Hom.app (pushforwardUnitMap morphism) ⊤ : Γ(base, ⊤) → Γ(source, ⊤)) =
        morphism.appTop := funext (pushforwardUnitMap_app morphism ⊤)
  exact functionEquation ▸ ConcreteCategory.bijective_of_isIso
    (Modules.Hom.app (pushforwardUnitMap morphism) ⊤)

end AlgebraicGeometry
