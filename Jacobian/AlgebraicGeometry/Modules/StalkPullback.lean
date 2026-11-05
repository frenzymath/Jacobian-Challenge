import Jacobian.AlgebraicGeometry.Modules.Stalk
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Stalks of pulled-back module sheaves

The stalk of a pullback is the tensor product along the map of local rings.
The comparison is induced by the pullback unit, and its bijectivity follows
from the stalk–skyscraper adjunction and the tensor-product universal property.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits TopologicalSpace Opposite TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

private lemma bijective_of_forall_bijective_comp {baseRing source target : Type u}
    [CommRing baseRing] [AddCommGroup source] [AddCommGroup target]
    [Module baseRing source] [Module baseRing target] (comparison : source →ₗ[baseRing] target)
    (universal : ∀ (moduleType : Type u) [AddCommGroup moduleType] [Module baseRing moduleType],
      Function.Bijective fun linearMap : target →ₗ[baseRing] moduleType ↦
        linearMap ∘ₗ comparison) : Function.Bijective comparison := by
  obtain ⟨inverse, leftInverse⟩ := (universal source).surjective LinearMap.id
  have rightInverse : comparison ∘ₗ inverse = LinearMap.id := (universal target).injective (by
    simp only [LinearMap.comp_assoc, leftInverse]
    rfl)
  exact ⟨Function.LeftInverse.injective (g := inverse) fun element ↦ congr($leftInverse element),
    Function.RightInverse.surjective (g := inverse) fun element ↦ congr($rightInverse element)⟩


variable {baseScheme sourceScheme : Scheme.{u}} (morphism : sourceScheme ⟶ baseScheme) (point : sourceScheme)

noncomputable def pushforwardStalkMap (targetSheaf : sourceScheme.Modules) :
    ((pushforward morphism).obj targetSheaf).presheaf.stalk (morphism point) →+ targetSheaf.presheaf.stalk point :=
  ConcreteCategory.hom (colimit.desc ((OpenNhds.inclusion (morphism point)).op ⋙
      ((pushforward morphism).obj targetSheaf).presheaf)
    { pt := targetSheaf.presheaf.stalk point
      ι :=
        { app openSubset := targetSheaf.presheaf.germ (morphism ⁻¹ᵁ openSubset.unop.1) point openSubset.unop.2
          naturality openSubset smallerOpen inclusion := by
            ext sectionValue
            exact targetSheaf.presheaf.germ_res_apply (homOfLE (morphism.preimage_mono (leOfHom inclusion.unop))) point
              smallerOpen.unop.2 sectionValue } })

variable {morphism point} in
@[simp]
lemma pushforwardStalkMap_germ (targetSheaf : sourceScheme.Modules) {openSubset : baseScheme.Opens} (membership : morphism point ∈ openSubset)
    (sectionValue : Γ((pushforward morphism).obj targetSheaf, openSubset)) :
    pushforwardStalkMap morphism point targetSheaf (((pushforward morphism).obj targetSheaf).presheaf.germ openSubset (morphism point) membership sectionValue) =
      targetSheaf.presheaf.germ (morphism ⁻¹ᵁ openSubset) point membership sectionValue := by
  rw [pushforwardStalkMap, TopCat.Presheaf.germ]
  erw [Limits.colimit.ι_desc_apply]
  rfl

noncomputable abbrev stalkAlgebra : Algebra (baseScheme.presheaf.stalk (morphism point)) (sourceScheme.presheaf.stalk point) :=
  (morphism.stalkMap point).hom.toAlgebra

attribute [local instance] stalkAlgebra

noncomputable abbrev stalkModule (moduleType : Type*) [AddCommGroup moduleType] [Module (sourceScheme.presheaf.stalk point) moduleType] :
    Module (baseScheme.presheaf.stalk (morphism point)) moduleType :=
  Module.compHom moduleType (morphism.stalkMap point).hom

attribute [local instance] stalkModule

instance (moduleType : Type*) [AddCommGroup moduleType] [Module (sourceScheme.presheaf.stalk point) moduleType] :
    IsScalarTower (baseScheme.presheaf.stalk (morphism point)) (sourceScheme.presheaf.stalk point) moduleType :=
  ⟨fun leftValue rightValue inclusion ↦ mul_smul (morphism.stalkMap point leftValue) rightValue inclusion⟩

noncomputable def pullbackStalkAddHom (moduleSheaf : baseScheme.Modules) :
    moduleSheaf.presheaf.stalk (morphism point) →+ ((pullback morphism).obj moduleSheaf).presheaf.stalk point :=
  (pushforwardStalkMap morphism point _).comp
    (((pullbackPushforwardAdjunction morphism).unit.app moduleSheaf).stalkLinearMap (morphism point)).toAddMonoidHom

variable {morphism point} in
@[simp]
lemma pullbackStalkAddHom_germ (moduleSheaf : baseScheme.Modules) {openSubset : baseScheme.Opens} (membership : morphism point ∈ openSubset)
    (element : Γ(moduleSheaf, openSubset)) :
    pullbackStalkAddHom morphism point moduleSheaf (moduleSheaf.presheaf.germ openSubset (morphism point) membership element) =
      ((pullback morphism).obj moduleSheaf).presheaf.germ (morphism ⁻¹ᵁ openSubset) point membership
        (((pullbackPushforwardAdjunction morphism).unit.app moduleSheaf).app openSubset element) := by
  rw [pullbackStalkAddHom, AddMonoidHom.comp_apply]
  erw [Hom.stalkLinearMap_germ]
  exact pushforwardStalkMap_germ _ membership _

noncomputable def pullbackStalkLinearMap (moduleSheaf : baseScheme.Modules) :
    moduleSheaf.presheaf.stalk (morphism point) →ₗ[baseScheme.presheaf.stalk (morphism point)] ((pullback morphism).obj moduleSheaf).presheaf.stalk point :=
  stalkLinearMapMk (pullbackStalkAddHom morphism point moduleSheaf) fun openSubset membership scalar element ↦ by
    rw [pullbackStalkAddHom_germ, pullbackStalkAddHom_germ, Hom.app_smul]
    refine (germ_smul ((pullback morphism).obj moduleSheaf) point membership (morphism.app openSubset scalar) _).trans ?_
    exact (congrArg (· • _) (Scheme.Hom.germ_stalkMap_apply morphism openSubset point membership scalar)).symm

variable {morphism point} in
@[simp]
lemma pullbackStalkLinearMap_germ (moduleSheaf : baseScheme.Modules) {openSubset : baseScheme.Opens} (membership : morphism point ∈ openSubset)
    (element : Γ(moduleSheaf, openSubset)) :
    pullbackStalkLinearMap morphism point moduleSheaf (moduleSheaf.presheaf.germ openSubset (morphism point) membership element) =
      ((pullback morphism).obj moduleSheaf).presheaf.germ (morphism ⁻¹ᵁ openSubset) point membership
        (((pullbackPushforwardAdjunction morphism).unit.app moduleSheaf).app openSubset element) :=
  pullbackStalkAddHom_germ moduleSheaf membership element

/-- The tensor-product comparison for the stalk of a pulled-back module. -/
noncomputable def pullbackStalkMap (moduleSheaf : baseScheme.Modules) :
    sourceScheme.presheaf.stalk point ⊗[baseScheme.presheaf.stalk (morphism point)] moduleSheaf.presheaf.stalk (morphism point) →ₗ[sourceScheme.presheaf.stalk point]
      ((pullback morphism).obj moduleSheaf).presheaf.stalk point :=
  (pullbackStalkLinearMap morphism point moduleSheaf).liftBaseChange _

lemma comp_pullbackStalkLinearMap_eq (moduleSheaf : baseScheme.Modules) (moduleType : Type u) [AddCommGroup moduleType]
    [Module (sourceScheme.presheaf.stalk point) moduleType]
    (linearMap : ((pullback morphism).obj moduleSheaf).presheaf.stalk point →ₗ[sourceScheme.presheaf.stalk point] moduleType) :
    linearMap.restrictScalars (baseScheme.presheaf.stalk (morphism point)) ∘ₗ pullbackStalkLinearMap morphism point moduleSheaf =
      (skyscraperHomEquiv (morphism point) moduleType moduleSheaf).symm
        ((pullbackPushforwardAdjunction morphism).homEquiv _ _ (skyscraperHomEquiv point moduleType _ linearMap) ≫
          (pushforwardSkyscraperIso morphism point moduleType rfl).hom) := by
  refine LinearMap.ext fun leftValue ↦ ?_
  obtain ⟨openSubset, membership, element, rfl⟩ := moduleSheaf.presheaf.exists_germ_eq leftValue
  rw [LinearMap.comp_apply, pullbackStalkLinearMap_germ, LinearMap.restrictScalars_apply]
  simp only [skyscraperHomEquiv, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, LinearMap.comp_apply,
    Adjunction.homEquiv_unit]
  erw [Hom.stalkLinearMap_germ, skyscraperStalkEval_germ]
  rfl

/-- The stalk of a pullback is extension of scalars along the local-ring map. -/
theorem bijective_pullbackStalkMap (moduleSheaf : baseScheme.Modules) :
    Function.Bijective (pullbackStalkMap morphism point moduleSheaf) := by
  refine bijective_of_forall_bijective_comp _ fun moduleType _ _ ↦ ?_
  have : (fun linearMap ↦ linearMap ∘ₗ pullbackStalkMap morphism point moduleSheaf) = LinearMap.liftBaseChangeEquiv _ ∘
      (fun linearMap ↦ (skyscraperHomEquiv (morphism point) moduleType moduleSheaf).symm
        ((pullbackPushforwardAdjunction morphism).homEquiv _ _ (skyscraperHomEquiv point moduleType _ linearMap) ≫
          (pushforwardSkyscraperIso morphism point moduleType rfl).hom)) := by
    ext linearMap : 1
    rw [Function.comp_apply, ← comp_pullbackStalkLinearMap_eq, pullbackStalkMap,
      LinearMap.liftBaseChange_comp]
  rw [this]
  refine (LinearEquiv.bijective _).comp ((Equiv.bijective _).comp ?_)
  have postcompose_bijective : Function.Bijective
      fun coefficientMap : moduleSheaf ⟶ (pushforward morphism).obj (skyscraper point moduleType) ↦
        coefficientMap ≫ (pushforwardSkyscraperIso morphism point moduleType rfl).hom :=
    ⟨fun leftValue rightValue equality ↦ by simpa using congrArg (· ≫ (pushforwardSkyscraperIso morphism point moduleType rfl).inv) equality,
      fun rightValue ↦ ⟨rightValue ≫ (pushforwardSkyscraperIso morphism point moduleType rfl).inv, by simp⟩⟩
  exact postcompose_bijective.comp ((Equiv.bijective _).comp (Equiv.bijective _))

/-- The stalk comparison commutes with morphisms of the coefficient module. -/
lemma pullbackStalkMap_naturality {moduleSheaf moduleSheaf' : baseScheme.Modules} (coefficientMap : moduleSheaf ⟶ moduleSheaf')
    (tensorElement : sourceScheme.presheaf.stalk point ⊗[baseScheme.presheaf.stalk (morphism point)] moduleSheaf.presheaf.stalk (morphism point)) :
    pullbackStalkMap morphism point moduleSheaf' (LinearMap.lTensor _ (coefficientMap.stalkLinearMap (morphism point)) tensorElement) =
      ((pullback morphism).map coefficientMap).stalkLinearMap point (pullbackStalkMap morphism point moduleSheaf tensorElement) := by
  induction tensorElement using TensorProduct.induction_on with
  | zero => simp
  | add tensorElement tensorElement' left_image left_image' => simp only [map_add, left_image, left_image']
  | tmul leftValue rightValue =>
    obtain ⟨openSubset, membership, element, rfl⟩ := moduleSheaf.presheaf.exists_germ_eq rightValue
    simp only [pullbackStalkMap, LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul,
      Hom.stalkLinearMap_germ, pullbackStalkLinearMap_germ, LinearMap.map_smul]
    congr 2
    exact congrArg (fun coefficientMap : moduleSheaf ⟶ (pushforward morphism).obj ((pullback morphism).obj moduleSheaf') ↦ coefficientMap.app openSubset element)
      ((pullbackPushforwardAdjunction morphism).unit.naturality coefficientMap)

end AlgebraicGeometry.Scheme.Modules
