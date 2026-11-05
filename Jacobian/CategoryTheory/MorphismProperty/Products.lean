import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Data.Fintype.Option
import Jacobian.CategoryTheory.Limits.Shapes.PiProd

/-!
# Morphism properties of products in over categories

A morphism property stable under base change and composition holds for the
structure morphism of a binary product in an over category whenever it holds
for both factors. If it also contains identities, the same holds for finite
products. The finite-product argument splits an `Option`-indexed product into
one factor and the product of the remaining factors.
-/

noncomputable section

set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

universe w v u

open CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

variable {categoryType : Type u} [Category.{v} categoryType]

variable (property : MorphismProperty categoryType) [property.IsStableUnderBaseChange]
    {baseObject : categoryType}

/-- Isomorphic objects of an over category have structure morphisms with the same property. -/
lemma hom_of_iso {firstObject secondObject : Over baseObject}
    (identification : firstObject ≅ secondObject) (second_property : property secondObject.hom) :
    property firstObject.hom := by
  have : IsIso identification.hom.left :=
    inferInstanceAs (IsIso ((Over.forget baseObject).map identification.hom))
  rw [← Over.w identification.hom, property.cancel_left_of_respectsIso]
  exact second_property

attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback

section ProductMap

variable [HasPullbacks categoryType] {firstObject secondObject secondTarget : Over baseObject}


/-- The underlying morphism of `prod.map (𝟙 firstObject) morphism` is, up to the canonical identification of the
binary product in `Over baseObject` with the fibre product over `baseObject`, the base change of `morphism.left` along
`pullback.snd firstObject.hom secondTarget.hom`. -/
private lemma isPullback_pullbackMap_id (morphism : secondObject ⟶ secondTarget) :
    IsPullback (pullback.snd firstObject.hom secondObject.hom)
      (pullback.map firstObject.hom secondObject.hom firstObject.hom secondTarget.hom (𝟙 firstObject.left) morphism.left (𝟙 baseObject) (by simp)
        (by simp [Over.w])) morphism.left (pullback.snd firstObject.hom secondTarget.hom) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback firstObject.hom secondTarget.hom).flip
  have : pullback.map firstObject.hom secondObject.hom firstObject.hom secondTarget.hom (𝟙 firstObject.left) morphism.left (𝟙 baseObject) (by simp)
      (by simp [Over.w]) ≫ pullback.fst firstObject.hom secondTarget.hom = pullback.fst firstObject.hom secondObject.hom := by simp
  rw [this, Over.w morphism]
  exact (IsPullback.of_hasPullback firstObject.hom secondObject.hom).flip

/-- Up to the canonical identification of binary products in `Over baseObject` with fibre products over
`baseObject`, the underlying morphism of `prod.map (𝟙 firstObject) morphism` is `pullback.map`. -/
private lemma prod_map_id_left_comp_prodLeftIsoPullback_hom (morphism : secondObject ⟶ secondTarget) :
    (prod.map (𝟙 firstObject) morphism).left ≫ (Over.prodLeftIsoPullback firstObject secondTarget).hom =
      (Over.prodLeftIsoPullback firstObject secondObject).hom ≫
        pullback.map firstObject.hom secondObject.hom firstObject.hom secondTarget.hom (𝟙 firstObject.left) morphism.left (𝟙 baseObject) (by simp)
          (by simp [Over.w]) := by
  ext
  · simp [← Over.comp_left]
  · simp [← Over.comp_left]

/-- a morphism property stable under base change is stable under taking the product with the
identity in an over category: if `morphism : secondObject ⟶ secondTarget` in `Over baseObject` satisfies `property morphism.left`, then
`property (prod.map (𝟙 firstObject) morphism).left`. -/
theorem left_prod_map_id (morphism : secondObject ⟶ secondTarget) (morphism_property : property morphism.left) : property (prod.map (𝟙 firstObject) morphism).left := by
  rw [← property.cancel_right_of_respectsIso _ (Over.prodLeftIsoPullback firstObject secondTarget).hom,
    prod_map_id_left_comp_prodLeftIsoPullback_hom, property.cancel_left_of_respectsIso]
  exact property.of_isPullback (isPullback_pullbackMap_id morphism) morphism_property

end ProductMap

variable [HasPullbacks categoryType] [property.IsStableUnderComposition]

/-- A base-change- and composition-stable property holds for the structure morphism of a
binary product in an over category if it holds for both factors. -/
theorem left_prod_hom (firstObject secondObject : Over baseObject)
    (first_property : property firstObject.hom) (second_property : property secondObject.hom) :
    property (firstObject ⨯ secondObject).hom := by
  have factorization : (Over.prodLeftIsoPullback firstObject secondObject).hom ≫
      pullback.fst firstObject.hom secondObject.hom ≫ firstObject.hom =
        (firstObject ⨯ secondObject).hom := by
    rw [Over.prodLeftIsoPullback_hom_fst_assoc, Over.w]
  rw [← factorization, property.cancel_left_of_respectsIso]
  exact property.comp_mem _ _
    (property.of_isPullback (IsPullback.of_hasPullback firstObject.hom secondObject.hom).flip
      second_property) first_property

/-- A base-change- and composition-stable property containing identities holds for the
structure morphism of a finite product if it holds for every factor. -/
theorem pi_hom [property.ContainsIdentities] [HasFiniteProducts (Over baseObject)]
    {indexType : Type w} [Finite indexType] (family : indexType → Over baseObject)
    (factor_property : ∀ index, property (family index).hom) : property (∏ᶜ family).hom := by
  refine Finite.induction_empty_option
    (P := fun finiteIndex ↦ ∀ [Finite finiteIndex] (family : finiteIndex → Over baseObject),
      (∀ index, property (family index).hom) → property (∏ᶜ family).hom)
    ?_ ?_ ?_ indexType family factor_property
  · intro firstIndex secondIndex equivalence induction_hyp _ family factor_property
    have : Finite firstIndex := Finite.of_equiv _ equivalence.symm
    exact property.hom_of_iso
      (Pi.whiskerEquiv equivalence fun index ↦ Iso.refl (family (equivalence index))).symm
      (induction_hyp (fun index ↦ family (equivalence index))
        fun index ↦ factor_property (equivalence index))
  · intro _ family _
    have terminalProduct : IsTerminal (∏ᶜ family) :=
      IsTerminal.ofUniqueHom (fun _ ↦ Pi.lift fun index ↦ index.elim)
        fun _ _ ↦ Pi.hom_ext _ _ fun index ↦ index.elim
    exact property.hom_of_iso (terminalProduct.uniqueUpToIso Over.mkIdTerminal)
      (by simpa using property.id_mem baseObject)
  · intro smallerIndex _ induction_hyp _ family factor_property
    exact property.hom_of_iso (piOptionIso family)
      (property.left_prod_hom _ _ (factor_property none)
        (induction_hyp _ fun index ↦ factor_property (some index)))

end CategoryTheory.MorphismProperty
