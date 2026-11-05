import Jacobian.AlgebraicGeometry.Modules.LocalIsomorphism
import Jacobian.AlgebraicGeometry.Modules.Vanishing

/-!
# Isomorphisms on an open subset

A morphism of module sheaves is an isomorphism after restriction to an open when
it is bijective on sections over the affine opens contained in that open.
Invertibility over an open subset is preserved by pullback.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A morphism which is an isomorphism over an open `W` is bijective on sections over every
open contained in `W`. -/
lemma bijective_app_of_isIso_restrict (φ : M ⟶ N) {W V : X.Opens}
    [IsIso ((restrictFunctor W.ι).map φ)] (hV : V ≤ W) : Function.Bijective (φ.app V) := by
  obtain ⟨V', rfl⟩ : ∃ V' : W.toScheme.Opens, W.ι ''ᵁ V' = V :=
    ⟨W.ι ⁻¹ᵁ V, by
      rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, inf_eq_right.2 hV]⟩
  exact ConcreteCategory.bijective_of_isIso (((restrictFunctor W.ι).map φ).app V')

/-- A morphism is an isomorphism over an open if it is bijective on sections over all affine
opens contained in that open. -/
lemma isIso_restrict_of_bijective_app (φ : M ⟶ N) (W : X.Opens)
    (h : ∀ V : X.Opens, IsAffineOpen V → V ≤ W → Function.Bijective (φ.app V)) :
    IsIso ((restrictFunctor W.ι).map φ) :=
  isIso_of_bijective_app_of_isAffineOpen _ fun V hV ↦
    h _ (hV.image_of_isOpenImmersion W.ι) ((W.ι.image_le_opensRange V).trans (by simp))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback is an isomorphism above any open on which a module morphism is an isomorphism. -/
lemma isIso_restrict_pullback_map {sourceScheme targetScheme : Scheme.{u}}
    (baseMap : sourceScheme ⟶ targetScheme) {sourceModule targetModule : targetScheme.Modules}
    (moduleMap : sourceModule ⟶ targetModule) (openSubset : targetScheme.Opens)
    [IsIso ((restrictFunctor openSubset.ι).map moduleMap)] :
    IsIso ((restrictFunctor (baseMap ⁻¹ᵁ openSubset).ι).map ((pullback baseMap).map moduleMap)) := by
  rw [NatIso.isIso_map_iff (restrictFunctorIsoPullback (baseMap ⁻¹ᵁ openSubset).ι)]
  have : IsIso ((pullback openSubset.ι).map moduleMap) := by
    rw [← NatIso.isIso_map_iff (restrictFunctorIsoPullback openSubset.ι)]
    infer_instance
  have comparison : pullback baseMap ⋙ pullback (baseMap ⁻¹ᵁ openSubset).ι ≅
      pullback openSubset.ι ⋙ pullback (baseMap ∣_ openSubset) :=
    pullbackComp _ _ ≪≫ pullbackCongr (morphismRestrict_ι baseMap openSubset).symm ≪≫
      (pullbackComp _ _).symm
  exact (NatIso.isIso_map_iff comparison moduleMap).2
    (inferInstanceAs (IsIso ((pullback (baseMap ∣_ openSubset)).map
      ((pullback openSubset.ι).map moduleMap))))

/-- Vanishing of a module-sheaf morphism can be checked on an open cover. -/
lemma hom_eq_zero_of_restrict {sourceModule targetModule : X.Modules} (morphism : sourceModule ⟶ targetModule) {indexType : Type*} (cover : indexType → X.Opens)
    (coverTop : ⨆ index, cover index = ⊤) (restrictionZero : ∀ index, (restrictFunctor (cover index).ι).map morphism = 0) : morphism = 0 := by
  have componentZero (index : indexType) (testOpen : X.Opens) (contained : testOpen ≤ cover index) : morphism.app testOpen = 0 := by
    have key : ∀ otherOpen : X.Opens, otherOpen = testOpen → morphism.app otherOpen = 0 → morphism.app testOpen = 0 := by
      rintro _ rfl restrictionZero
      exact restrictionZero
    refine key _ ?_ (by
      have := congrArg (fun ψ ↦ Hom.app ψ ((cover index).ι ⁻¹ᵁ testOpen)) (restrictionZero index)
      exact this)
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 contained
  ext openSubset sectionValue
  change morphism.app openSubset sectionValue = 0
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨targetModule.presheaf, targetModule.isSheaf⟩ (fun index ↦ openSubset ⊓ cover index) openSubset
    (fun _ ↦ homOfLE inf_le_left) (fun point membership ↦ ?_) _ 0 fun index ↦ ?_
  · obtain ⟨index, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (coverTop.ge (Set.mem_univ point))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨index, membership, hi⟩
  · rw [map_zero]
    have := ConcreteCategory.congr_hom
      (morphism.mapPresheaf.naturality (homOfLE (inf_le_left : openSubset ⊓ cover index ≤ openSubset)).op) sectionValue
    refine (this.symm.trans ?_)
    change morphism.app (openSubset ⊓ cover index) _ = 0
    rw [componentZero index _ inf_le_right]
    rfl

/-- A morphism of `𝒪_X`-modules which is a monomorphism over every member of an open cover is a
monomorphism. -/
lemma mono_of_restrict {sourceModule targetModule : X.Modules} (morphism : sourceModule ⟶ targetModule) {indexType : Type*} (cover : indexType → X.Opens)
    (coverTop : ⨆ index, cover index = ⊤) (restrictionZero : ∀ index, Mono ((restrictFunctor (cover index).ι).map morphism)) : Mono morphism := by
  refine Preadditive.mono_of_cancel_zero _ fun {testModule} testMorphism compositeZero ↦ ?_
  refine hom_eq_zero_of_restrict testMorphism cover coverTop fun index ↦ ?_
  rw [← cancel_mono ((restrictFunctor (cover index).ι).map morphism), ← Functor.map_comp,
    compositeZero, zero_comp]
  rfl


end AlgebraicGeometry.Scheme.Modules
