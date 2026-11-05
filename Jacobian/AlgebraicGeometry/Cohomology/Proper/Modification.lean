import Jacobian.AlgebraicGeometry.Modules.AffineSections
import Jacobian.AlgebraicGeometry.Modules.PullbackSections
import Jacobian.AlgebraicGeometry.Modules.RestrictionIsomorphism
import Jacobian.LinearAlgebra.TensorProduct.Quotient

/-!
# Cohomology along a Chow modification

This module isolates the comparison morphism used after choosing a native Chow
modification.  Pullback of a quasi-coherent module is identified with its source
sections over affine opens where the modification is an isomorphism, and the
adjunction unit followed by a locally invertible map gives the corresponding
pushforward comparison on that open.

The finite-`H` input for the twisted projective module is supplied by the native
projective cohomology provider; this module does not replace that provider.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- A morphism which is an isomorphism over an open induces a bijection on pullback sections
over every affine open contained in that open. -/
lemma bijective_pullbackSection_of_isIso_morphismRestrict (π : X ⟶ Y)
    {U : Y.Opens} [IsIso (π ∣_ U)] (G : Y.Modules) [G.IsQuasicoherent] {V : Y.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ U) :
    Function.Bijective (pullbackSection π : Γ(G, V) → Γ((pullback π).obj G, π ⁻¹ᵁ V)) := by
  obtain ⟨V', rfl⟩ : ∃ V' : U.toScheme.Opens, U.ι ''ᵁ V' = V :=
    ⟨U.ι ⁻¹ᵁ V, by
      rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, inf_eq_right.2 hVU]⟩
  have hV' : IsAffineOpen V' := (U.ι.isAffineOpen_iff_of_isOpenImmersion).1 hV
  have hpre : (π ⁻¹ᵁ U).ι ''ᵁ ((π ∣_ U) ⁻¹ᵁ V') =
      π ⁻¹ᵁ (U.ι ''ᵁ V') :=
    image_morphismRestrict_preimage π U V'
  have hA : IsAffineOpen (π ⁻¹ᵁ (U.ι ''ᵁ V')) :=
    hpre ▸ (IsAffineOpen.preimage_of_isIso hV' (π ∣_ U)).image_of_isOpenImmersion _
  have hbij : Function.Bijective
      (π.appLE (U.ι ''ᵁ V') (π ⁻¹ᵁ (U.ι ''ᵁ V')) le_rfl).hom := by
    have h₁ : Function.Bijective
        (π.appLE (U.ι ''ᵁ V')
          ((π ⁻¹ᵁ U).ι ''ᵁ ((π ∣_ U) ⁻¹ᵁ V'))
          (image_morphismRestrict_preimage π U V').le).hom := by
      have := ConcreteCategory.bijective_of_isIso ((π ∣_ U).app V')
      rwa [morphismRestrict_app'] at this
    have h₂ : Function.Bijective
        (X.presheaf.map (homOfLE hpre.ge).op) := by
      have : ∀ {A B : X.Opens} (h : B ≤ A), A = B →
          IsIso (X.presheaf.map (homOfLE h).op) := by
        rintro A B h rfl
        rw [Subsingleton.elim (homOfLE h) (𝟙 _), op_id, X.presheaf.map_id]
        infer_instance
      have := this hpre.ge hpre
      exact ConcreteCategory.bijective_of_isIso _
    rw [← π.appLE_map (image_morphismRestrict_preimage π U V').le (homOfLE hpre.ge).op]
    rw [CategoryTheory.hom_comp]
    exact h₂.comp h₁
  obtain ⟨e, he⟩ := exists_linearEquiv_pullback_sections π G hV hA le_rfl
  let := (π.appLE (U.ι ''ᵁ V') (π ⁻¹ᵁ (U.ι ''ᵁ V')) le_rfl).hom.toAlgebra
  have hb := TensorProduct.bijective_one_tmul_of_surjective
    (M := Γ(G, U.ι ''ᵁ V')) (S := Γ(X, π ⁻¹ᵁ (U.ι ''ᵁ V')))
    hbij.2 (fun a ha m ↦ by
      rw [show a = 0 from hbij.1 ((RingHom.mem_ker.1 ha).trans (map_zero _).symm), zero_smul])
  have hid : (homOfLE (le_rfl : π ⁻¹ᵁ (U.ι ''ᵁ V') ≤ π ⁻¹ᵁ (U.ι ''ᵁ V'))).op = 𝟙 _ :=
    Subsingleton.elim _ _
  have key : (pullbackSection π : Γ(G, U.ι ''ᵁ V') → _) =
      e ∘ fun m ↦ (1 : Γ(X, π ⁻¹ᵁ (U.ι ''ᵁ V'))) ⊗ₜ[Γ(Y, U.ι ''ᵁ V')] m := by
    funext m
    rw [Function.comp_apply, he, hid, CategoryTheory.Functor.map_id]
    rfl
  rw [key]
  exact e.bijective.comp hb

/-- The adjunction unit followed by a map out of the pullback module. -/
def modificationComparison (π : X ⟶ Y) (G : Y.Modules) (E : X.Modules)
    (ψ : (pullback π).obj G ⟶ E) : G ⟶ (pushforward π).obj E :=
  (pullbackPushforwardAdjunction π).unit.app G ≫ (pushforward π).map ψ

/-- The comparison associated with a locally invertible map on a modification is an
isomorphism after restriction to the corresponding open. -/
lemma isIso_restrict_modificationComparison (π : X ⟶ Y) (G : Y.Modules) (E : X.Modules)
    [G.IsQuasicoherent] (ψ : (pullback π).obj G ⟶ E) (U : Y.Opens)
    [IsIso (π ∣_ U)] [IsIso ((restrictFunctor (π ⁻¹ᵁ U).ι).map ψ)] :
    IsIso ((restrictFunctor U.ι).map (modificationComparison π G E ψ)) := by
  let φ := modificationComparison π G E ψ
  refine isIso_restrict_of_bijective_app φ U fun V hV hVU ↦ ?_
  have h₁ := bijective_pullbackSection_of_isIso_morphismRestrict π G hV
    hVU
  have h₂ := bijective_app_of_isIso_restrict ψ
    (π.preimage_mono hVU : π ⁻¹ᵁ V ≤ π ⁻¹ᵁ U)
  exact h₂.comp h₁

end AlgebraicGeometry.Scheme.Modules
