import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Affine opens in a fibre product

Over an affine base, the product of two affine opens is an affine open of the
fibre product.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The product of two affine opens is affine inside a fibre product over
an affine base. -/
lemma isAffineOpen_preimage_inf_preimage_pullback {firstScheme secondScheme baseScheme : Scheme.{u}} [IsAffine baseScheme]
    (firstMap : firstScheme ⟶ baseScheme) (secondMap : secondScheme ⟶ baseScheme) {firstOpen : firstScheme.Opens} {secondOpen : secondScheme.Opens} (hA : IsAffineOpen firstOpen)
    (hB : IsAffineOpen secondOpen) :
    IsAffineOpen (pullback.fst firstMap secondMap ⁻¹ᵁ firstOpen ⊓ pullback.snd firstMap secondMap ⁻¹ᵁ secondOpen) := by
  have : IsAffine firstOpen.toScheme := hA
  have : IsAffine secondOpen.toScheme := hB
  obtain ⟨openMap, hm₁, hm₂⟩ : ∃ openMap : pullback (firstOpen.ι ≫ firstMap) (secondOpen.ι ≫ secondMap) ⟶ pullback firstMap secondMap,
      IsOpenImmersion openMap ∧ Set.range openMap =
        pullback.fst firstMap secondMap ⁻¹' (firstOpen : Set firstScheme) ∩ pullback.snd firstMap secondMap ⁻¹' (secondOpen : Set secondScheme) := by
    refine ⟨pullback.map (firstOpen.ι ≫ firstMap) (secondOpen.ι ≫ secondMap) firstMap secondMap firstOpen.ι secondOpen.ι (𝟙 _) (by simp) (by simp), ?_, ?_⟩
    · exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
        rfl rfl
    · rw [Scheme.Pullback.range_map]
      simp
  have := hm₁
  have hr : pullback.fst firstMap secondMap ⁻¹ᵁ firstOpen ⊓ pullback.snd firstMap secondMap ⁻¹ᵁ secondOpen = openMap.opensRange :=
    TopologicalSpace.Opens.ext (by rw [Scheme.Hom.coe_opensRange, hm₂]; rfl)
  rw [hr]
  exact isAffineOpen_opensRange _

end AlgebraicGeometry
