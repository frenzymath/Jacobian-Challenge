import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# Conditional cancellation of affine-local morphism properties

A cancellation rule for ring maps gives the contravariant cancellation rule
for the corresponding properties of scheme morphisms.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.HasRingHomProperty

variable {P P' : MorphismProperty Scheme.{u}}
  {Q Q' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
  [HasRingHomProperty P Q] [HasRingHomProperty P' Q']

/-- Conditional left cancellation for affine-local properties of scheme morphisms. -/
theorem of_comp_of
    (cancellation : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      ∀ (firstMap : R →+* S) (secondMap : S →+* T),
        Q' firstMap → Q (secondMap.comp firstMap) → Q secondMap)
    {X Y Z : Scheme.{u}} {firstMap : X ⟶ Y} {secondMap : Y ⟶ Z}
    (compositeProperty : P (firstMap ≫ secondMap)) (secondProperty : P' secondMap) :
    P firstMap := by
  wlog targetAffine : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _
      (secondMap.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro targetOpen
    have restricted := IsZariskiLocalAtTarget.restrict compositeProperty targetOpen.1
    rw [morphismRestrict_comp] at restricted
    exact this restricted (IsZariskiLocalAtTarget.restrict secondProperty targetOpen.1)
      inferInstance
  wlog middleAffine : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top Y)]
    intro middleOpen
    have restricted := comp_of_isOpenImmersion P (firstMap ⁻¹ᵁ middleOpen.1).ι
      (firstMap ≫ secondMap) compositeProperty
    rw [← morphismRestrict_ι_assoc] at restricted
    exact this restricted (comp_of_isOpenImmersion P' middleOpen.1.ι secondMap secondProperty)
      inferInstance
  wlog sourceAffine : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top X)]
    intro sourceOpen
    have restricted := comp_of_isOpenImmersion P sourceOpen.1.ι
      (firstMap ≫ secondMap) compositeProperty
    rw [← Category.assoc] at restricted
    exact this restricted inferInstance
  rw [iff_of_isAffine (P := P)] at compositeProperty ⊢
  exact cancellation _ _ (appTop P' secondMap secondProperty) compositeProperty

end AlgebraicGeometry.HasRingHomProperty
