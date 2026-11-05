import Jacobian.AlgebraicGeometry.IdealSheaf.RelativeCartierPullback
import Jacobian.RingTheory.Flat.RegularPrincipal

/-!
# Fibrewise Cartier divisors

For a flat morphism locally of finite presentation, a locally principal ideal
whose fibres are effective Cartier is itself effective Cartier and defines a
flat closed subscheme over the base.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}}

/-- A locally principal ideal is principal on arbitrarily small affine neighborhoods. -/
lemma IsLocallyPrincipal.exists_isPrincipal_le {J : X.IdealSheafData}
    (hJ : J.IsLocallyPrincipal) {x : X} {O : X.Opens} (hx : x ∈ O) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ O ∧ (J.ideal U).IsPrincipal := by
  obtain ⟨U₀, hxU₀, a, ha⟩ := hJ x
  obtain ⟨V, hVaff, hxV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (U := U₀.1 ⊓ O) (x := x) ⟨hxU₀, hx⟩
  refine ⟨⟨V, hVaff⟩, hxV, hVU.trans inf_le_right,
    ⟨(X.presheaf.map (homOfLE (hVU.trans inf_le_left)).op).hom a, ?_⟩⟩
  rw [← J.map_ideal (U := ⟨V, hVaff⟩) (V := U₀) (hVU.trans inf_le_left), ha,
    Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]
  rfl

/-- Fibrewise regular local equations give an effective Cartier divisor flat over the base. -/
theorem IsLocallyPrincipal.isInvertible_and_flat (π : X ⟶ S) [Flat π]
    [LocallyOfFinitePresentation π] {J : X.IdealSheafData} (hJ : J.IsLocallyPrincipal)
    (hfib : ∀ s : S, (J.comap (π.fiberι s)).IsInvertible) :
    J.IsInvertible ∧ Flat (J.subschemeι ≫ π) := by
  have key (x : X) : ∃ (W : S.affineOpens) (V : X.affineOpens) (hVW : V.1 ≤ π ⁻¹ᵁ W.1),
      x ∈ V.1 ∧ (J.ideal V).IsRegularPrincipal ∧
        ((J.subschemeι.app V.1).hom.comp (π.appLE W V hVW).hom).Flat := by
    obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (x := π x) (U := ⊤) trivial
    obtain ⟨U, hxU, hUW, hJU⟩ := hJ.exists_isPrincipal_le (O := π ⁻¹ᵁ W) hsW
    have hU : IsAffineOpen U.1 := U.2
    obtain ⟨q, hq⟩ : x ∈ Set.range hU.fromSpec := by
      rw [IsAffineOpen.range_fromSpec]
      exact hxU
    have hsW' : ⊤ ≤ S.fromSpecResidueField (π x) ⁻¹ᵁ W := fun y _ ↦ by
      rw [Scheme.Hom.mem_preimage, Scheme.fromSpecResidueField_apply]
      exact hsW
    let := (π.appLE W U hUW).hom.toAlgebra
    let := ((S.fromSpecResidueField (π x)).appLE W ⊤ hsW').hom.toAlgebra
    have : Module.Flat Γ(S, W) Γ(X, U) := π.flat_appLE hW U.2 hUW
    have : Algebra.FinitePresentation Γ(S, W) Γ(X, U) :=
      HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) π inferInstance ⟨W, hW⟩ U hUW
    have := q.isPrime
    obtain ⟨g, hgq, hg⟩ := Algebra.exists_notMem_isRegularPrincipal_and_flat_of_fiber
      (isField_residueField_sections _) (J.ideal U) hJU q.asIdeal
      (ker_appLE_fromSpecResidueField π _ hW hsW' hU hUW q (by rw [hq]))
      (exists_isRegularPrincipal_map_tensorProduct_of_isInvertible_comap_fiberι π _ (hfib _)
        hW hsW' U hUW)
    let D := X.affineBasicOpen (U := U) g
    have hDU : D.1 ≤ U.1 := X.basicOpen_le g
    let := (X.presheaf.map (homOfLE hDU).op).hom.toAlgebra
    have : IsLocalization.Away g Γ(X, D) := hU.isLocalization_of_eq_basicOpen g (homOfLE hDU) rfl
    obtain ⟨h₁, h₂⟩ := hg Γ(X, D) Γ(J.subscheme, J.subschemeι ⁻¹ᵁ D) (J.subschemeι.app D).hom
      (J.subschemeι_app_surjective D) (by
        rw [ker_subschemeι_app, ← J.map_ideal hDU]
        rfl)
    refine ⟨⟨W, hW⟩, D, hDU.trans hUW, ?_, ?_, ?_⟩
    · have : q ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen g := by
        rw [hU.fromSpec_preimage_basicOpen]
        exact hgq
      rw [← hq]
      exact this
    · rw [← J.map_ideal hDU]
      exact h₁
    · rw [← Scheme.Hom.appLE_map π hUW (homOfLE hDU).op]
      exact h₂
  refine ⟨fun x ↦ ?_, ?_⟩
  · obtain ⟨W, V, hVW, hxV, hV, -⟩ := key x
    exact ⟨V, hxV, hV⟩
  · rw [HasRingHomProperty.iff_exists_appLE (P := @Flat)
      (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.Flat.holdsForLocalizationAway).left]
    intro d
    obtain ⟨W, V, hVW, hxV, -, hflat⟩ := key (J.subschemeι d)
    refine ⟨W, ⟨_, V.2.preimage J.subschemeι⟩, hxV, J.subschemeι.preimage_mono hVW, ?_⟩
    rwa [← Scheme.Hom.appLE_comp_appLE _ _ _ V.1 _ hVW le_rfl, CommRingCat.hom_comp,
      ← Scheme.Hom.app_eq_appLE]

end AlgebraicGeometry.Scheme.IdealSheafData
