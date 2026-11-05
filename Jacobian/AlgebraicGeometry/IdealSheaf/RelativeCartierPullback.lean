import Jacobian.AlgebraicGeometry.IdealSheaf.Colon
import Jacobian.AlgebraicGeometry.IdealSheaf.Image
import Jacobian.AlgebraicGeometry.IdealSheaf.RelativeCartier
import Jacobian.RingTheory.Flat.Exact

/-!
# Base change of relative effective Cartier divisors

Flatness of the divisor over the base ensures that its regular local equation
remains regular under arbitrary base change. The associated ideal and divisor
line bundles pull back to those of the base-changed divisor.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits
open scoped nonZeroDivisors AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}}

/-- A Cartier ideal has regular principal equations on arbitrarily small affine neighborhoods. -/
lemma IsInvertible.exists_isRegularPrincipal_le {J : X.IdealSheafData} (hJ : J.IsInvertible)
    {x : X} {O : X.Opens} (hx : x ∈ O) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ O ∧ (J.ideal U).IsRegularPrincipal := by
  obtain ⟨U₀, hxU₀, hU₀⟩ := hJ x
  obtain ⟨V, hVaff, hxV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (U := U₀.1 ⊓ O) (x := x) ⟨hxU₀, hx⟩
  exact ⟨⟨V, hVaff⟩, hxV, hVU.trans inf_le_right,
    J.isRegularPrincipal_ideal_of_le (hVU.trans inf_le_left) hU₀⟩

/-- A locally principal closed subscheme is locally of finite presentation over the base. -/
theorem IsLocallyPrincipal.locallyOfFinitePresentation_subschemeι_comp (π : X ⟶ S)
    [LocallyOfFinitePresentation π] {J : X.IdealSheafData} (hJ : J.IsLocallyPrincipal) :
    LocallyOfFinitePresentation (J.subschemeι ≫ π) := by
  have : LocallyOfFinitePresentation J.subschemeι := by
    rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
      (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.finitePresentation_holdsForLocalizationAway).left]
    intro d
    obtain ⟨U, hU, a, ha⟩ := hJ (J.subschemeι d)
    refine ⟨U, ⟨_, U.2.preimage J.subschemeι⟩, hU, le_rfl, ?_⟩
    rw [← Scheme.Hom.app_eq_appLE]
    refine RingHom.FinitePresentation.of_surjective _ (J.subschemeι_app_surjective U) ?_
    rw [ker_subschemeι_app, ha]
    exact ⟨{a}, by simp⟩
  infer_instance

/-- The closed subscheme defined by the pulled-back ideal is the base change of the divisor. -/
theorem flat_comap_subschemeι_comp_of_isPullback {π : X ⟶ S} {J : X.IdealSheafData}
    (hflat : Flat (J.subschemeι ≫ π)) {X' T : Scheme.{u}} {g' : X' ⟶ X} {π' : X' ⟶ T}
    {g : T ⟶ S} (h : IsPullback g' π' π g) : Flat ((J.comap g').subschemeι ≫ π') := by
  exact MorphismProperty.of_isPullback (P := @Flat)
    ((J.isPullback_comap g').flip.paste_vert h) hflat

/-- A Cartier ideal whose divisor is flat over the base remains Cartier after base change. -/
theorem IsInvertible.comap_of_isPullback {π : X ⟶ S} {J : X.IdealSheafData}
    (hJ : J.IsInvertible) (hflat : Flat (J.subschemeι ≫ π)) {X' T : Scheme.{u}} {g' : X' ⟶ X}
    {π' : X' ⟶ T} {g : T ⟶ S} (h : IsPullback g' π' π g) : (J.comap g').IsInvertible := by
  have key (x' : X') : ∃ (R : CommRingCat.{u}) (ι : Spec R ⟶ X'), IsOpenImmersion ι ∧
      x' ∈ Set.range ι ∧ (J.comap (ι ≫ g')).IsInvertible := by
    obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (x := π (g' x')) (U := ⊤) trivial
    obtain ⟨U, hxU, hUW, f, hf, hJU⟩ := hJ.exists_isRegularPrincipal_le (O := π ⁻¹ᵁ W) hsW
    have htW : π' x' ∈ g ⁻¹ᵁ W := by
      rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]
      exact hsW
    obtain ⟨V, hV, htV, hVW⟩ := exists_isAffineOpen_mem_and_subset htW
    obtain ⟨ι, hι, hιg, -, hrange⟩ :=
      h.exists_isOpenImmersion_spec_tensorProduct hW U.2 hUW hV hVW
    let := (π.appLE W U hUW).hom.toAlgebra
    let := (g.appLE W V hVW).hom.toAlgebra
    refine ⟨_, ι, hι, hrange x' hxU htV, ?_⟩
    rw [hιg]
    refine IsInvertible.of_specMap_ofHom_fromSpec U _ ?_
    rw [hJU, Ideal.map_span, Set.image_singleton]
    refine Ideal.isRegularPrincipal_span_singleton
      (Algebra.TensorProduct.includeLeftRingHom_mem_nonZeroDivisors_of_flat
        (J.subschemeι.app U.1).hom (J.subschemeι_app_surjective U) ?_ ?_ hf)
    · rw [ker_subschemeι_app, hJU]
    · rw [RingHom.algebraMap_toAlgebra]
      exact flat_app_subschemeι_comp_appLE hflat ⟨W, hW⟩ U hUW
  choose R ι hι hx' hinv using key
  have : ∀ x', IsOpenImmersion (ι x') := hι
  refine IsInvertible.of_iSup_opensRange_eq_top ι ?_ fun x' ↦ ?_
  · exact eq_top_iff.mpr fun x' _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x', hx' x'⟩
  · rw [← comap_comp]
    exact hinv x'

/-- Pullback of a Cartier divisor line bundle is the dual of the pulled-back ideal. -/
theorem IsInvertible.nonempty_pullback_dual_toModules_iso (g : X ⟶ S)
    {J : S.IdealSheafData} (hJ : J.IsInvertible) (hJ' : (J.comap g).IsInvertible) :
    Nonempty ((Modules.pullback g).obj J.toModulesᵛ ≅ (J.comap g).toModulesᵛ) := by
  letI : J.toModules.IsInvertible := hJ.isInvertible_toModules
  obtain ⟨comparison⟩ := hJ.nonempty_pullback_toModules_iso g hJ'
  exact ⟨Modules.pullbackDualIso g J.toModules ≪≫
    ((Modules.dualFunctor X).mapIso comparison.op).symm⟩

/-- Relative effective Cartier divisors are preserved by arbitrary base change. -/
theorem IsRelativeEffectiveCartier.isRelativeEffectiveCartier_comap_of_isPullback
    {π : X ⟶ S} {J : X.IdealSheafData} (hJ : J.IsRelativeEffectiveCartier π)
    {X' T : Scheme.{u}} {g' : X' ⟶ X} {π' : X' ⟶ T} {g : T ⟶ S}
    (h : IsPullback g' π' π g) : (J.comap g').IsRelativeEffectiveCartier π' :=
  ⟨hJ.1.comap_of_isPullback hJ.2 h, flat_comap_subschemeι_comp_of_isPullback hJ.2 h⟩

/-- Base change preserves a relative Cartier divisor together with its divisor line bundle. -/
theorem IsRelativeEffectiveCartier.comap_of_isPullback {π : X ⟶ S}
    {J : X.IdealSheafData} (hJ : J.IsRelativeEffectiveCartier π)
    {X' T : Scheme.{u}} {g' : X' ⟶ X} {π' : X' ⟶ T} {g : T ⟶ S}
    (h : IsPullback g' π' π g) :
    (J.comap g').IsRelativeEffectiveCartier π' ∧
      Nonempty ((J.comap g').toModulesᵛ ≅ (Modules.pullback g').obj J.toModulesᵛ) := by
  have pulledBack := hJ.isRelativeEffectiveCartier_comap_of_isPullback h
  exact ⟨pulledBack, (hJ.1.nonempty_pullback_dual_toModules_iso g' pulledBack.1).map Iso.symm⟩

end AlgebraicGeometry.Scheme.IdealSheafData
