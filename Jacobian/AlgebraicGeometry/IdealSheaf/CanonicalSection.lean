import Jacobian.AlgebraicGeometry.Modules.ZeroLocusTensor

/-!
# The canonical section of an effective divisor

An effective Cartier ideal is the zero ideal of its inclusion in the structure
sheaf. Dualizing this inclusion gives a section of the divisor line bundle
whose scheme-theoretic zero locus is precisely the divisor. On a nonempty scheme,
the complement of an effective Cartier divisor is nonempty.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The zero ideal of the inclusion of a Cartier ideal is that ideal. -/
theorem IsInvertible.zeroLocus_toModulesι {J : X.IdealSheafData} (hJ : J.IsInvertible) :
    letI := hJ.isInvertible_toModules
    Modules.Hom.zeroLocus J.toModulesι = J := by
  letI := hJ.isInvertible_toModules
  have key (x : X) : ∃ U : X.affineOpens, x ∈ U.1 ∧
      (Modules.Hom.zeroLocus J.toModulesι).ideal U = J.ideal U := by
    obtain ⟨U, hxU, b, -, hU⟩ := hJ x
    obtain ⟨s, hs⟩ := J.exists_toModulesι_app_eq (hU ▸ Ideal.mem_span_singleton_self b)
    have he := hJ.isFreeGenerator s fun V h ↦ by
      rw [hs, ← J.map_ideal h, hU, Ideal.map_span, Set.image_singleton]
      rfl
    refine ⟨U, hxU, ?_⟩
    rw [Modules.Hom.ideal_zeroLocus _ U he (Modules.isFreeGenerator_one U.1) (b := b), hU]
    exact hs.trans (mul_one b).symm
  choose U hxU hU using key
  exact ext_of_iSup_eq_top U
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩) hU

/-- The canonical section of the divisor line bundle vanishes precisely on the divisor. -/
theorem IsInvertible.exists_zeroLocus_eq {J : X.IdealSheafData} (hJ : J.IsInvertible) :
    letI := hJ.isInvertible_toModules
    ∃ sectionMap : 𝟙_ X.Modules ⟶ J.toModulesᵛ, Modules.Hom.zeroLocus sectionMap = J := by
  letI := hJ.isInvertible_toModules
  letI : (SheafOfModules.homObj (R := X.sheaf) J.toModules
      (SheafOfModules.unit X.ringCatSheaf)).IsInvertible :=
    Modules.isInvertible_dual J.toModules
  let sectionMap : 𝟙_ X.Modules ⟶ J.toModulesᵛ :=
    inv (Modules.dualEvaluation J.toModules) ≫ (J.toModulesι ▷ J.toModulesᵛ) ≫
      (λ_ J.toModulesᵛ).hom
  let comparison : Arrow.mk sectionMap ≅ Arrow.mk (J.toModulesι ▷ J.toModulesᵛ) :=
    Arrow.isoMk (asIso (Modules.dualEvaluation J.toModules)).symm (λ_ J.toModulesᵛ).symm
      (by simp [sectionMap])
  refine ⟨sectionMap, ?_⟩
  calc
    sectionMap.zeroLocus = (J.toModulesι ▷ J.toModulesᵛ).zeroLocus :=
      Modules.Hom.zeroLocus_eq_of_arrowIso sectionMap (J.toModulesι ▷ J.toModulesᵛ) comparison
    _ = J.toModulesι.zeroLocus := Modules.Hom.zeroLocus_whiskerRight J.toModulesι J.toModulesᵛ
    _ = J := hJ.zeroLocus_toModulesι

/-- Transporting the canonical section along a line-bundle isomorphism preserves its zero ideal. -/
theorem IsInvertible.exists_zeroLocus_eq_of_iso {scheme : Scheme.{u}}
    {cartierIdeal : scheme.IdealSheafData} (hJ : cartierIdeal.IsInvertible)
    {lineBundle : scheme.Modules} [lineBundle.IsInvertible]
    (equivalence : cartierIdeal.toModulesᵛ ≅ lineBundle) :
    ∃ sectionFamily : 𝟙_ scheme.Modules ⟶ lineBundle,
      Modules.Hom.zeroLocus sectionFamily = cartierIdeal := by
  letI := hJ.isInvertible_toModules
  obtain ⟨sectionFamily, hs⟩ := hJ.exists_zeroLocus_eq
  exact ⟨sectionFamily ≫ equivalence.hom, by
    rw [Modules.Hom.zeroLocus_eq_of_arrowIso (sectionFamily ≫ equivalence.hom) sectionFamily
      (Arrow.isoMk (Iso.refl _) equivalence.symm (by simp)), hs]⟩

section

variable {sourceScheme : Scheme.{u}} [Nonempty sourceScheme]

/-- The complement of an effective Cartier divisor on a nonempty scheme is nonempty. -/
theorem IsInvertible.exists_notMem_support {ideal : sourceScheme.IdealSheafData}
    (cartier : ideal.IsInvertible) : ∃ point : sourceScheme, point ∉ ideal.support := by
  obtain ⟨point⟩ := ‹Nonempty sourceScheme›
  obtain ⟨openSubset, point_mem, generator, regular, ideal_eq⟩ := cartier point
  by_contra! full_support
  have basicOpen_empty : sourceScheme.basicOpen generator = ⊥ := eq_bot_iff.mpr fun point mem ↦ by
    have vanishing := (mem_support_iff_of_mem (sourceScheme.basicOpen_le generator mem)).mp
      (full_support point)
    rw [Scheme.mem_zeroLocus_iff] at vanishing
    exact (vanishing generator (ideal_eq ▸ Ideal.subset_span rfl) mem).elim
  have := openSubset.2.isLocalization_basicOpen generator
  have trivial_sections : Subsingleton Γ(sourceScheme, sourceScheme.basicOpen generator) :=
    CommRingCat.subsingleton_of_isTerminal (sourceScheme.sheaf.isTerminalOfEqEmpty basicOpen_empty)
  obtain ⟨exponent, power_zero⟩ :=
    (IsLocalization.subsingleton_iff (M := Submonoid.powers generator)
      (S := Γ(sourceScheme, sourceScheme.basicOpen generator))).mp trivial_sections
  have : Nontrivial Γ(sourceScheme, openSubset.1) :=
    (sourceScheme.presheaf.germ openSubset.1 point point_mem).hom.domain_nontrivial
  have vanishing_power : generator ^ exponent = 0 := power_zero
  exact zero_notMem_nonZeroDivisors (vanishing_power ▸ pow_mem regular exponent)

end

end AlgebraicGeometry.Scheme.IdealSheafData
