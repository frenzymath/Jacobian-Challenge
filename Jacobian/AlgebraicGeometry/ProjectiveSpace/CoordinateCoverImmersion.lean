import Jacobian.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
import Jacobian.AlgebraicGeometry.ProjectiveSpace.CoordinateCover

/-!
# Projective immersions from affine coordinate covers

A finite coordinate cover with affine charts supplies enough homogeneous
sections to immerse a finite-type scheme into finite-coordinate projective space.
-/

set_option backward.isDefEq.respectTransparency false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.CoordinateCover

variable {scheme : Scheme.{schemeUniverse}} {coverIndex : Type schemeUniverse} (coordinates : scheme.CoordinateCover coverIndex)

lemma nonvanishing_coordPow (thirdIndex : coverIndex) {exponent : ℕ} (hn : 0 < exponent) :
    (coordinates.coordPow thirdIndex exponent).nonvanishing = coordinates.opens thirdIndex := by
  refine le_antisymm (iSup_le fun index ↦ ?_) ?_
  · rw [coordPow_s, Scheme.basicOpen_pow _ _ hn, coordinates.basicOpen_ratio]
    exact inf_le_right
  · rw [← inf_eq_right.mpr (le_top : coordinates.opens thirdIndex ≤ ⊤), ← coordinates.iSup_U, iSup_inf_eq]
    refine iSup_le fun index ↦ ?_
    rw [← coordinates.basicOpen_ratio, ← Scheme.basicOpen_pow _ _ hn, ← coordPow_s]
    exact le_iSup (fun index ↦ scheme.basicOpen ((coordinates.coordPow thirdIndex exponent).localSection index)) index

lemma exists_generators {base : Scheme.{schemeUniverse}} [IsAffine base] (structureMap : scheme ⟶ base) [LocallyOfFiniteType structureMap]
    (index : coverIndex) (hi : IsAffineOpen (coordinates.opens index)) :
    ∃ (otherExponent : Type schemeUniverse) (_ : Finite otherExponent) (otherElement : otherExponent → Γ(scheme, coordinates.opens index)),
      Subring.closure (Set.range ((coordinates.opens index).ι ≫ structureMap).appTop ∪
        Set.range fun μ ↦ (coordinates.opens index).topIso.inv (otherElement μ)) = ⊤ := by
  have : IsAffine (coordinates.opens index).toScheme := hi
  let : Algebra Γ(base, ⊤) Γ((coordinates.opens index).toScheme, ⊤) := ((coordinates.opens index).ι ≫ structureMap).appTop.hom.toAlgebra
  have hft : ((coordinates.opens index).ι ≫ structureMap).appTop.hom.FiniteType :=
    HasRingHomProperty.iff_of_isAffine.mp (inferInstance : LocallyOfFiniteType ((coordinates.opens index).ι ≫ structureMap))
  obtain ⟨localSection, hs⟩ := hft.out
  refine ⟨localSection, inferInstance, fun μ ↦ (coordinates.opens index).topIso.hom μ.1, ?_⟩
  have compatibility := congrArg Subalgebra.toSubring hs
  rw [Algebra.adjoin_eq_ring_closure] at compatibility
  have equivalence : (Set.range fun μ : localSection ↦ (coordinates.opens index).topIso.inv ((coordinates.opens index).topIso.hom μ.1)) = ↑localSection := by
    rw [show (fun μ : localSection ↦ (coordinates.opens index).topIso.inv ((coordinates.opens index).topIso.hom μ.1)) = fun μ ↦ μ.1 from
      funext fun μ ↦ Iso.hom_inv_id_apply _ _]
    ext point
    simp
  rw [equivalence]
  exact compatibility

theorem exists_isImmersion {base : Scheme.{schemeUniverse}} [IsAffine base] (structureMap : scheme ⟶ base) [LocallyOfFiniteType structureMap]
    [Finite coverIndex] (h𝒟 : ∀ index, IsAffineOpen (coordinates.opens index)) :
    ∃ (newIndex : Type schemeUniverse) (_ : Finite newIndex) (secondIndex : scheme ⟶ ℙ(newIndex; base)), IsImmersion secondIndex ∧ secondIndex ≫ ℙ(newIndex; base) ↘ base = structureMap := by
  classical
  have := Fintype.ofFinite coverIndex
  choose otherExponent hm otherElement ht using fun index ↦ coordinates.exists_generators structureMap index (h𝒟 index)
  have hU (index : coverIndex) : IsCompact (coordinates.opens index : Set scheme) := (h𝒟 index).isCompact
  have hU' (index : coverIndex) : IsQuasiSeparated (coordinates.opens index : Set scheme) := (h𝒟 index).isQuasiSeparated
  choose N₀ hN₀ using fun prime : Σ index, otherExponent index ↦ coordinates.exists_section hU hU' prime.1 (otherElement prime.1 prime.2)
  have : Finite (Σ index, otherExponent index) := inferInstance
  have := Fintype.ofFinite (Σ index, otherExponent index)
  set powerBound := max 1 (Finset.univ.sup N₀)
  have hN (prime : Σ index, otherExponent index) : powerBound ≥ N₀ prime :=
    (Finset.le_sup (Finset.mem_univ prime)).trans (le_max_right _ _)
  choose gradingIndex hσ' using fun prime ↦ hN₀ prime powerBound (hN prime)
  let newIndex : Type schemeUniverse := coverIndex ⊕ (Σ index, otherExponent index)
  let sectionFamily : newIndex → coordinates.Section powerBound := Sum.elim (fun index ↦ coordinates.coordPow index powerBound) gradingIndex
  have hσ (secondIndex : coverIndex) : Ideal.span (Set.range fun coordinate ↦ (sectionFamily coordinate).localSection secondIndex) = ⊤ := by
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨Sum.inl secondIndex, rfl⟩) ?_
    simp [sectionFamily, coordinates.ratio_self]
  let Φ := hom sectionFamily hσ structureMap
  have hpre (index : coverIndex) : Φ ⁻¹ᵁ ProjectiveSpace.standardOpen newIndex base (Sum.inl index) = coordinates.opens index := by
    rw [preimage_hom_standardOpen]
    exact coordinates.nonvanishing_coordPow index (lt_of_lt_of_le one_pos (le_max_left _ _))
  refine ⟨newIndex, inferInstance, Φ, ?_, hom_over sectionFamily hσ structureMap⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup
    (fun index : coverIndex ↦ ProjectiveSpace.standardOpen newIndex base (Sum.inl index)) ?_ fun index ↦ ?_
  · rintro _ ⟨point, rfl⟩
    obtain ⟨index, hi⟩ := Opens.mem_iSup.mp (coordinates.iSup_U.ge (Set.mem_univ point))
    refine SetLike.mem_coe.mpr (Opens.mem_iSup.mpr ⟨index, ?_⟩)
    change point ∈ Φ ⁻¹ᵁ ProjectiveSpace.standardOpen newIndex base (Sum.inl index)
    rw [hpre index]
    exact hi
  ·
    rw [← Scheme.Hom.resLE_eq_morphismRestrict,
      Scheme.Hom.resLE_congr Φ (U := ProjectiveSpace.standardOpen newIndex base (Sum.inl index)) le_rfl rfl
        (hpre index) @IsImmersion]
    have : IsAffine (coordinates.opens index).toScheme := h𝒟 index
    set openSubset := (coordinates.opens index).toScheme
    set localSection : newIndex → Γ(openSubset, ⊤) := fun coordinate ↦ (coordinates.opens index).topIso.inv ((sectionFamily coordinate).localSection index)
    have hs1 : localSection (Sum.inl index) = 1 := by simp [localSection, sectionFamily, coordinates.ratio_self]
    have hb : openSubset.basicOpen (localSection (Sum.inl index)) = ⊤ := by rw [hs1]; exact openSubset.basicOpen_one
    have : IsIso (openSubset.basicOpen (localSection (Sum.inl index))).ι := by
      rw [← openSubset.isoOfEq_hom_ι hb, ← Scheme.topIso_hom]
      infer_instance
    have hloc : (openSubset.basicOpen (localSection (Sum.inl index))).ι ≫
        Φ.resLE (ProjectiveSpace.standardOpen newIndex base (Sum.inl index)) (coordinates.opens index) (hpre index).ge =
        (ProjectiveSpace.homOfSections ((coordinates.opens index).ι ≫ structureMap) localSection (span_topIso_inv sectionFamily hσ index)).resLE
          (ProjectiveSpace.standardOpen newIndex base (Sum.inl index)) (openSubset.basicOpen (localSection (Sum.inl index)))
          (ProjectiveSpace.homOfSections_preimage_standardOpen _ localSection _ (Sum.inl index)).ge := by
      rw [← cancel_mono (ProjectiveSpace.standardOpen newIndex base (Sum.inl index)).ι, Category.assoc,
        Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι, ι_hom]
      rfl
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsImmersion
      (openSubset.basicOpen (localSection (Sum.inl index))).ι, hloc,
      ← MorphismProperty.cancel_right_of_respectsIso @IsImmersion _
        (ProjectiveSpace.standardOpenIso newIndex base (Sum.inl index)).hom,
      ProjectiveSpace.homOfSections_resLE_standardOpenIso_hom]
    refine isImmersion_homOfVector_divBasicOpen ((coordinates.opens index).ι ≫ structureMap) localSection (Sum.inl index) ⊤
      (isAffineOpen_top base) (by simp) ?_

    set restriction := (openSubset.basicOpen (localSection (Sum.inl index))).ι.appTop
    have hρ : Function.Surjective restriction.hom := by
      have : IsIso restriction := inferInstance
      exact (ConcreteCategory.bijective_of_isIso restriction).2
    have hdiv (coordinate : newIndex) : openSubset.divBasicOpen (localSection coordinate) (localSection (Sum.inl index)) = restriction (localSection coordinate) := by
      symm
      refine openSubset.eq_divBasicOpen ?_
      have h1 : ∀ point : Γ(openSubset, ⊤), point = 1 → restriction point = 1 := by rintro point rfl; exact map_one _
      rw [h1 _ hs1, mul_one]
    refine eq_top_iff.mpr ?_
    rw [← (RingHom.range_eq_top.mpr hρ), RingHom.range_eq_map, ← ht index, RingHom.map_closure]
    refine Subring.closure_mono ?_
    rintro _ ⟨point, (⟨element, rfl⟩ | ⟨μ, rfl⟩), rfl⟩
    · refine Or.inl ⟨(⊤ : base.Opens).ι.appTop element, ?_⟩
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        ← Scheme.Hom.comp_appTop, Scheme.Hom.resLE_comp_ι]
    · refine Or.inr ⟨⟨Sum.inr ⟨index, μ⟩, Sum.inr_ne_inl⟩, ?_⟩
      refine (hdiv (Sum.inr ⟨index, μ⟩)).trans ?_
      simp only [localSection, sectionFamily, Sum.elim_inr, (hσ' ⟨index, μ⟩).1]

end AlgebraicGeometry.Scheme.CoordinateCover
