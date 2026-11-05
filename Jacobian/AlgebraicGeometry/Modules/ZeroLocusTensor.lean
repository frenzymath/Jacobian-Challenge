import Jacobian.AlgebraicGeometry.Modules.ZeroLocusFunctorial

/-!
# Tensor products and zero schemes

The zero scheme of a morphism of line bundles is unchanged by tensoring with
a line bundle. If the zero scheme is an effective Cartier divisor, the target
line bundle is its divisor line bundle tensored with the source.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules} [M.IsInvertible] [N.IsInvertible]

/-- The ideal of the zero scheme of a composite is contained in that of its second factor. -/
theorem Hom.zeroLocus_comp_le {L : X.Modules} [L.IsInvertible]
    (ψ : L ⟶ M) (φ : M ⟶ N) : (ψ ≫ φ).zeroLocus ≤ φ.zeroLocus := by
  have key (x : X) : ∃ V : X.affineOpens, x ∈ V.1 ∧
      (ψ ≫ φ).zeroLocus.ideal V ≤ φ.zeroLocus.ideal V := by
    obtain ⟨U, hxU, -, ⟨eM, hM⟩, eN, hN⟩ :=
      exists_isFreeGenerator₂ M N (TopologicalSpace.Opens.mem_top x)
    obtain ⟨V, hxV, hVU, eL, hL⟩ := exists_isFreeGenerator L hxU
    obtain ⟨b, hb⟩ := (hM.map hVU).exists_smul_eq (ψ.app V.1 eL)
    obtain ⟨c, hc⟩ := (hN.map hVU).exists_smul_eq
      (φ.app V.1 (M.presheaf.map (homOfLE hVU).op eM))
    refine ⟨V, hxV, ?_⟩
    rw [Hom.ideal_zeroLocus φ V (hM.map hVU) (hN.map hVU) hc.symm,
      Hom.ideal_zeroLocus (ψ ≫ φ) V hL (hN.map hVU) (b := b * c) ?_]
    · exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left c b)
    · change φ.app V.1 (ψ.app V.1 eL) = _
      rw [← hb, Hom.app_smul, ← hc, mul_smul]
  choose V hxV hV using key
  exact IdealSheafData.le_of_iSup_eq_top V
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩) hV

private def arrowIsoPullbackWhiskerRightUnit {Y : Scheme.{u}} (g : Y ⟶ X)
    (φ : M ⟶ N) (P : X.Modules) (trivialization : (pullback g).obj P ≅ 𝟙_ Y.Modules) :
    Arrow.mk ((pullback g).map (φ ▷ P)) ≅ Arrow.mk ((pullback g).map φ) := by
  let firstIso : Arrow.mk ((pullback g).map (φ ▷ P)) ≅
      Arrow.mk ((pullback g).map φ ▷ (pullback g).obj P) :=
    Arrow.isoMk (pullbackTensorObjIso g M P) (pullbackTensorObjIso g N P) (by
      change Functor.OplaxMonoidal.δ (pullback g) M P ≫
          (pullback g).map φ ▷ (pullback g).obj P =
        (pullback g).map (φ ▷ P) ≫ Functor.OplaxMonoidal.δ (pullback g) N P
      exact Functor.OplaxMonoidal.δ_natural_left (pullback g) φ P)
  let secondIso : Arrow.mk ((pullback g).map φ ▷ (pullback g).obj P) ≅
      Arrow.mk ((pullback g).map φ ▷ 𝟙_ Y.Modules) :=
    Arrow.isoMk (whiskerLeftIso _ trivialization) (whiskerLeftIso _ trivialization)
      (MonoidalCategory.whisker_exchange ((pullback g).map φ) trivialization.hom)
  exact firstIso ≪≫ secondIso ≪≫
    Arrow.isoMk (ρ_ _) (ρ_ _) (MonoidalCategory.rightUnitor_naturality _).symm

/-- Tensoring with an invertible module sheaf leaves the zero scheme unchanged. -/
theorem Hom.zeroLocus_whiskerRight (φ : M ⟶ N) (P : X.Modules) [P.IsInvertible] :
    (φ ▷ P).zeroLocus = φ.zeroLocus := by
  have key (x : X) : ∃ V : X.affineOpens, x ∈ V.1 ∧
      (φ ▷ P).zeroLocus.ideal V = φ.zeroLocus.ideal V := by
    let invertible : P.IsInvertible := inferInstance
    obtain ⟨U, hxU, ⟨trivialization⟩⟩ := invertible.exists_isoUnit x
    have equality : (φ ▷ P).zeroLocus.comap U.ι = φ.zeroLocus.comap U.ι := by
      rw [Hom.comap_zeroLocus, Hom.comap_zeroLocus]
      exact Hom.zeroLocus_eq_of_arrowIso _ _
        (arrowIsoPullbackWhiskerRightUnit U.ι φ P trivialization)
    obtain ⟨V, hVaff, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (x := x) hxU
    have refinedEquality := congrArg (fun ideal ↦ ideal.comap (X.homOfLE hVU)) equality
    rw [← IdealSheafData.comap_comp, ← IdealSheafData.comap_comp, X.homOfLE_ι] at refinedEquality
    refine ⟨⟨V, hVaff⟩, hxV, ?_⟩
    rw [← IdealSheafData.map_topIso_ideal_top_comap_ι _ ⟨V, hVaff⟩,
      ← IdealSheafData.map_topIso_ideal_top_comap_ι _ ⟨V, hVaff⟩, refinedEquality]
  choose V hxV hV using key
  exact IdealSheafData.ext_of_iSup_eq_top V
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩) hV

/-- A regular line-bundle morphism identifies its target with the divisor line
bundle of its zero scheme tensored with its source. -/
theorem Hom.nonempty_iso_dual_toModules_tensorObj (φ : M ⟶ N)
    (hφ : φ.zeroLocus.IsInvertible) :
    Nonempty (N ≅ φ.zeroLocus.toModulesᵛ ⊗ M) := by
  let ψ : M ⊗ Nᵛ ⟶ unit X := φ ▷ Nᵛ ≫ dualEvaluation N
  have hψ : ψ.zeroLocus = φ.zeroLocus := by
    rw [← φ.zeroLocus_whiskerRight Nᵛ]
    exact (Hom.zeroLocus_eq_of_arrowIso (φ ▷ Nᵛ) ψ
      (Arrow.isoMk (Iso.refl _) (asIso (dualEvaluation N) : N ⊗ Nᵛ ≅ unit X)
        (by simp [ψ]))).symm
  rw [← hψ] at hφ ⊢
  obtain ⟨e⟩ := ψ.nonempty_iso_toModules_zeroLocus hφ
  letI := hφ.isInvertible_toModules
  let dN := tensorObjDualIsoUnit N
  let dJ := tensorObjDualIsoUnit ψ.zeroLocus.toModules
  exact ⟨(λ_ N).symm ≪≫ whiskerRightIso ((β_ _ _) ≪≫ dJ).symm N ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso _ (whiskerRightIso e.symm N ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso M ((β_ _ _) ≪≫ dN) ≪≫ ρ_ M)⟩

end AlgebraicGeometry.Scheme.Modules
