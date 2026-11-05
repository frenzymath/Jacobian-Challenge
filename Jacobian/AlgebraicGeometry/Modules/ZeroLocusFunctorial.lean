import Jacobian.AlgebraicGeometry.Modules.ZeroLocus
import Jacobian.AlgebraicGeometry.Modules.FreeGeneratorPullback

/-!
# Functoriality of zero loci of line-bundle maps

The zero locus of a morphism between invertible module sheaves is invariant
under isomorphisms of arrows and commutes with arbitrary pullback. Both
statements follow from the local scalar equations of the morphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules} [M.IsInvertible] [N.IsInvertible]

/-- The ideals cutting out the zero scheme of `φ` are contained in those of `ψ` when `φ` and `ψ`
are isomorphic arrows. -/
private lemma Hom.zeroLocusIdeal_le_of_iso {M' N' : X.Modules}
    [M'.IsInvertible] [N'.IsInvertible] {φ : M ⟶ N} {ψ : M' ⟶ N'}
    (eM : M ≅ M') (eN : N ≅ N') (w : φ ≫ eN.hom = eM.hom ≫ ψ) (W : X.Opens) :
    φ.zeroLocusIdeal W ≤ ψ.zeroLocusIdeal W := by
  intro a ha
  rw [Hom.mem_zeroLocusIdeal_iff] at ha ⊢
  intro V h x hx y hy b hb
  have w' : eM.inv ≫ φ = ψ ≫ eN.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← w, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  refine ha V h _ (hx.app_hom eM.symm) _ (hy.app_hom eN.symm) b ?_
  change (eM.inv.app V.1 ≫ φ.app V.1) x = b • eN.inv.app V.1 y
  rw [← Hom.comp_app, w', Hom.comp_app]
  change eN.inv.app V.1 (ψ.app V.1 x) = _
  rw [hb, Hom.app_smul]

/-- **The zero scheme only depends on the isomorphism class of the morphism.** If
`φ : M ⟶ N` and `ψ : M' ⟶ N'` are isomorphic as arrows, then `Z(φ) = Z(ψ)`. -/
theorem Hom.zeroLocus_eq_of_arrowIso {M' N' : X.Modules}
    [M'.IsInvertible] [N'.IsInvertible] (φ : M ⟶ N) (ψ : M' ⟶ N')
    (e : Arrow.mk φ ≅ Arrow.mk ψ) : φ.zeroLocus = ψ.zeroLocus := by
  let sourceIso : M ≅ M' := Arrow.leftFunc.mapIso e
  let targetIso : N ≅ N' := Arrow.rightFunc.mapIso e
  have w : φ ≫ targetIso.hom = sourceIso.hom ≫ ψ :=
    e.hom.w.symm
  have w' : ψ ≫ targetIso.inv = sourceIso.inv ≫ φ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← w, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have := fun W ↦ le_antisymm
    (Hom.zeroLocusIdeal_le_of_iso (φ := φ) (ψ := ψ) sourceIso targetIso w W)
    (Hom.zeroLocusIdeal_le_of_iso (φ := ψ) (ψ := φ) sourceIso.symm targetIso.symm w' W)
  simp only [Hom.zeroLocus, this]

/-- The ideal defining a zero locus commutes with arbitrary base change. -/
theorem Hom.comap_zeroLocus {Y : Scheme.{u}} (g : Y ⟶ X) (φ : M ⟶ N) :
    φ.zeroLocus.comap g = ((Modules.pullback g).map φ).zeroLocus := by
  have key (y : Y) : ∃ V : Y.affineOpens, y ∈ V.1 ∧
      (φ.zeroLocus.comap g).ideal V = ((pullback g).map φ).zeroLocus.ideal V := by
    obtain ⟨U₁, hy₁, -, eM, hM⟩ := exists_isFreeGenerator M (x := g y) (W := ⊤) trivial
    obtain ⟨U, hyU, hU, eN, hN⟩ := exists_isFreeGenerator N hy₁
    obtain ⟨b, hb⟩ := hN.exists_smul_eq (φ.app U.1 (M.presheaf.map (homOfLE hU).op eM))
    obtain ⟨V, hVaff, hyV, hVU⟩ :=
      exists_isAffineOpen_mem_and_subset (U := g ⁻¹ᵁ U.1) (x := y) hyU
    obtain ⟨eM', eN', hM', hN', hb'⟩ := (hM.map hU).exists_pullback g φ hN hb.symm
    refine ⟨⟨V, hVaff⟩, hyV, ?_⟩
    rw [IdealSheafData.ideal_comap_appLE _ g U ⟨V, hVaff⟩ hVU,
      Hom.ideal_zeroLocus φ U (hM.map hU) hN hb.symm,
      Hom.ideal_zeroLocus _ ⟨V, hVaff⟩ (hM'.map hVU) (hN'.map hVU) (b := g.appLE U V hVU b),
      Ideal.map_span, Set.image_singleton]
    rw [Hom.app_presheaf_map, hb', map_smul]
    rfl
  choose V hyV hV using key
  have hcov : ⨆ y, (V y).1 = ⊤ := eq_top_iff.mpr fun y _ ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyV y⟩
  exact le_antisymm (IdealSheafData.le_of_iSup_eq_top V hcov fun y ↦ (hV y).le)
    (IdealSheafData.le_of_iSup_eq_top V hcov fun y ↦ (hV y).ge)

end AlgebraicGeometry.Scheme.Modules
