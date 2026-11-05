import Jacobian.AlgebraicGeometry.IdealSheaf.Affine

/-!
# Gluing ideal sheaves on affine open covers

Compatible ideal sheaves on affine opens glue to an ideal sheaf. Equality can
be checked on affine opens lying over an affine cover of a target scheme.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- Two ideal sheaves on `Z` coincide as soon as their restrictions to every affine open of `Z`
mapping into an affine open of `Y` along `f : Z ⟶ Y` coincide. -/
theorem eq_of_comap_ι_eq {Z : Scheme.{u}} (f : Z ⟶ Y) {A B : Z.IdealSheafData}
    (H : ∀ (U : Y.affineOpens) (W : Z.affineOpens), W.1 ≤ f ⁻¹ᵁ U.1 →
      A.comap W.1.ι = B.comap W.1.ι) : A = B := by
  refine ext_of_iSup_eq_top (ι := {p : Y.affineOpens × Z.affineOpens // p.2.1 ≤ f ⁻¹ᵁ p.1.1})
    (fun p ↦ p.1.2) ?_ fun p ↦ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (a := x) hxV (f ⁻¹ᵁ V).2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(⟨V, hV⟩, ⟨W, hW⟩), hWV⟩, hxW⟩
  · obtain ⟨⟨U, W⟩, h⟩ := p
    rw [← map_topIso_ideal_top_comap_ι A W, ← map_topIso_ideal_top_comap_ι B W, H U W h]

/-- **Gluing ideal sheaves.** A family of ideal sheaves `K U` on the affine opens `U` of `X`
which is compatible with restriction to basic opens is the family of restrictions of a single
ideal sheaf on `X`. -/
theorem exists_comap_ι_eq (K : ∀ U : X.affineOpens, U.1.toScheme.IdealSheafData)
    (hK : ∀ (U : X.affineOpens) (f : Γ(X, U)),
      (K U).comap (X.homOfLE (X.basicOpen_le f)) = K (X.affineBasicOpen f)) :
    ∃ J : X.IdealSheafData, ∀ U, J.comap U.1.ι = K U := by
  have (U : X.affineOpens) : IsAffine U.1.toScheme := U.2
  have key (U V : X.affineOpens) (h : V.1 ≤ U.1) :
      (((K U).comap (X.homOfLE h)).ideal ⟨⊤, isAffineOpen_top _⟩).map V.1.topIso.hom.hom =
        (((K U).ideal ⟨⊤, isAffineOpen_top _⟩).map U.1.topIso.hom.hom).map
          (X.presheaf.map (homOfLE h).op).hom := by
    rw [ideal_comap_appLE _ _ ⟨⊤, isAffineOpen_top _⟩ ⟨⊤, isAffineOpen_top _⟩
      (X.homOfLE h).preimage_top.ge, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp]
    congr 2
    simp only [Scheme.Opens.topIso_hom]
    rw [Scheme.homOfLE_appLE]
    exact (X.presheaf.map_comp _ _).symm.trans
      ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _))
  let J : X.IdealSheafData :=
    { ideal U := ((K U).ideal ⟨⊤, isAffineOpen_top _⟩).map U.1.topIso.hom.hom
      map_ideal_basicOpen U f := by
        have := key U (X.affineBasicOpen f) (X.basicOpen_le f)
        have e : (K U).comap (X.homOfLE (show (X.affineBasicOpen f).1 ≤ U.1 from
          X.basicOpen_le f)) = K (X.affineBasicOpen f) := hK U f
        rw [e] at this
        exact this.symm }
  refine ⟨J, fun U ↦ ext_of_isAffine ?_⟩
  have h : ((J.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩).map U.1.topIso.hom.hom =
      ((K U).ideal ⟨⊤, isAffineOpen_top _⟩).map U.1.topIso.hom.hom :=
    map_topIso_ideal_top_comap_ι J U
  have := congrArg (Ideal.map U.1.topIso.inv.hom) h
  rwa [Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
    Ideal.map_id, Ideal.map_id] at this

/-- The pullback of `K` along `h` is contained in the kernel of `a` if and only if `K` is
contained in the kernel of `a ≫ h`. -/
lemma comap_le_ker_iff {W : Scheme.{u}} (K : Y.IdealSheafData) (h : X ⟶ Y) (a : W ⟶ X) :
    K.comap h ≤ a.ker ↔ K ≤ (a ≫ h).ker := by
  rw [← map_bot a, ← map_bot (a ≫ h), le_map_iff_comap_le, le_map_iff_comap_le, comap_comp]

/-- An ideal sheaf on an affine scheme is determined by the morphisms from affine schemes whose
kernel contains it: test with the inclusions of the closed subschemes. -/
lemma eq_of_forall_le_ker_iff [IsAffine X] {K₁ K₂ : X.IdealSheafData}
    (H : ∀ (W : Scheme.{u}) [IsAffine W] (a : W ⟶ X), K₁ ≤ a.ker ↔ K₂ ≤ a.ker) : K₁ = K₂ := by
  have (K : X.IdealSheafData) : IsAffine K.subscheme := isAffine_of_isAffineHom K.subschemeι
  refine le_antisymm ?_ ?_
  · simpa only [ker_subschemeι] using (H _ K₂.subschemeι).2 (ker_subschemeι K₂).ge
  · simpa only [ker_subschemeι] using (H _ K₁.subschemeι).1 (ker_subschemeι K₁).ge

/-- An inclusion of ideal sheaves can be checked after pullback along a family of open
immersions jointly covering the scheme. -/
lemma le_of_forall_comap_le {ι : Type*} {Z : ι → Scheme.{u}} (j : ∀ i, Z i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hj : ⨆ i, (j i).opensRange = ⊤) {A B : X.IdealSheafData}
    (H : ∀ i, A.comap (j i) ≤ B.comap (j i)) : A ≤ B := by
  refine le_of_iSup_eq_top (ι := Σ i, (Z i).affineOpens)
    (fun p ↦ ⟨j p.1 ''ᵁ p.2.1, p.2.2.image_of_isOpenImmersion _⟩) ?_ fun p ↦ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, z, rfl⟩ := TopologicalSpace.Opens.mem_iSup.mp (hj.ge (Set.mem_univ x))
    obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ :=
      (Z i).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, ⟨W, hW⟩⟩, ⟨z, hzW, rfl⟩⟩
  · have h := H p.1 p.2
    rw [ideal_comap_of_isOpenImmersion, ideal_comap_of_isOpenImmersion] at h
    exact (Ideal.comap_le_comap_iff_of_surjective _
      (j p.1 |>.appIso p.2.1).commRingCatIsoToRingEquiv.symm.surjective _ _).mp h

end AlgebraicGeometry.Scheme.IdealSheafData
