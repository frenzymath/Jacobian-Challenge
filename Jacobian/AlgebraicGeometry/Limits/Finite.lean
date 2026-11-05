import Jacobian.AlgebraicGeometry.Limits.Affine
import Jacobian.AlgebraicGeometry.Pullback.AffineCoordinates
import Jacobian.RingTheory.FiniteType.FilteredColimits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Finite morphisms at a finite stage

A finite type morphism of quasi-compact quasi-separated stage schemes that
becomes finite over an affine-transition inverse limit becomes finite at
a finite stage. The proof descends affineness, then finitely many integral
generators on an affine cover of the target.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem exists_isFinite_morphismRestrict_baseChange_affine_base_piece
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ k : I) (hk : i₀ ≤ k)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [LocallyOfFiniteType f₀.left]
    (haffine : IsAffineHom (((Over.pullback (D.map (homOfLE hk).op)).map f₀).left))
    (V : Y₀.left.Opens) (hV : IsAffineOpen V)
    (W : (D.obj (op i₀)).Opens) (hW : IsAffineOpen W)
    (hVW : V ≤ Y₀.hom ⁻¹ᵁ W)
    (hfinite : IsFinite
      ((((Over.pullback (c.π.app (op i₀))).map f₀).left) ∣_
        ((pullback.fst Y₀.hom (c.π.app (op i₀))) ⁻¹ᵁ V))) :
    ∃ (j : I) (hkj : k ≤ j),
      IsFinite
        ((((Over.pullback (D.map (homOfLE (hk.trans hkj)).op)).map f₀).left)
          ∣_ ((pullback.fst Y₀.hom (D.map (homOfLE (hk.trans hkj)).op)) ⁻¹ᵁ V)) := by
  classical
  have : IsDirected {i : I // k ≤ i} (· ≤ ·) := ⟨fun i j ↦ by
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨l, i.property.trans hil⟩, hil, hjl⟩⟩
  obtain ⟨F, B, C, aB, aC, H⟩ :=
    exists_affine_base_piece_tensor_presentation D c hc i₀ k hk X₀ Y₀ f₀
      haffine V hV W hW hVW
  let : Algebra (F.obj ⟨k, le_rfl⟩) B := aB.toAlgebra
  let : Algebra (F.obj ⟨k, le_rfl⟩) C := aC.toAlgebra
  obtain ⟨φ, hft, ⟨elim⟩, estage⟩ := H
  let : Algebra (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u}) :=
    (CommRingCat.Hom.hom (colimit.ι F ⟨k, le_rfl⟩)).toAlgebra
  have hlim : (Algebra.TensorProduct.map
      (AlgHom.id (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u})) φ).Finite := by
    exact (IsFinite.SpecMap_iff (CommRingCat.ofHom
      (Algebra.TensorProduct.map
        (AlgHom.id (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u})) φ).toRingHom)).mp
      ((MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) elim).mp hfinite)
  obtain ⟨j, hj, hjfin⟩ :=
    RingHom.exists_finite_tensorProductMap_of_colimit F ⟨k, le_rfl⟩ B C φ hft hlim
  let : Algebra (F.obj ⟨k, le_rfl⟩) (F.obj j) :=
    (CommRingCat.Hom.hom (F.map (homOfLE hj))).toAlgebra
  obtain ⟨e⟩ := estage j
  refine ⟨j.val, j.property, ?_⟩
  apply (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) e).mpr
  exact (IsFinite.SpecMap_iff (CommRingCat.ofHom
    (Algebra.TensorProduct.map (AlgHom.id (F.obj ⟨k, le_rfl⟩) (F.obj j)) φ).toRingHom)).mpr
    hjfin

end AlgebraicGeometry
end

section
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem over_pullback_square {S T : Scheme.{u}}
    (X Y : Over S) (f : X ⟶ Y) (a : T ⟶ S) :
    IsPullback (pullback.fst X.hom a) (((Over.pullback a).map f).left)
      f.left (pullback.fst Y.hom a) := by
  have HX : IsPullback (pullback.fst X.hom a) (pullback.snd X.hom a)
      (f.left ≫ Y.hom) a := by
    simpa only [Over.w f] using IsPullback.of_hasPullback X.hom a
  have HY := IsPullback.of_hasPullback Y.hom a
  have H := IsPullback.of_bot' HX HY
  have he : (((Over.pullback a).map f).left) =
      HY.lift (pullback.fst X.hom a ≫ f.left) (pullback.snd X.hom a) (by
        simp [pullback.condition]) := by
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, pullback.lift_fst, HY.lift_fst]
    · simp only [Over.pullback_map_left, pullback.lift_snd, HY.lift_snd]
  rw [he]
  exact H
private theorem finite_restrict_baseChange_comp
    {S T R : Scheme.{u}} (X Y : Over S) (f : X ⟶ Y)
    (a : T ⟶ S) (b : R ⟶ T) (V : Y.left.Opens)
    (hf : IsFinite ((((Over.pullback a).map f).left) ∣_
      ((pullback.fst Y.hom a) ⁻¹ᵁ V))) :
    IsFinite ((((Over.pullback (b ≫ a)).map f).left) ∣_
      ((pullback.fst Y.hom (b ≫ a)) ⁻¹ᵁ V)) := by
  let x : pullback X.hom (b ≫ a) ⟶ pullback X.hom a :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ b) (by
      simp only [Category.assoc, pullback.condition])
  let y : pullback Y.hom (b ≫ a) ⟶ pullback Y.hom a :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ b) (by
      simp only [Category.assoc, pullback.condition])
  let fa := ((Over.pullback a).map f).left
  let fq := ((Over.pullback (b ≫ a)).map f).left
  have hcomm : x ≫ fa = fq ≫ y := by
    apply pullback.hom_ext <;> simp [x, y, fa, fq, Over.pullback_map_left]
  have hs : IsPullback x fq fa y := by
    apply IsPullback.of_right (t := over_pullback_square X Y f a)
    · simpa [x, y, fq] using over_pullback_square X Y f (b ≫ a)
    · exact hcomm
  have hpre : y ⁻¹ᵁ ((pullback.fst Y.hom a) ⁻¹ᵁ V) =
      (pullback.fst Y.hom (b ≫ a)) ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage]
    simp [y]
  have hsource : x ⁻¹ᵁ fa ⁻¹ᵁ ((pullback.fst Y.hom a) ⁻¹ᵁ V) =
      fq ⁻¹ᵁ (pullback.fst Y.hom (b ≫ a)) ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, hcomm, Scheme.Hom.comp_preimage, hpre]
  have hr := Scheme.Hom.isPullback_resLE hs
    (US := (pullback.fst Y.hom a) ⁻¹ᵁ V)
    (UT := (pullback.fst Y.hom (b ≫ a)) ⁻¹ᵁ V)
    (UX := fa ⁻¹ᵁ (pullback.fst Y.hom a) ⁻¹ᵁ V)
    (UY := fq ⁻¹ᵁ (pullback.fst Y.hom (b ≫ a)) ⁻¹ᵁ V)
    hpre.ge le_rfl (by rw [hsource, inf_of_le_left (Scheme.Hom.preimage_mono _ le_rfl)])
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at hr
  exact MorphismProperty.of_isPullback (P := @IsFinite) hr hf

private theorem isFinite_morphismRestrict_of_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    {B : Type*} (U : B → Y.Opens) (hle : ∀ b, U b ≤ V)
    (hcover : V ≤ ⨆ b, U b) (hfin : ∀ b, IsFinite (f ∣_ U b)) :
    IsFinite (f ∣_ V) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite)
    (fun b ↦ V.ι ⁻¹ᵁ U b)
  · apply top_unique
    intro x hx
    have hx' := hcover x.property
    simpa only [Scheme.Hom.preimage_iSup, Scheme.Hom.mem_preimage,
      TopologicalSpace.Opens.mem_iSup, Scheme.Opens.ι_apply] using hx'
  · intro b
    apply (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
      (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U b))).mpr
    have he : V.ι ''ᵁ (V.ι ⁻¹ᵁ U b) = U b := by
      simp [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr (hle b)]
    rw [he]
    exact hfin b

private theorem exists_isFinite_morphismRestrict_baseChange_affine_open
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ k : I) (hk : i₀ ≤ k)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [LocallyOfFiniteType f₀.left]
    (haffine : IsAffineHom (((Over.pullback (D.map (homOfLE hk).op)).map f₀).left))
    (V : Y₀.left.Opens) (hV : IsAffineOpen V)
    (hfinite : IsFinite
      ((((Over.pullback (c.π.app (op i₀))).map f₀).left) ∣_
        ((pullback.fst Y₀.hom (c.π.app (op i₀))) ⁻¹ᵁ V))) :
    ∃ (j : I) (hkj : k ≤ j), ∀ (i : I) (hji : j ≤ i),
      IsFinite
        ((((Over.pullback (D.map (homOfLE (hk.trans (hkj.trans hji))).op)).map f₀).left)
          ∣_ ((pullback.fst Y₀.hom
            (D.map (homOfLE (hk.trans (hkj.trans hji))).op)) ⁻¹ᵁ V)) := by
  classical
  have hnbhd (x : V) : ∃ (U : Y₀.left.Opens), IsAffineOpen U ∧ x.val ∈ U ∧
      U ≤ V ∧ ∃ W : (D.obj (op i₀)).Opens, IsAffineOpen W ∧ U ≤ Y₀.hom ⁻¹ᵁ W := by
    obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := D.obj (op i₀)) (x := Y₀.hom x.val) (U := ⊤) (by trivial)
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (U := V ⊓ Y₀.hom ⁻¹ᵁ W) ⟨x.property, hxW⟩
    exact ⟨U, hU, hxU, le_trans hUV inf_le_left, W, hW, le_trans hUV inf_le_right⟩
  choose U hU hxU hUV W hW hUW using hnbhd
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x ↦ (U x : Set Y₀.left))
    (fun x ↦ (U x).isOpen) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  have hlocal (b : t) :=
    exists_isFinite_morphismRestrict_baseChange_affine_base_piece D c hc i₀ k hk
      X₀ Y₀ f₀ haffine (U b.val) (hU b.val) (W b.val) (hW b.val) (hUW b.val)
      (by
        let p := pullback.fst Y₀.hom (c.π.app (op i₀))
        have H := IsZariskiLocalAtTarget.restrict (P := @IsFinite) hfinite
          ((p ⁻¹ᵁ V).ι ⁻¹ᵁ (p ⁻¹ᵁ U b.val))
        have he : (p ⁻¹ᵁ V).ι ''ᵁ ((p ⁻¹ᵁ V).ι ⁻¹ᵁ (p ⁻¹ᵁ U b.val)) =
            p ⁻¹ᵁ U b.val := by
          rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
          exact inf_eq_right.mpr (p.preimage_mono (hUV b.val))
        have H' := (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
          (morphismRestrictRestrict _ _ _)).mp H
        rw [he] at H'
        exact H')
  choose j hj hfin using hlocal
  have : Nonempty I := ⟨k⟩
  obtain ⟨l, hl⟩ := (Set.finite_range j).bddAbove
  obtain ⟨l', hkl', hll'⟩ := exists_ge_ge k l
  refine ⟨l', hkl', ?_⟩
  intro i hli
  apply isFinite_morphismRestrict_of_cover _ _
    (fun b : t ↦ (pullback.fst Y₀.hom
      (D.map (homOfLE (hk.trans (hkl'.trans hli))).op)) ⁻¹ᵁ U b.val)
  · intro b
    exact Scheme.Hom.preimage_mono _ (hUV b.val)
  · intro x hx
    obtain ⟨b, hxb⟩ := Set.mem_iUnion.mp (ht hx)
    obtain ⟨hb, hxb⟩ := Set.mem_iUnion.mp hxb
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨b, hb⟩, hxb⟩
  · intro b
    have hji := ((hl (Set.mem_range_self b)).trans hll').trans hli
    have H := finite_restrict_baseChange_comp X₀ Y₀ f₀
      (D.map (homOfLE (hk.trans (hj b))).op) (D.map (homOfLE hji).op)
      (U b.val) (hfin b)
    have he : D.map (homOfLE hji).op ≫ D.map (homOfLE (hk.trans (hj b))).op =
        D.map (homOfLE (hk.trans (hkl'.trans hli))).op := by
      rw [← D.map_comp]
      congr 1
    rw [he] at H
    exact H

end AlgebraicGeometry
end

section
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem isAffineHom_over_pullback_iff
    {S T : Scheme.{u}} (X Y : Over S) (f : X ⟶ Y) (q : T ⟶ S) :
    IsAffineHom
      (pullback.map (f.left ≫ Y.hom) q Y.hom q f.left (𝟙 T) (𝟙 S)
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) ↔
      IsAffineHom (((Over.pullback q).map f).left) := by
  let e := pullback.congrHom (Over.w f) (rfl : q = q)
  have he : pullback.map (f.left ≫ Y.hom) q Y.hom q f.left (𝟙 T) (𝟙 S)
      (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) =
      e.hom ≫ ((Over.pullback q).map f).left := by
    apply pullback.hom_ext <;>
      simp [e, Over.pullback_map_left, pullback.congrHom_hom, pullback.map]
  rw [he]
  exact MorphismProperty.cancel_left_of_respectsIso @IsAffineHom e.hom _

/-- A finite type stage morphism finite over the limit becomes finite at a later stage. -/
theorem Scheme.exists_isFinite_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    (hfinite : IsFinite (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsFinite (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left) := by
  classical
  have hf : IsAffineHom (((Over.pullback (c.π.app (op i₀))).map f₀).left) :=
    hfinite.toIsAffineHom
  have hlim := (isAffineHom_over_pullback_iff X₀ Y₀ f₀ (c.π.app (op i₀))).mpr hf
  obtain ⟨k, hk, haffine⟩ :=
    Scheme.exists_isAffineHom_baseChange_of_isLimit D c hc i₀ f₀.left Y₀.hom hlim
  have hak :=
    (isAffineHom_over_pullback_iff X₀ Y₀ f₀ (D.map (homOfLE hk).op)).mp haffine
  let 𝒰 := Y₀.left.affineCover.finiteSubcover
  have hlocal (b : 𝒰.I₀) :=
    exists_isFinite_morphismRestrict_baseChange_affine_open D c hc i₀ k hk X₀ Y₀ f₀
      hak (𝒰.f b).opensRange (isAffineOpen_opensRange (𝒰.f b))
      (IsZariskiLocalAtTarget.restrict (P := @IsFinite) hfinite _)
  choose j hj hfin using hlocal
  have : Nonempty I := ⟨k⟩
  obtain ⟨i, hi⟩ := (Set.finite_range j).bddAbove
  obtain ⟨i', hki', hii'⟩ := exists_ge_ge k i
  refine ⟨i', hk.trans hki', ?_⟩
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite)
    (fun b : 𝒰.I₀ ↦ (pullback.fst Y₀.hom
      (D.map (homOfLE (hk.trans hki')).op)) ⁻¹ᵁ (𝒰.f b).opensRange)
  · simp only [← Scheme.Hom.preimage_iSup, 𝒰.iSup_opensRange,
      Scheme.Hom.preimage_top]
  · intro b
    exact hfin b i' ((hi (Set.mem_range_self b)).trans hii')

end AlgebraicGeometry
end
