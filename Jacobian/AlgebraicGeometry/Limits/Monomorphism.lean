import Jacobian.AlgebraicGeometry.Limits.Isomorphism
import Jacobian.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Monomorphisms at finite stages of inverse systems

A monomorphism is detected by its diagonal. Isomorphism descent for finitely
presented models therefore gives eventual monomorphisms after base change
along a cofiltered inverse system with affine transition maps.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in

private theorem exists_iso_snd
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (t : i ⟶ j), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (k : I)
    [CompactSpace (D.obj k)] [QuasiSeparatedSpace (D.obj k)]
    {Z X : Scheme.{u}} [CompactSpace Z] [QuasiSeparatedSpace Z]
    (q : Z ⟶ D.obj k) [LocallyOfFinitePresentation q]
    (w : X ⟶ c.pt) [IsIso w] (h : X ⟶ Z)
    (H : IsPullback h w q (c.π.app k)) :
    ∃ (j : I) (f : j ⟶ k), IsIso (pullback.snd q (D.map f)) := by
  have H₁ : IsPullback (inv w ≫ h) (𝟙 c.pt) q (c.π.app k) := by
    exact H.of_iso (asIso w) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  have H₂ : IsPullback (c.π.app k) (𝟙 c.pt) (𝟙 (D.obj k)) (c.π.app k) :=
    IsPullback.of_vert_isIso (snd := 𝟙 _) (f := 𝟙 _) ⟨by simp⟩
  obtain ⟨j, f, hj⟩ := Scheme.exists_iso_of_isPullback_of_isLimit hc H₁ H₂
  have H₁' : IsPullback (pullback.fst q (D.map f)) (pullback.snd q (D.map f))
      q (D.map f) := IsPullback.of_hasPullback _ _
  have H₂' : IsPullback (D.map f) (𝟙 (D.obj j)) (𝟙 (D.obj k)) (D.map f) :=
    IsPullback.of_vert_isIso (snd := 𝟙 _) (f := 𝟙 _) ⟨by simp⟩
  let comparison : c.pt ⟶ pullback q (D.map f) :=
    pullback.lift (inv w ≫ h) (c.π.app j) (by
      calc
        (inv w ≫ h) ≫ q = c.π.app k := by
          simpa only [Category.id_comp] using H₁.w
        _ = c.π.app j ≫ D.map f := (c.w f).symm)
  obtain ⟨e, he, _⟩ := hj (firstLaterComparison := comparison)
    H₁' (pullback.lift_fst _ _ _) (by simp [comparison]) H₂' (c.w f) (by simp)
  refine ⟨j, f, ?_⟩
  simpa using (he ▸ (inferInstance : IsIso e.hom))

set_option backward.defeqAttrib.useBackward true in

private theorem exists_iso_overPullback
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (t : i ⟶ j), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (k : I)
    {Z Y : Over (D.obj k)}
    [CompactSpace Z.left] [QuasiSeparatedSpace Z.left]
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
    (γ : Z ⟶ Y) [LocallyOfFinitePresentation γ.left]
    (hS : IsIso ((Over.pullback (c.π.app k)).map γ).left) :
    ∃ (j : I) (a : j ⟶ k), IsIso ((Over.pullback (D.map a)).map γ).left := by
  have hw : γ.left ≫ Y.hom = Z.hom ≫ D.map (𝟙 k) := by
    rw [Over.w γ, D.map_id, Category.comp_id]
  have he : (𝟙 Y.left) ≫ Y.hom = Y.hom ≫ D.map (𝟙 k) := by
    rw [Category.id_comp, D.map_id, Category.comp_id]
  have : IsIso (D.map (𝟙 k)) := by rw [D.map_id]; infer_instance
  have hfst : IsIso (pullback.fst Y.hom (D.map (𝟙 k))) := inferInstance
  have hfl : pullback.fst Y.hom (D.map (𝟙 k)) ≫ pullback.lift (𝟙 Y.left) Y.hom he = 𝟙 _ := by
    apply pullback.hom_ext
    · simp
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.condition, D.map_id,
        Category.comp_id]
  have he₀ : IsIso (pullback.lift (𝟙 Y.left) Y.hom he) := by
    rw [show pullback.lift (𝟙 Y.left) Y.hom he = inv (pullback.fst Y.hom (D.map (𝟙 k))) from
      IsIso.eq_inv_of_hom_inv_id hfl]
    infer_instance
  have hq₀ : pullback.lift γ.left Z.hom hw = γ.left ≫ pullback.lift (𝟙 Y.left) Y.hom he := by
    apply pullback.hom_ext <;> simp
  have : LocallyOfFinitePresentation (pullback.lift γ.left Z.hom hw) := by
    rw [hq₀]; infer_instance
  -- The base change of `γ` to the limit is the base change of the identity-stage model.
  have hsq : IsPullback (pullback.fst Z.hom (c.π.app k))
      ((Over.pullback (c.π.app k)).map γ).left (pullback.lift γ.left Z.hom hw)
      ((baseChangeCone D c Y.hom).π.app (Over.mk (𝟙 k))) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_baseChangeCone_π D c Y.hom (Over.mk (𝟙 k)))
    · refine (IsPullback.of_hasPullback Z.hom (c.π.app k)).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by simp [Over.pullback])
        (by simp) (by simp)
    · apply pullback.hom_ext <;>
        simp [Over.pullback,
          pullback.condition]
  have hI1 : @LocallyOfFinitePresentation Z.left
      ((baseChangeDiagram D Y.hom).obj (Over.mk (𝟙 k))) (pullback.lift γ.left Z.hom hw) :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.lift γ.left Z.hom hw))
  have hI4 : @IsIso Scheme.{u} _ (pullback Z.hom (c.π.app k)) (baseChangeCone D c Y.hom).pt
      ((Over.pullback (c.π.app k)).map γ).left := hS
  obtain ⟨j, a, ha⟩ := exists_iso_snd (baseChangeDiagram D Y.hom)
    (baseChangeCone D c Y.hom) (isLimitBaseChangeCone D c Y.hom hc)
    (Over.mk (𝟙 k)) (pullback.lift γ.left Z.hom hw)
    ((Over.pullback (c.π.app k)).map γ).left (pullback.fst Z.hom (c.π.app k)) hsq
  refine ⟨j.left, j.hom, ?_⟩
  have hργ : IsPullback (pullback.fst Z.hom (D.map j.hom))
      ((Over.pullback (D.map j.hom)).map γ).left γ.left
      (pullback.fst Y.hom (D.map j.hom)) := by
    refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback Y.hom (D.map j.hom))
    · refine (IsPullback.of_hasPullback Z.hom (D.map j.hom)).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by simp [Over.pullback]) (by simp) (by simp)
    · simp [Over.pullback]
  have hsq3 : IsPullback (𝟙 Z.left) (pullback.lift γ.left Z.hom hw) γ.left
      (pullback.fst Y.hom (D.map (𝟙 k))) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, pullback.lift_fst]⟩
  have hρq : IsPullback
      (pullback.fst (pullback.lift γ.left Z.hom hw) ((baseChangeDiagram D Y.hom).map a))
      (pullback.snd (pullback.lift γ.left Z.hom hw) ((baseChangeDiagram D Y.hom).map a))
      γ.left (pullback.fst Y.hom (D.map j.hom)) := by
    have h1 := (IsPullback.of_hasPullback (pullback.lift γ.left Z.hom hw)
        ((baseChangeDiagram D Y.hom).map a)).paste_horiz hsq3
    refine h1.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) ?_
    simp
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme.{u})
    (Arrow.isoMk (hρq.isoIsPullback _ _ hργ) (Iso.refl _) (by simp))).mp ha

set_option backward.defeqAttrib.useBackward true in

private theorem exists_mono_snd
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (t : i ⟶ j), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (k : I)
    [CompactSpace (D.obj k)] [QuasiSeparatedSpace (D.obj k)]
    {Y X : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (p : Y ⟶ D.obj k) [LocallyOfFiniteType p]
    (g : X ⟶ c.pt) [Mono g] (h : X ⟶ Y)
    (H : IsPullback h g p (c.π.app k)) :
    ∃ (j : I) (a : j ⟶ k), Mono (pullback.snd p (D.map a)) := by
  have : QuasiCompact p := inferInstance
  have : QuasiSeparated p := inferInstance
  have : CompactSpace ↥(pullback p p) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p p)
  have : QuasiSeparatedSpace ↥(pullback p p) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p p)
  let γ : Over.mk p ⟶ Over.mk (pullback.snd p p ≫ p) :=
    Over.homMk (pullback.diagonal p) (by simp)
  have : LocallyOfFinitePresentation (pullback.diagonal p ≫ pullback.fst p p) := by
    rw [pullback.diagonal_fst]
    infer_instance
  have : LocallyOfFinitePresentation γ.left :=
    .of_comp (pullback.diagonal p) (pullback.fst p p)
  have hmono : Mono (pullback.fst (c.π.app k) p) := by
    refine (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.monomorphisms Scheme.{u})
      (Arrow.isoMk (H.isoPullback ≪≫ pullbackSymmetry p (c.π.app k)) (Iso.refl _) ?_)).mp
      ‹Mono g›
    simp
  have : Mono (pullback.fst (c.π.app k) p) := hmono
  have hlim : IsIso (pullback.diagonal (pullback.fst (c.π.app k) p)) := inferInstance
  rw [diagonal_pullback_fst] at hlim
  have hS : IsIso ((Over.pullback (c.π.app k)).map γ).left :=
    (MorphismProperty.cancel_right_of_respectsIso (MorphismProperty.isomorphisms Scheme.{u})
      _ _).mp ((MorphismProperty.cancel_left_of_respectsIso
        (MorphismProperty.isomorphisms Scheme.{u}) _ _).mp hlim)
  have : CompactSpace ↥((Over.mk p : Over (D.obj k)).left) := ‹CompactSpace Y›
  have : QuasiSeparatedSpace ↥((Over.mk p : Over (D.obj k)).left) :=
    ‹QuasiSeparatedSpace Y›
  have : CompactSpace ↥((Over.mk (pullback.snd p p ≫ p) : Over (D.obj k)).left) :=
    ‹CompactSpace ↥(pullback p p)›
  have : QuasiSeparatedSpace
      ↥((Over.mk (pullback.snd p p ≫ p) : Over (D.obj k)).left) :=
    ‹QuasiSeparatedSpace ↥(pullback p p)›
  obtain ⟨j, a, ha⟩ := exists_iso_overPullback D c hc k γ hS
  have hdiag : IsIso (pullback.diagonal (pullback.fst (D.map a) p)) := by
    rw [diagonal_pullback_fst]
    exact (MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme.{u})
      _ _).mpr ((MorphismProperty.cancel_right_of_respectsIso
        (MorphismProperty.isomorphisms Scheme.{u}) _ _).mpr ha)
  refine ⟨j, a, ?_⟩
  have : Mono (pullback.fst (D.map a) p) := (pullback.isIso_diagonal_iff _).mp hdiag
  change (MorphismProperty.monomorphisms Scheme.{u}) (pullback.snd p (D.map a))
  rw [← MorphismProperty.cancel_left_of_respectsIso
    (MorphismProperty.monomorphisms Scheme.{u})
    (pullbackSymmetry (D.map a) p).hom, pullbackSymmetry_hom_comp_snd]
  infer_instance

set_option backward.defeqAttrib.useBackward true in

private theorem exists_mono_overPullback
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (t : i ⟶ j), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (k : I)
    {Z Y : Over (D.obj k)}
    [CompactSpace Z.left] [QuasiSeparatedSpace Z.left]
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
    (γ : Z ⟶ Y) [LocallyOfFiniteType γ.left]
    (hS : Mono ((Over.pullback (c.π.app k)).map γ).left) :
    ∃ (j : I) (a : j ⟶ k), Mono ((Over.pullback (D.map a)).map γ).left := by
  have hw : γ.left ≫ Y.hom = Z.hom ≫ D.map (𝟙 k) := by
    rw [Over.w γ, D.map_id, Category.comp_id]
  have he : (𝟙 Y.left) ≫ Y.hom = Y.hom ≫ D.map (𝟙 k) := by
    rw [Category.id_comp, D.map_id, Category.comp_id]
  have : IsIso (D.map (𝟙 k)) := by rw [D.map_id]; infer_instance
  have hfst : IsIso (pullback.fst Y.hom (D.map (𝟙 k))) := inferInstance
  have hfl : pullback.fst Y.hom (D.map (𝟙 k)) ≫ pullback.lift (𝟙 Y.left) Y.hom he = 𝟙 _ := by
    apply pullback.hom_ext
    · simp
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.condition, D.map_id,
        Category.comp_id]
  have he₀ : IsIso (pullback.lift (𝟙 Y.left) Y.hom he) := by
    rw [show pullback.lift (𝟙 Y.left) Y.hom he = inv (pullback.fst Y.hom (D.map (𝟙 k))) from
      IsIso.eq_inv_of_hom_inv_id hfl]
    infer_instance
  have hq₀ : pullback.lift γ.left Z.hom hw = γ.left ≫ pullback.lift (𝟙 Y.left) Y.hom he := by
    apply pullback.hom_ext <;> simp
  have : LocallyOfFiniteType (pullback.lift γ.left Z.hom hw) := by
    rw [hq₀]; infer_instance
  -- The base change of `γ` to the limit is the base change of the identity-stage model.
  have hsq : IsPullback (pullback.fst Z.hom (c.π.app k))
      ((Over.pullback (c.π.app k)).map γ).left (pullback.lift γ.left Z.hom hw)
      ((baseChangeCone D c Y.hom).π.app (Over.mk (𝟙 k))) := by
    refine IsPullback.of_bot ?_ ?_ (isPullback_baseChangeCone_π D c Y.hom (Over.mk (𝟙 k)))
    · refine (IsPullback.of_hasPullback Z.hom (c.π.app k)).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by simp [Over.pullback])
        (by simp) (by simp)
    · apply pullback.hom_ext <;>
        simp [Over.pullback,
          pullback.condition]
  have hI1 : @LocallyOfFiniteType Z.left
      ((baseChangeDiagram D Y.hom).obj (Over.mk (𝟙 k))) (pullback.lift γ.left Z.hom hw) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.lift γ.left Z.hom hw))
  have hI4 : @Mono Scheme.{u} _ (pullback Z.hom (c.π.app k)) (baseChangeCone D c Y.hom).pt
      ((Over.pullback (c.π.app k)).map γ).left := hS
  obtain ⟨j, a, ha⟩ := exists_mono_snd (baseChangeDiagram D Y.hom)
    (baseChangeCone D c Y.hom) (isLimitBaseChangeCone D c Y.hom hc)
    (Over.mk (𝟙 k)) (pullback.lift γ.left Z.hom hw)
    ((Over.pullback (c.π.app k)).map γ).left (pullback.fst Z.hom (c.π.app k)) hsq
  refine ⟨j.left, j.hom, ?_⟩
  have hργ : IsPullback (pullback.fst Z.hom (D.map j.hom))
      ((Over.pullback (D.map j.hom)).map γ).left γ.left
      (pullback.fst Y.hom (D.map j.hom)) := by
    refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback Y.hom (D.map j.hom))
    · refine (IsPullback.of_hasPullback Z.hom (D.map j.hom)).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by simp [Over.pullback]) (by simp) (by simp)
    · simp [Over.pullback]
  have hsq3 : IsPullback (𝟙 Z.left) (pullback.lift γ.left Z.hom hw) γ.left
      (pullback.fst Y.hom (D.map (𝟙 k))) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, pullback.lift_fst]⟩
  have hρq : IsPullback
      (pullback.fst (pullback.lift γ.left Z.hom hw) ((baseChangeDiagram D Y.hom).map a))
      (pullback.snd (pullback.lift γ.left Z.hom hw) ((baseChangeDiagram D Y.hom).map a))
      γ.left (pullback.fst Y.hom (D.map j.hom)) := by
    have h1 := (IsPullback.of_hasPullback (pullback.lift γ.left Z.hom hw)
        ((baseChangeDiagram D Y.hom).map a)).paste_horiz hsq3
    refine h1.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) ?_
    simp
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.monomorphisms Scheme.{u})
    (Arrow.isoMk (hρq.isoIsPullback _ _ hργ) (Iso.refl _) (by simp))).mp ha


/-- A morphism of finite type between quasi-compact quasi-separated stage schemes
that is monic at a cofiltered affine-transition limit is monic at some later stage. -/
theorem Scheme.exists_mono_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    (hmono : Mono ((Over.pullback (c.π.app (op i₀))).map f₀).left) :
    ∃ (i : I) (hi : i₀ ≤ i),
      Mono ((Over.pullback (D.map (homOfLE hi).op)).map f₀).left := by
  have : Nonempty I := ⟨i₀⟩
  obtain ⟨j, a, ha⟩ := exists_mono_overPullback D c hc (op i₀) f₀ hmono
  refine ⟨j.unop, leOfHom a.unop, ?_⟩
  exact ha

end AlgebraicGeometry
