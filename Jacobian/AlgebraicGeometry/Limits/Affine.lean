import Jacobian.AlgebraicGeometry.Limits.BaseChange
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Affineness at a finite stage

For inverse systems of quasi-compact quasi-separated schemes with affine
transition maps, affineness of a morphism to a fixed target and affineness
of a base-changed stage morphism descend to a finite stage.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- An affine map to a fixed qcqs target is affine at every sufficiently late stage. -/
theorem Scheme.eventually_isAffineHom_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (h : D ⟶ (Functor.const Iᵒᵖ).obj T)
    (c : Cone D) (_hc : IsLimit c) (f : c.pt ⟶ T)
    (_hf : ∀ i : Iᵒᵖ, c.π.app i ≫ h.app i = f) [IsAffineHom f] :
    ∃ i : I, ∀ j : I, i ≤ j → IsAffineHom (h.app (op j)) := by
  classical
  let b : Iᵒᵖ := op (Classical.choice inferInstance)
  let 𝒰 := T.affineCover.finiteSubcover
  have (a : 𝒰.I₀) : IsAffine (𝒰.X a) := inferInstanceAs (IsAffine (Spec _))
  let V (a : 𝒰.I₀) : T.affineOpens := ⟨(𝒰.f a).opensRange,
    isAffineOpen_opensRange (𝒰.f a)⟩
  have H (a : 𝒰.I₀) : ∃ k : Over b, IsAffineOpen (h.app k.left ⁻¹ᵁ (V a).1) := by
    let U := h.app b ⁻¹ᵁ (V a).1
    have : QuasiCompact (h.app b) := by
      change QuasiCompact (show D.obj b ⟶ T from h.app b)
      infer_instance
    have hU : IsCompact (U : Set (D.obj b)) :=
      QuasiCompact.isCompact_preimage (f := h.app b) _ (V a).1.isOpen (V a).2.isCompact
    have (k : Over b) : CompactSpace ((opensDiagram D b U).obj k) :=
      isCompact_iff_compactSpace.mp
        (QuasiCompact.isCompact_preimage (f := D.map k.hom) _ U.isOpen hU)
    have (k : Over b) : QuasiSeparatedSpace ((opensDiagram D b U).obj k) :=
      (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map k.hom ⁻¹ᵁ U).isOpen).mp
        (.of_quasiSeparatedSpace _)
    have : IsAffine (opensCone D c b U).pt := by
      change IsAffineOpen (c.π.app b ⁻¹ᵁ U)
      simpa [U, ← Scheme.Hom.comp_preimage, _hf b] using (V a).2.preimage f
    obtain ⟨k, hk⟩ := Scheme.exists_isAffine_of_isLimit
      (opensDiagram D b U) (opensCone D c b U) (isLimitOpensCone D c _hc b U)
    refine ⟨k, ?_⟩
    change IsAffineOpen (D.map k.hom ⁻¹ᵁ U) at hk
    simpa [U, ← Scheme.Hom.comp_preimage, h.naturality k.hom] using hk
  choose k hk using H
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image (fun a ↦ (k a).left))
  have gi (a : 𝒰.I₀) : i ⟶ (k a).left := (hi (by simp)).some
  refine ⟨i.unop, fun j hij ↦ ?_⟩
  let g : op j ⟶ i := (homOfLE hij).op
  apply HasAffineProperty.of_iSup_eq_top (P := @IsAffineHom) V 𝒰.iSup_opensRange
  intro a
  change IsAffineOpen (h.app (op j) ⁻¹ᵁ (V a).1)
  have ha := (hk a).preimage (D.map (g ≫ gi a))
  simpa [← Scheme.Hom.comp_preimage, h.naturality (g ≫ gi a)] using ha

end AlgebraicGeometry
end

section
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private def upperTailEquivalence {I : Type u} [Preorder I] (i₀ : I) :
    (Set.Ici i₀)ᵒᵖ ≌ Over (op i₀) where
  functor :=
    { obj := fun i ↦ Over.mk (homOfLE i.unop.property).op
      map := fun f ↦ Over.homMk (homOfLE (leOfHom f.unop)).op
      map_id := by intros; ext; apply Subsingleton.elim
      map_comp := by intros; ext; apply Subsingleton.elim }
  inverse :=
    { obj := fun i ↦ op ⟨i.left.unop, leOfHom i.hom.unop⟩
      map := fun f ↦ (homOfLE (leOfHom f.left.unop)).op
      map_id := by intros; apply Subsingleton.elim
      map_comp := by intros; apply Subsingleton.elim }
  unitIso := NatIso.ofComponents (fun i ↦ Iso.refl i)
  counitIso := NatIso.ofComponents
    (fun i ↦ Over.isoMk (Iso.refl i.left))

/-- Affineness of a stage morphism over an inverse limit descends to a finite stage. -/
theorem Scheme.exists_isAffineHom_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    {X₀ Y₀ : Scheme.{u}} [CompactSpace X₀] [QuasiSeparatedSpace X₀]
    [CompactSpace Y₀] [QuasiSeparatedSpace Y₀]
    (f₀ : X₀ ⟶ Y₀) (h : Y₀ ⟶ D.obj (op i₀))
    (hf : IsAffineHom
      (pullback.map (f₀ ≫ h) (c.π.app (op i₀)) h (c.π.app (op i₀))
        f₀ (𝟙 c.pt) (𝟙 (D.obj (op i₀)))
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm))) :
    ∃ (i : I) (hi : i₀ ≤ i), IsAffineHom
      (pullback.map (f₀ ≫ h) (D.map (homOfLE hi).op) h (D.map (homOfLE hi).op)
        f₀ (𝟙 (D.obj (op i))) (𝟙 (D.obj (op i₀)))
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) := by
  
  
  let : Nonempty I := ⟨i₀⟩
  let : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirected (Set.Ici i₀) (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨k, ha, hb⟩ := IsDirected.directed (r := (· ≤ ·)) a.val b.val
    exact ⟨⟨k, a.property.trans ha⟩, ha, hb⟩⟩
  let F := (upperTailEquivalence i₀).functor
  let E := F ⋙ baseChangeDiagram D (f₀ ≫ h)
  have : ∀ j, CompactSpace (E.obj j) := fun j ↦
    baseChangeDiagram_compactSpace (diagram := D) (f₀ ≫ h) (F.obj j)
  have : ∀ j, QuasiSeparatedSpace (E.obj j) := fun j ↦
    baseChangeDiagram_quasiSeparatedSpace (diagram := D) (f₀ ≫ h) (F.obj j)
  have : ∀ {j k} (a : j ⟶ k), IsAffineHom (E.map a) := fun a ↦ by
    change IsAffineHom ((baseChangeDiagram D (f₀ ≫ h)).map (F.map a))
    infer_instance
  let t := (baseChangeCone D c (f₀ ≫ h)).whisker F
  have ht : IsLimit t :=
    (Functor.Initial.isLimitWhiskerEquiv F _).symm
      (isLimitBaseChangeCone D c (f₀ ≫ h) hc)
  let g : E ⟶ (Functor.const (Set.Ici i₀)ᵒᵖ).obj Y₀ :=
    { app := fun j ↦ pullback.fst _ _ ≫ f₀
      naturality := by
        intro j k a
        simp [E] }
  let m := pullback.map (f₀ ≫ h) (c.π.app (op i₀)) h (c.π.app (op i₀))
    f₀ (𝟙 c.pt) (𝟙 (D.obj (op i₀)))
    (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)
  have : IsAffineHom (c.π.app (op i₀)) := isAffineHom_π_app D c hc _
  have : IsAffineHom (pullback.fst h (c.π.app (op i₀))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : IsAffineHom m := hf
  have hm : m ≫ pullback.fst h (c.π.app (op i₀)) =
      pullback.fst (f₀ ≫ h) (c.π.app (op i₀)) ≫ f₀ := by simp [m]
  have : IsAffineHom (pullback.fst (f₀ ≫ h) (c.π.app (op i₀)) ≫ f₀) := by
    rw [← hm]
    infer_instance
  obtain ⟨j, hj⟩ := Scheme.eventually_isAffineHom_of_isLimit Y₀ E g t ht
    (pullback.fst (f₀ ≫ h) (c.π.app (op i₀)) ≫ f₀) (by
      intro j
      simp [t, g, E])
  refine ⟨j.val, j.property, ?_⟩
  have H := hj j le_rfl
  change IsAffineHom
    (pullback.fst (f₀ ≫ h) (D.map (homOfLE j.property).op) ≫ f₀) at H
  have : IsAffineHom (pullback.fst h (D.map (homOfLE j.property).op)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  apply (IsAffineHom.comp_iff
    (g := pullback.fst h (D.map (homOfLE j.property).op))).mp
  simpa using H

end AlgebraicGeometry
end
