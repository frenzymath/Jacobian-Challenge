import Jacobian.AlgebraicGeometry.Limits.Separated
import Jacobian.AlgebraicGeometry.ChowLemma
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Relative
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Properness at a finite stage

For a family of finite type over Noetherian stages of an affine-transition
inverse system, properness of a stage morphism after base change to the limit
descends to a later stage. Chow's lemma supplies a proper surjective modification
with a projective immersion; eventual closedness of that immersion proves
universal closedness. Projective coordinates may be any finite type.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem over_natIso_property
    {S S' : Scheme.{u}} (F G : Over S ⥤ Over S') (e : F ≅ G)
    {X Y : Over S} (f : X ⟶ Y) (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    P (F.map f).left ↔ P (G.map f).left := by
  let ex := (Over.forget S').mapIso (e.app X)
  let ey := (Over.forget S').mapIso (e.app Y)
  apply P.arrow_mk_iso_iff
  exact Arrow.isoMk ex ey (congrArg (fun k ↦ k.left) (e.hom.naturality f).symm)

private theorem exists_closed_chow_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀)))
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left]
    (hf : IsProper (((Over.pullback (c.π.app (op i₀))).map f₀).left))
    (i₁ : I) (h₁ : i₀ ≤ i₁)
    (hsep : IsSeparated (((Over.pullback (D.map (homOfLE h₁).op)).map f₀).left))
    (coordinates : Type u) [Finite coordinates] (T₁ : Scheme.{u})
    (π₁ : T₁ ⟶ ((Over.pullback (D.map (homOfLE h₁).op)).obj X₀).left)
    (j₁ : T₁ ⟶ ProjectiveSpace coordinates
      ((Over.pullback (D.map (homOfLE h₁).op)).obj Y₀).left)
    (hπ₁ : IsProper π₁) (hsurj₁ : Surjective π₁) (hj₁ : IsImmersion j₁)
    (hw₁ : j₁ ≫ ProjectiveSpace coordinates
      ((Over.pullback (D.map (homOfLE h₁).op)).obj Y₀).left ↘
        ((Over.pullback (D.map (homOfLE h₁).op)).obj Y₀).left =
      π₁ ≫ ((Over.pullback (D.map (homOfLE h₁).op)).map f₀).left) :
    ∃ (i : I) (h₁i : i₁ ≤ i)
      (π : pullback (π₁ ≫ ((Over.pullback (D.map (homOfLE h₁).op)).obj X₀).hom)
          (D.map (homOfLE h₁i).op) ⟶
        ((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).obj X₀).left)
      (j : pullback (π₁ ≫ ((Over.pullback (D.map (homOfLE h₁).op)).obj X₀).hom)
          (D.map (homOfLE h₁i).op) ⟶
        ProjectiveSpace coordinates
          ((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).obj Y₀).left),
      Surjective π ∧ IsClosedImmersion j ∧
        j ≫ ProjectiveSpace coordinates
          ((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).obj Y₀).left ↘
            ((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).obj Y₀).left =
          π ≫ ((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).map f₀).left ∧
        IsSeparated (((Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)).map f₀).left) := by
  let B := Over.pullback (D.map (homOfLE h₁).op)
  let X₁ := B.obj X₀
  let Y₁ := B.obj Y₀
  let f₁ := B.map f₀
  let T : Over (D.obj (op i₁)) := Over.mk (π₁ ≫ X₁.hom)
  let Q : Over (D.obj (op i₁)) :=
    Over.mk (ProjectiveSpace coordinates Y₁.left ↘ Y₁.left ≫ Y₁.hom)
  let p : T ⟶ X₁ := Over.homMk π₁
  let q : Q ⟶ Y₁ := Over.homMk
    (ProjectiveSpace coordinates Y₁.left ↘ Y₁.left)
  let j : T ⟶ Q := Over.homMk j₁ (by
    change j₁ ≫ _ ≫ Y₁.hom = π₁ ≫ X₁.hom
    rw [← Category.assoc, hw₁, Category.assoc]
    exact congrArg (π₁ ≫ ·) f₁.w)
  have hjq : j ≫ q = p ≫ f₁ := by
    ext
    exact hw₁
  let L := Over.pullback (c.π.app (op i₁))
  have hcomp : c.π.app (op i₁) ≫ D.map (homOfLE h₁).op = c.π.app (op i₀) := by
    exact c.w (homOfLE h₁).op
  have hfL : IsProper (L.map f₁).left := by
    have hF : IsProper (((Over.pullback
        (c.π.app (op i₁) ≫ D.map (homOfLE h₁).op)).map f₀).left) := by
      rw [hcomp]
      exact hf
    exact (over_natIso_property _ _
      (Over.pullbackComp (c.π.app (op i₁)) (D.map (homOfLE h₁).op))
      f₀ (@IsProper)).mp hF
  have hpL : IsProper (L.map p).left :=
    MorphismProperty.overPullbackMap _ p hπ₁
  have hqL : IsSeparated (L.map q).left :=
    MorphismProperty.overPullbackMap _ q (inferInstanceAs (IsSeparated
      (ProjectiveSpace coordinates Y₁.left ↘ Y₁.left)))
  have hjL : IsImmersion (L.map j).left :=
    MorphismProperty.overPullbackMap _ j hj₁
  have : IsProper ((L.map j).left ≫ (L.map q).left) := by
    have : IsProper ((L.map p).left ≫ (L.map f₁).left) := by
      let := hpL
      let := hfL
      infer_instance
    simpa only [← Over.comp_left, ← CategoryTheory.Functor.map_comp, hjq] using this
  have : IsProper (L.map j).left := by
    let := hqL
    exact IsProper.of_comp _ (L.map q).left
  have hjclosed : IsClosedImmersion (L.map j).left := by
    let := hjL
    exact IsClosedImmersion.of_isPreimmersion _
      (Scheme.Hom.isClosedMap (L.map j).left).isClosed_range
  have : CompactSpace (D.obj (op i₁)) :=
    QuasiCompact.compactSpace_of_compactSpace (D.map (homOfLE h₁).op)
  have : QuasiSeparatedSpace (D.obj (op i₁)) :=
    quasiSeparatedSpace_of_quasiSeparated (D.map (homOfLE h₁).op)
  have : CompactSpace X₁.left := by
    dsimp [X₁, B, Over.pullback]
    infer_instance
  have : QuasiSeparatedSpace X₁.left := by
    dsimp [X₁, B, Over.pullback]
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)
  have : CompactSpace Y₁.left := by
    dsimp [Y₁, B, Over.pullback]
    infer_instance
  have : QuasiSeparatedSpace Y₁.left := by
    dsimp [Y₁, B, Over.pullback]
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)
  have : CompactSpace T.left := by
    let := hπ₁
    exact QuasiCompact.compactSpace_of_compactSpace π₁
  have : QuasiSeparatedSpace T.left := by
    let := hπ₁
    exact quasiSeparatedSpace_of_quasiSeparated π₁
  have : CompactSpace Q.left :=
    QuasiCompact.compactSpace_of_compactSpace
      (ProjectiveSpace coordinates Y₁.left ↘ Y₁.left)
  have : QuasiSeparatedSpace Q.left := by
    dsimp [Q]
    exact quasiSeparatedSpace_of_quasiSeparated
      (ProjectiveSpace coordinates Y₁.left ↘ Y₁.left)
  have : LocallyOfFiniteType j.left := by
    let := hj₁
    exact inferInstanceAs (LocallyOfFiniteType j₁)
  let J := {i : I // i₁ ≤ i}
  have : IsDirected J (· ≤ ·) := ⟨by
    intro a b
    obtain ⟨k, ha, hb⟩ := exists_ge_ge a.val b.val
    exact ⟨⟨k, a.property.trans ha⟩, ha, hb⟩⟩
  let F : J ⥤ I := (Subtype.mono_coe _).functor
  have : F.Final := by
    apply (Subtype.mono_coe _).final_functor_iff.mpr
    intro i
    obtain ⟨k, hi, h₁k⟩ := exists_ge_ge i i₁
    exact ⟨⟨k, h₁k⟩, hi⟩
  let D' := F.op ⋙ D
  have : ∀ {i j : Jᵒᵖ} (t : i ⟶ j), IsAffineHom (D'.map t) :=
    fun t ↦ inferInstanceAs (IsAffineHom (D.map (F.op.map t)))
  let c' := c.whisker F.op
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv F.op c).symm hc
  let k₁ : J := ⟨i₁, le_rfl⟩
  have : CompactSpace (D'.obj (op k₁)) :=
    inferInstanceAs (CompactSpace (D.obj (op i₁)))
  have : QuasiSeparatedSpace (D'.obj (op k₁)) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj (op i₁)))
  have hlimit : IsClosedImmersion
      (((Over.pullback (c'.π.app (op k₁))).map j).left) := hjclosed
  obtain ⟨k, hk, hclosed⟩ :=
    Scheme.exists_isClosedImmersion_baseChange_of_isLimit D' c' hc' k₁ T Q j hlimit
  have hclosed' : IsClosedImmersion
      (((Over.pullback (D.map (homOfLE k.property).op))).map j).left := hclosed
  let g := D.map (homOfLE k.property).op
  let C := Over.pullback g
  let Bi := Over.pullback (D.map (homOfLE (h₁.trans k.property)).op)
  have hg : g ≫ D.map (homOfLE h₁).op =
      D.map (homOfLE (h₁.trans k.property)).op := by
    rw [← D.map_comp]
    rfl
  let e : Bi ≅ B ⋙ C := by
    dsimp [Bi, B, C]
    rw [← hg]
    exact Over.pullbackComp g (D.map (homOfLE h₁).op)
  let ex : (Bi.obj X₀).left ≅ (C.obj X₁).left :=
    (Over.forget (D.obj (op k.val))).mapIso (e.app X₀)
  let ey : (Bi.obj Y₀).left ≅ (C.obj Y₁).left :=
    (Over.forget (D.obj (op k.val))).mapIso (e.app Y₀)
  let Yi := (Bi.obj Y₀).left
  let π := (C.map p).left ≫ ex.inv
  have hsurjC : Surjective (C.map p).left :=
    MorphismProperty.overPullbackMap _ p hsurj₁
  have hsurjπ : Surjective π := by
    let := hsurjC
    dsimp [π]
    infer_instance
  have hsepC : IsSeparated (C.map f₁).left :=
    MorphismProperty.overPullbackMap _ f₁ hsep
  have hsepi : IsSeparated (Bi.map f₀).left :=
    (over_natIso_property _ _ e f₀ (@IsSeparated)).mpr hsepC
  let v : Yi ⟶ Y₁.left := ey.hom ≫ pullback.fst Y₁.hom g
  let sYi : Yi ⟶ D.obj (op k.val) := ey.hom ≫ pullback.snd Y₁.hom g
  have hY : IsPullback v sYi Y₁.hom g := by
    exact (IsPullback.of_hasPullback Y₁.hom g).of_iso'
      ey (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [v]) (by simp [sYi]) (by simp) (by simp)
  have hQ := (ProjectiveSpace.isPullback_map coordinates v).paste_vert hY
  let eQ := hQ.isoPullback
  have hq : eQ.hom ≫ (C.map q).left =
      (ProjectiveSpace coordinates Yi ↘ Yi) ≫ ey.hom := by
    apply pullback.hom_ext
    · simp only [C, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
      change hQ.isoPullback.hom ≫
        (pullback.fst
          ((ProjectiveSpace coordinates Y₁.left ↘ Y₁.left) ≫ Y₁.hom) g) ≫
          (ProjectiveSpace coordinates Y₁.left ↘ Y₁.left) =
        (ProjectiveSpace coordinates Yi ↘ Yi) ≫ v
      rw [← Category.assoc, hQ.isoPullback_hom_fst]
      exact ProjectiveSpace.map_over coordinates v
    · simp only [C, Over.pullback_map_left, Category.assoc, pullback.lift_snd]
      exact hQ.isoPullback_hom_snd
  let jᵢ := (C.map j).left ≫ eQ.inv
  have hjᵢ : IsClosedImmersion jᵢ := by
    have : IsClosedImmersion (C.map j).left := hclosed'
    dsimp [jᵢ]
    infer_instance
  have hqinv : eQ.inv ≫
      (ProjectiveSpace coordinates Yi ↘ Yi) =
      (C.map q).left ≫ ey.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hq]
    simp
  have heinv : ex.inv ≫ (Bi.map f₀).left = (C.map f₁).left ≫ ey.inv := by
    exact (congrArg (fun z ↦ z.left) (e.inv.naturality f₀)).symm
  refine ⟨k.val, k.property, π, jᵢ, hsurjπ, hjᵢ, ?_, hsepi⟩
  change (C.map j).left ≫ eQ.inv ≫
    (ProjectiveSpace coordinates Yi ↘ Yi) =
    ((C.map p).left ≫ ex.inv) ≫ (Bi.map f₀).left
  rw [hqinv, ← Category.assoc, ← Over.comp_left,
    ← CategoryTheory.Functor.map_comp, hjq, CategoryTheory.Functor.map_comp, Over.comp_left, Category.assoc, ← heinv]
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry
end

section
universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Properness over an affine-transition limit descends to a Noetherian finite type stage. -/
theorem Scheme.exists_isProper_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [∀ i, IsLocallyNoetherian (D.obj i)]
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    {X₀ Y₀ : Scheme.{u}} [CompactSpace X₀] [QuasiSeparatedSpace X₀]
    [CompactSpace Y₀] [QuasiSeparatedSpace Y₀]
    (a : X₀ ⟶ D.obj (op i₀)) (b : Y₀ ⟶ D.obj (op i₀))
    [LocallyOfFiniteType a]
    (f₀ : X₀ ⟶ Y₀) (h : f₀ ≫ b = a) [LocallyOfFiniteType f₀]
    (hf : IsProper (pullback.map a (c.π.app (op i₀)) b (c.π.app (op i₀))
      f₀ (𝟙 c.pt) (𝟙 (D.obj (op i₀)))
      ((Category.comp_id a).trans h.symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm))) :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsProper (pullback.map a (D.map (homOfLE hi).op) b (D.map (homOfLE hi).op)
        f₀ (𝟙 (D.obj (op i))) (𝟙 (D.obj (op i₀)))
        ((Category.comp_id a).trans h.symm)
        ((Category.comp_id _).trans (Category.id_comp _).symm)) := by
  let X : Over (D.obj (op i₀)) := Over.mk a
  let Y : Over (D.obj (op i₀)) := Over.mk b
  let f : X ⟶ Y := Over.homMk f₀ h
  have : CompactSpace X.left := inferInstanceAs (CompactSpace X₀)
  have : QuasiSeparatedSpace X.left := inferInstanceAs (QuasiSeparatedSpace X₀)
  have : CompactSpace Y.left := inferInstanceAs (CompactSpace Y₀)
  have : QuasiSeparatedSpace Y.left := inferInstanceAs (QuasiSeparatedSpace Y₀)
  have : LocallyOfFiniteType f.left := inferInstanceAs (LocallyOfFiniteType f₀)
  have hf' : IsProper (((Over.pullback (c.π.app (op i₀))).map f).left) := by
    simpa [X, Y, f, Over.pullback, pullback.map] using hf
  have hsep : IsSeparated (((Over.pullback (c.π.app (op i₀))).map f).left) :=
    hf'.toIsSeparated
  obtain ⟨i₁, h₁, hsep₁⟩ := Scheme.exists_isSeparated_overPullbackMap D c hc i₀ X Y f hsep
  let B := Over.pullback (D.map (homOfLE h₁).op)
  have : IsSeparated (B.map f).left := hsep₁
  have : LocallyOfFiniteType (B.map f).left :=
    MorphismProperty.overPullbackMap _ f (inferInstance : LocallyOfFiniteType f.left)
  have : CompactSpace (B.obj Y).left := by dsimp [B, Y, Over.pullback]; infer_instance
  have : QuasiSeparatedSpace (B.obj Y).left := by
    dsimp [B, Y, Over.pullback]
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)
  have : CompactSpace (B.obj X).left := by dsimp [B, X, Over.pullback]; infer_instance
  have : LocallyOfFiniteType X.hom := inferInstanceAs (LocallyOfFiniteType a)
  have : IsLocallyNoetherian (B.obj X).left := by
    dsimp [B, Over.pullback]
    infer_instance
  have : IsNoetherian (B.obj X).left := IsNoetherian.mk
  obtain ⟨T₁, π₁, coordinates, finiteCoordinates, j₁, hπ₁, hsurj₁, hj₁, hw₁, _⟩ :=
    exists_chowModification_of_finite_irreducibleComponents (B.map f).left
      NoetherianSpace.finite_irreducibleComponents
  obtain ⟨i, h₁i, π, j, hsurj, hj, hw, hsepᵢ⟩ :=
    exists_closed_chow_stage D c hc i₀ X Y f hf' i₁ h₁ hsep₁
      coordinates T₁ π₁ j₁ hπ₁ hsurj₁ hj₁ hw₁
  let Bi := Over.pullback (D.map (homOfLE (h₁.trans h₁i)).op)
  have : Surjective π := hsurj
  have : IsClosedImmersion j := hj
  have : IsProper (π ≫ (Bi.map f).left) := by
    rw [← hw]
    infer_instance
  have : IsSeparated (Bi.map f).left := hsepᵢ
  have : LocallyOfFiniteType (Bi.map f).left :=
    MorphismProperty.overPullbackMap _ f (inferInstance : LocallyOfFiniteType f.left)
  have hp : IsProper (Bi.map f).left := by
    rw [isProper_iff]
    exact ⟨inferInstance, UniversallyClosed.of_comp_surjective π _, inferInstance⟩
  refine ⟨i, h₁.trans h₁i, ?_⟩
  simpa [Bi, X, Y, f, Over.pullback, pullback.map] using hp

end AlgebraicGeometry
end
