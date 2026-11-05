import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.CategoryTheory.Sites.Over

/-!
# Open subfunctors of presheaves on schemes

A subfunctor is represented by open immersions precisely when its membership
condition after arbitrary pullback is the condition that the test morphism
lands in an open subscheme. This formulation allows large-valued presheaves
through the lifted Yoneda functor.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- Pulling back a subfunctor represented by open immersions gives an open
membership locus on every test scheme. -/
lemma exists_opens_of_relative_isOpenImmersion {S : Scheme.{u}}
    {P : (Over S)ᵒᵖ ⥤ Type (max w u)} {F : Subfunctor P}
    (hF : (IsOpenImmersion.inverseImage (Over.forget S)).relative uliftYoneda.{w} F.ι)
    (T : Over S) (x : P.obj (op T)) :
    ∃ U : T.left.Opens, ∀ (W : Over S) (a : W ⟶ T),
      P.map a.op x ∈ F.obj (op W) ↔ Set.range a.left ⊆ U := by
  let g : uliftYoneda.{w}.obj T ⟶ P := uliftYonedaEquiv.symm x
  have hg {W : Over S} (a : W ⟶ T) : g.app (op W) (ULift.up a) = P.map a.op x := rfl
  have hpb := hF.rep.isPullback g
  have hsnd : IsOpenImmersion (hF.rep.snd g).left := hF.property_snd g
  refine ⟨(hF.rep.snd g).left.opensRange, fun W a ↦ ?_⟩
  rw [Scheme.Hom.coe_opensRange]
  constructor
  · intro h
    obtain ⟨d, -, hd⟩ := Types.exists_of_isPullback (hpb.app (op W)) ⟨_, h⟩ (ULift.up a)
      (by rw [hg]; rfl)
    replace hd : d.down ≫ hF.rep.snd g = a := congr_arg ULift.down hd
    rw [← hd, Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  · intro h
    let d : W ⟶ hF.rep.pullback g := Over.homMk (IsOpenImmersion.lift _ a.left h) (by
      rw [← Over.w (hF.rep.snd g), IsOpenImmersion.lift_fac_assoc, Over.w a])
    have hd : d ≫ hF.rep.snd g = a := by ext; exact IsOpenImmersion.lift_fac _ _ _
    have := congr_arg (fun φ ↦ φ.app (op W) (ULift.up d)) hpb.w
    have h₂ : P.map a.op x = ((hF.rep.fst g).app (op W) (ULift.up d)).1 := by
      rw [← hg, ← hd]
      exact this.symm
    rw [h₂]
    exact ((hF.rep.fst g).app (op W) (ULift.up d)).2

/-- Open membership loci, compatible with every test morphism, make a
subfunctor inclusion representable by open immersions. -/
lemma relative_isOpenImmersion_of_exists_opens {S : Scheme.{u}}
    {P : (Over S)ᵒᵖ ⥤ Type (max w u)} {F : Subfunctor P}
    (hF : ∀ (T : Over S) (x : P.obj (op T)), ∃ U : T.left.Opens, ∀ (W : Over S) (a : W ⟶ T),
      P.map a.op x ∈ F.obj (op W) ↔ Set.range a.left ⊆ U) :
    (IsOpenImmersion.inverseImage (Over.forget S)).relative uliftYoneda.{w} F.ι := by
  refine MorphismProperty.relative.of_exists fun T g ↦ ?_
  obtain ⟨x, rfl⟩ := uliftYonedaEquiv.symm.surjective g
  obtain ⟨U, hU⟩ := hF T x
  let b : Over S := Over.mk (U.ι ≫ T.hom)
  let snd : b ⟶ T := Over.homMk U.ι
  have hb : P.map snd.op x ∈ F.obj (op b) :=
    (hU b snd).2 (by change Set.range U.ι ⊆ U; rw [Scheme.Opens.range_ι])
  refine ⟨b, uliftYonedaEquiv.symm ⟨_, hb⟩, snd,
    IsPullback.of_forall_isPullback_app fun W ↦ ?_, ?_⟩
  · rw [Types.isPullback_iff]
    refine ⟨?_, fun d d' ⟨_, h⟩ ↦ ?_, fun e a h ↦ ?_⟩
    · ext d
      change P.map d.down.op (P.map snd.op x) = P.map (d.down ≫ snd).op x
      rw [op_comp, Functor.map_comp_apply]
    · replace h : d.down.left ≫ U.ι = d'.down.left ≫ U.ι := congr_arg (·.down.left) h
      exact ULift.ext _ _ (Over.OverMorphism.ext ((cancel_mono U.ι).1 h))
    · replace h : e.1 = P.map a.down.op x := h
      have hrange : Set.range a.down.left.base ⊆ Set.range U.ι.base := by
        rw [Scheme.Opens.range_ι, ← hU, ← h]
        exact e.2
      let d : W.unop ⟶ b := Over.homMk (IsOpenImmersion.lift U.ι a.down.left hrange) (by
        simp [b, IsOpenImmersion.lift_fac_assoc])
      have hd : d ≫ snd = a.down := by ext; exact IsOpenImmersion.lift_fac _ _ _
      refine ⟨ULift.up d, Subtype.ext ?_, ULift.ext _ _ hd⟩
      change P.map d.op (P.map snd.op x) = e.1
      rw [← Functor.map_comp_apply, ← op_comp, hd, h]
  · change IsOpenImmersion U.ι
    infer_instance

end AlgebraicGeometry
