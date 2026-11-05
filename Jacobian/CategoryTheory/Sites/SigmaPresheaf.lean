import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Presheaves over a represented presheaf

The dependent sum of a presheaf on an over-category gives a presheaf on the underlying category.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe w v u

open CategoryTheory Opposite

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] {Z : C}

/-- Two pairs whose sections are pulled back from the same section along morphisms with the
same underlying morphism in `C` agree. -/
lemma sigmaPresheaf_mk_map_eq (P : (Over Z)ᵒᵖ ⥤ Type w) {Y : C} {y y' : Y ⟶ Z} (e : y = y')
    {T : Over Z} (h : Over.mk y ⟶ T) (h' : Over.mk y' ⟶ T) (hh : h.left = h'.left)
    (t : P.obj (op T)) :
    (⟨y, P.map h.op t⟩ : Σ y : Y ⟶ Z, P.obj (op (Over.mk y))) = ⟨y', P.map h'.op t⟩ := by
  subst e
  obtain rfl : h = h' := Over.OverMorphism.ext hh
  rfl

/-- A pair whose section is pulled back along a morphism over `Z` with identity underlying
morphism agrees with the original pair. -/
lemma sigmaPresheaf_mk_map_eq_self (P : (Over Z)ᵒᵖ ⥤ Type w) {Y : C} {y y' : Y ⟶ Z}
    (e : y = y') (h : Over.mk y ⟶ Over.mk y') (hh : h.left = 𝟙 Y)
    (t : P.obj (op (Over.mk y'))) :
    (⟨y, P.map h.op t⟩ : Σ y : Y ⟶ Z, P.obj (op (Over.mk y))) = ⟨y', t⟩ :=
  (sigmaPresheaf_mk_map_eq P e h (𝟙 _) hh t).trans (by simp)

/-- The presheaf on `C` of pairs `(y : Y ⟶ Z, p)` with `p` a section of `P` over `Over.mk y`. -/
def sigmaPresheaf (P : (Over Z)ᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type (max v w) where
  obj Y := Σ y : Y.unop ⟶ Z, P.obj (op (Over.mk y))
  map g := ↾fun x ↦ ⟨g.unop ≫ x.1,
    P.map (Over.homMk g.unop rfl : Over.mk (g.unop ≫ x.1) ⟶ Over.mk x.1).op x.2⟩
  map_id Y := by
    refine ConcreteCategory.hom_ext _ _ fun ⟨y, p⟩ ↦ ?_
    exact sigmaPresheaf_mk_map_eq_self P (Category.id_comp y) _ (by rfl) p
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ fun ⟨y, p⟩ ↦ ?_
    refine (sigmaPresheaf_mk_map_eq P (y' := g.unop ≫ f.unop ≫ y) (by simp) _
      ((Over.homMk g.unop rfl : Over.mk (g.unop ≫ f.unop ≫ y) ⟶ Over.mk (f.unop ≫ y)) ≫
        (Over.homMk f.unop rfl : Over.mk (f.unop ≫ y) ⟶ Over.mk y)) (by simp) p).trans ?_
    rw [op_comp, Functor.map_comp_apply]
    rfl

/-- If `sigmaPresheaf P` is a sheaf for the underlying family in `C` of a family of morphisms
in `Over Z`, and the representable presheaf of `Z` is separated for it, then `P` is a sheaf for
the family. -/
theorem isSheafFor_ofArrows_of_sigmaPresheaf (P : (Over Z)ᵒᵖ ⥤ Type w) {Y : Over Z}
    {ι : Type*} {W : ι → Over Z} (g : ∀ i, W i ⟶ Y)
    (hQ : (Presieve.ofArrows (fun i ↦ (W i).left) (fun i ↦ (g i).left)).IsSheafFor
      (sigmaPresheaf P))
    (hZ : (Presieve.ofArrows (fun i ↦ (W i).left) (fun i ↦ (g i).left)).IsSeparatedFor
      (yoneda.obj Z)) :
    (Presieve.ofArrows W g).IsSheafFor P := by
  rw [Presieve.isSheafFor_arrows_iff] at hQ ⊢
  intro x hx
  have hmap (i : ι) (p : P.obj (op Y)) :
      (sigmaPresheaf P).map (g i).left.op ⟨Y.hom, p⟩ = ⟨(W i).hom, P.map (g i).op p⟩ :=
    sigmaPresheaf_mk_map_eq P (Over.w (g i)) _ (g i) rfl p
  obtain ⟨⟨y, p⟩, ht, huniq⟩ := hQ (fun i ↦ ⟨(W i).hom, x i⟩) fun i j T gi gj h ↦ by
    have e : gi ≫ (W i).hom = gj ≫ (W j).hom := by
      rw [← Over.w (g i), ← Over.w (g j), ← Category.assoc, h, Category.assoc]
    exact (congrArg (Sigma.mk (β := fun y : T ⟶ Z ↦ P.obj (op (Over.mk y))) _)
      (hx i j (Over.mk (gi ≫ (W i).hom)) (Over.homMk gi rfl) (Over.homMk gj e.symm)
        (Over.OverMorphism.ext (by simpa using h)))).trans
      (sigmaPresheaf_mk_map_eq P e _ _ rfl _)
  obtain rfl : y = Y.hom := hZ.ext fun _ _ ⟨i⟩ ↦
    (congrArg Sigma.fst (ht i)).trans (Over.w (g i)).symm
  refine ⟨p, fun i ↦ eq_of_heq (Sigma.mk.inj_iff.1 ((hmap i p).symm.trans (ht i))).2,
    fun p' hp' ↦ eq_of_heq (Sigma.mk.inj_iff.1 (huniq ⟨Y.hom, p'⟩ fun i ↦ ?_)).2⟩
  rw [hmap, hp']

/-- If the representable presheaf of `Z` is a sheaf for a family `u i : U i ⟶ Y` in `C`, and `P`
is a sheaf for the corresponding families over every `y : Y ⟶ Z`, then `sigmaPresheaf P` is a
sheaf for the family. -/
theorem isSheafFor_sigmaPresheaf (P : (Over Z)ᵒᵖ ⥤ Type w) {Y : C} {ι : Type*} {U : ι → C}
    (u : ∀ i, U i ⟶ Y) (hZ : (Presieve.ofArrows U u).IsSheafFor (yoneda.obj Z))
    (hP : ∀ y : Y ⟶ Z, (Presieve.ofArrows (fun i ↦ Over.mk (u i ≫ y))
      (fun i ↦ (Over.homMk (u i) rfl : Over.mk (u i ≫ y) ⟶ Over.mk y))).IsSheafFor P) :
    (Presieve.ofArrows U u).IsSheafFor (sigmaPresheaf P) := by
  rw [Presieve.isSheafFor_arrows_iff] at hZ ⊢
  intro x hx
  obtain ⟨y, hy, hyuniq⟩ := hZ (fun i ↦ (x i).1) fun i j T gi gj h ↦
    congrArg Sigma.fst (hx i j T gi gj h)
  have hy' (i : ι) : u i ≫ y = (x i).1 := hy i
  let q (i : ι) : P.obj (op (Over.mk (u i ≫ y))) :=
    P.map (Over.homMk (𝟙 _) (by simp [hy']) : Over.mk (u i ≫ y) ⟶ Over.mk (x i).1).op (x i).2
  have hq (i : ι) : (⟨u i ≫ y, q i⟩ : Σ y : U i ⟶ Z, P.obj (op (Over.mk y))) = x i :=
    sigmaPresheaf_mk_map_eq_self P (hy' i) _ rfl _
  have hq' (i : ι) (T : Over Z) (gi : T ⟶ Over.mk (u i ≫ y)) :
      (⟨T.hom, P.map gi.op (q i)⟩ : Σ y : T.left ⟶ Z, P.obj (op (Over.mk y))) =
        (sigmaPresheaf P).map gi.left.op (x i) := by
    rw [← Functor.map_comp_apply, ← op_comp]
    refine sigmaPresheaf_mk_map_eq P ?_ _ _ (by simp) _
    rw [← hy' i, ← Over.w gi]
    rfl
  obtain ⟨p, hp, hpuniq⟩ := (Presieve.isSheafFor_arrows_iff P _).1 (hP y) q
      fun i j T gi gj h ↦ by
    refine eq_of_heq (Sigma.mk.inj_iff.1 ((hq' i T gi).trans
      ((hx i j T.left gi.left gj.left ?_).trans (hq' j T gj).symm))).2
    simpa using congrArg CommaMorphism.left h
  refine ⟨⟨y, p⟩, fun i ↦ ?_, fun ⟨y', p'⟩ ht ↦ ?_⟩
  · refine Eq.trans ?_ (hq i)
    rw [← hp i]
    rfl
  · obtain rfl : y' = y := hyuniq y' fun i ↦ congrArg Sigma.fst (ht i)
    refine congrArg (Sigma.mk y') (hpuniq p' fun i ↦
      eq_of_heq (Sigma.mk.inj_iff.1 ((ht i).trans (hq i).symm)).2)

end CategoryTheory.Over
