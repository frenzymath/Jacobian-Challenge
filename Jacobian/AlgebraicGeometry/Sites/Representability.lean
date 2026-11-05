import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.CategoryTheory.Sites.Over

/-!
# Local representability over a base scheme

A small-valued Zariski sheaf on schemes over a base is representable if it has
an open cover by representable subfunctors. It suffices to verify injectivity,
openness of the chart loci and local coverage on affine test schemes.

The total presheaf of pairs consisting of a structure morphism and a section
reduces relative representability to representability on schemes.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.LocalRepresentability

variable {S : Scheme.{u}} (P : (Over S)ᵒᵖ ⥤ Type w) [∀ T, Small.{u} (P.obj T)]

/-- A section over `Y` and a morphism to `Y` determine a section of the total presheaf. -/
noncomputable def sigmaOverMk {T : Scheme.{u}} {Y : Over S} (a : T ⟶ Y.left)
    (y : P.obj (op Y)) : Σ s : T ⟶ S, Shrink.{u} (P.obj (op (Over.mk s))) :=
  ⟨a ≫ Y.hom, equivShrink _ (P.map (Over.homMk a rfl : Over.mk (a ≫ Y.hom) ⟶ Y).op y)⟩

lemma sigma_mk_eq_iff {T : Scheme.{u}} {s s' : T ⟶ S} (x : P.obj (op (Over.mk s)))
    (x' : P.obj (op (Over.mk s'))) :
    (⟨s, equivShrink _ x⟩ : Σ s : T ⟶ S, Shrink.{u} (P.obj (op (Over.mk s)))) =
      ⟨s', equivShrink _ x'⟩ ↔ ∃ h : s = s',
        x = P.map (Over.homMk (𝟙 T) (by simp [h]) : Over.mk s ⟶ Over.mk s').op x' := by
  constructor
  · intro h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
    refine ⟨rfl, ?_⟩
    rw [show (Over.homMk (𝟙 T) (by simp) : Over.mk s ⟶ Over.mk s) = 𝟙 _ by ext; simp]
    simpa using (equivShrink _).injective (eq_of_heq h)
  · rintro ⟨rfl, rfl⟩
    rw [show (Over.homMk (𝟙 T) (by simp) : Over.mk s ⟶ Over.mk s) = 𝟙 _ by ext; simp]
    simp

lemma sigmaOverMk_eq_iff {W Y Y' : Over S} (a : W.left ⟶ Y.left) (a' : W.left ⟶ Y'.left)
    (ha : a ≫ Y.hom = W.hom) (ha' : a' ≫ Y'.hom = W.hom)
    (y : P.obj (op Y)) (y' : P.obj (op Y')) :
    sigmaOverMk P a y = sigmaOverMk P a' y' ↔
      P.map (Over.homMk a ha).op y = P.map (Over.homMk a' ha').op y' := by
  rw [sigmaOverMk, sigmaOverMk, sigma_mk_eq_iff]
  let i : W ⟶ Over.mk (a ≫ Y.hom) := Over.homMk (𝟙 W.left) (by simp [ha])
  let j : Over.mk (a ≫ Y.hom) ⟶ W := Over.homMk (𝟙 W.left) (by simp [ha])
  have hij : j ≫ i = 𝟙 _ := by ext; simp [i, j]
  have e₁ : (Over.homMk a ha : W ⟶ Y) = i ≫ Over.homMk a rfl := by ext; simp [i]
  have e₂ : (Over.homMk a' ha' : W ⟶ Y') = i ≫
      (Over.homMk (𝟙 W.left) (by simp [ha, ha']) :
        Over.mk (a ≫ Y.hom) ⟶ Over.mk (a' ≫ Y'.hom)) ≫
        Over.homMk a' rfl := by ext; simp [i]
  rw [e₁, e₂]
  simp only [op_comp, Functor.map_comp_apply]
  constructor
  · rintro ⟨h, h'⟩
    rw [h']
  · intro h
    refine ⟨by rw [ha, ha'], ?_⟩
    have key : ∀ z, P.map j.op (P.map i.op z) = z := by
      intro z
      rw [← Functor.map_comp_apply, ← op_comp, hij, op_id, Functor.map_id_apply]
    have := congrArg (P.map j.op) h
    rwa [key, key] at this

lemma sigmaOverMk_id {T : Scheme.{u}} (x : Σ s : T ⟶ S, Shrink.{u} (P.obj (op (Over.mk s)))) :
    sigmaOverMk P (Y := Over.mk x.1) (𝟙 T) ((equivShrink _).symm x.2) = x := by
  obtain ⟨s, x⟩ := x
  obtain ⟨x, rfl⟩ := (equivShrink _).surjective x
  rw [sigmaOverMk, Equiv.symm_apply_apply, sigma_mk_eq_iff]
  exact ⟨by simp, rfl⟩

lemma sigmaOverMk_comp {T T' : Scheme.{u}} {Y : Over S} (b : T' ⟶ T) (a : T ⟶ Y.left)
    (y : P.obj (op Y)) :
    sigmaOverMk P (Y := Over.mk (a ≫ Y.hom)) b
      ((equivShrink _).symm (sigmaOverMk P a y).2) = sigmaOverMk P (b ≫ a) y := by
  rw [sigmaOverMk_eq_iff P (W := Over.mk (b ≫ a ≫ Y.hom)) _ _ rfl (by simp)]
  simp only [sigmaOverMk, Equiv.symm_apply_apply]
  rw [← Functor.map_comp_apply, ← op_comp]
  congr 3

/-- The presheaf of pairs consisting of a structure morphism and a section over that base. -/
@[simps obj]
noncomputable def sigmaOver : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := Σ s : T.unop ⟶ S, Shrink.{u} (P.obj (op (Over.mk s)))
  map a := ↾fun x ↦ sigmaOverMk P (Y := Over.mk x.1) a.unop ((equivShrink _).symm x.2)
  map_id T := by
    ext x : 3
    exact sigmaOverMk_id P x
  map_comp {T T' T''} a b := by
    ext x : 3
    obtain ⟨s, x⟩ := x
    obtain ⟨x, rfl⟩ := (equivShrink _).surjective x
    dsimp
    rw [Equiv.symm_apply_apply]
    exact (sigmaOverMk_comp P (Y := Over.mk s) b.unop a.unop x).symm

lemma sigmaOver_map_sigmaOverMk {T T' : Scheme.{u}} {Y : Over S} (b : T' ⟶ T) (a : T ⟶ Y.left)
    (y : P.obj (op Y)) :
    (sigmaOver P).map b.op (sigmaOverMk P a y) = sigmaOverMk P (b ≫ a) y :=
  sigmaOverMk_comp P b a y

lemma sigmaOverMk_map {T : Scheme.{u}} {W Z : Over S} (a : T ⟶ W.left) (g : W ⟶ Z)
    (z : P.obj (op Z)) :
    sigmaOverMk P a (P.map g.op z) = sigmaOverMk P (a ≫ g.left) z := by
  rw [sigmaOverMk_eq_iff P (W := Over.mk (a ≫ W.hom)) _ _ rfl (by simp)]
  rw [← Functor.map_comp_apply, ← op_comp]
  congr 3

lemma sigmaOverMk_injective {Y : Over S} :
    Function.Injective (sigmaOverMk P (𝟙 Y.left) : P.obj (op Y) → _) := by
  intro y y' h
  rw [sigmaOverMk_eq_iff P (W := Y) _ _ (by simp) (by simp)] at h
  have e : (Over.homMk (𝟙 Y.left) (by simp) : Y ⟶ Y) = 𝟙 Y := by ext; simp
  simpa [e] using h

noncomputable def toObj {Z : Over S} (q : (sigmaOver P).obj (op Z.left)) (hq : q.1 = Z.hom) :
    P.obj (op Z) :=
  P.map (Over.homMk (𝟙 Z.left) (by simp [hq]) : Z ⟶ Over.mk q.1).op ((equivShrink _).symm q.2)

lemma sigmaOverMk_toObj {Z : Over S} (q : (sigmaOver P).obj (op Z.left)) (hq : q.1 = Z.hom) :
    sigmaOverMk P (𝟙 Z.left) (toObj P q hq) = q := by
  rw [toObj, sigmaOverMk_map]
  conv_rhs => rw [← sigmaOverMk_id P q]
  rw [sigmaOverMk_eq_iff P (W := Z) _ _ (by simp [hq]) (by simp [hq])]
  congr 3

/-- The total presheaf of a relative Zariski sheaf is a Zariski sheaf on schemes. -/
theorem isSheaf_sigmaOver (hP : Presheaf.IsSheaf (zariskiTopology.over S) P) :
    Presheaf.IsSheaf zariskiTopology (sigmaOver P) := by
  rw [isSheaf_iff_isSheaf_of_type] at hP ⊢
  intro T R hR x hx
  have hS : Presieve.IsSheaf zariskiTopology (yoneda.obj S) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (zariskiTopology.yoneda.obj S).property
  let xS : Presieve.FamilyOfElements (yoneda.obj S) R.arrows := fun V f hf ↦ (x f hf).1
  have hxS : xS.Compatible := by
    intro V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ e
    exact congr_arg Sigma.fst (hx g₁ g₂ h₁ h₂ e)
  obtain ⟨s, hs, hs'⟩ := hS R hR xS hxS
  replace hs : ∀ (V : Scheme.{u}) (f : V ⟶ T) (hf : R f), f ≫ s = (x f hf).1 := hs
  let R' := (Sieve.overEquiv (Over.mk s)).symm R
  have hR' : R' ∈ zariskiTopology.over S (Over.mk s) :=
    GrothendieckTopology.overEquiv_symm_mem_over _ _ _ hR
  have hR'iff {Z : Over S} (g : Z ⟶ Over.mk s) : R'.arrows g ↔ R g.left :=
    Sieve.overEquiv_symm_iff _ _
  let y : Presieve.FamilyOfElements P R'.arrows := fun Z g hg ↦
    toObj P (x g.left ((hR'iff g).1 hg)) (by rw [← hs]; exact Over.w g)
  have hy (Z : Over S) (g : Z ⟶ Over.mk s) (hg : R'.arrows g) :
      sigmaOverMk P (𝟙 Z.left) (y g hg) = x g.left ((hR'iff g).1 hg) :=
    sigmaOverMk_toObj _ _ _
  have hyc : y.Compatible := by
    intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ e
    apply sigmaOverMk_injective P
    rw [sigmaOverMk_map, sigmaOverMk_map, Category.id_comp, Category.id_comp,
      ← Category.comp_id g₁.left, ← Category.comp_id g₂.left,
      ← sigmaOver_map_sigmaOverMk, ← sigmaOver_map_sigmaOverMk, hy _ _ h₁, hy _ _ h₂]
    exact hx _ _ _ _ (congr_arg CommaMorphism.left e)
  obtain ⟨t, ht, ht'⟩ := hP R' hR' y hyc
  refine ⟨sigmaOverMk P (Y := Over.mk s) (𝟙 T) t, ?_, ?_⟩
  · intro V f hf
    have hg : R'.arrows (Over.homMk f rfl : Over.mk (f ≫ s) ⟶ Over.mk s) := (hR'iff _).2 hf
    rw [sigmaOver_map_sigmaOverMk, Category.comp_id]
    refine Eq.trans ?_ (hy _ _ hg)
    rw [← ht _ hg, sigmaOverMk_map, Category.id_comp]
    rfl
  · intro q hq
    have h₁ : q.1 = s := hs' q.1 (fun V f hf ↦ congr_arg Sigma.fst (hq f hf))
    rw [← sigmaOverMk_toObj P (Z := Over.mk s) q h₁]
    congr 1
    refine ht' _ (fun Z g hg ↦ sigmaOverMk_injective P ?_)
    rw [hy _ _ hg, sigmaOverMk_map, Category.id_comp]
    refine Eq.trans (b := (sigmaOver P).map g.left.op
      (sigmaOverMk P (Y := Over.mk s) (𝟙 _) (toObj P (Z := Over.mk s) q h₁))) ?_ ?_
    · rw [sigmaOver_map_sigmaOverMk, Category.comp_id]
    · rw [sigmaOverMk_toObj]
      exact hq _ _

section

variable {P} {ι : Type u} (X : ι → Over S) (ξ : ∀ i, P.obj (op (X i)))

noncomputable def toSigmaOver (i : ι) : yoneda.obj (X i).left ⟶ sigmaOver P :=
  yonedaEquiv.symm (sigmaOverMk P (𝟙 (X i).left) (ξ i))

lemma toSigmaOver_app {V : Scheme.{u}} (i : ι) (e : V ⟶ (X i).left) :
    (toSigmaOver X ξ i).app (op V) e = sigmaOverMk P e (ξ i) := by
  change (sigmaOver P).map e.op (sigmaOverMk P (𝟙 (X i).left) (ξ i)) = _
  rw [sigmaOver_map_sigmaOverMk, Category.comp_id]

variable {X ξ}

lemma exists_isPullback_toSigmaOver
    (hinj : ∀ i {T : Over S} (a b : T ⟶ X i), P.map a.op (ξ i) = P.map b.op (ξ i) → a = b)
    {i : ι} {T : Over S} {y : P.obj (op T)} {U : T.left.Opens}
    (hU : ∀ (W : Over S) (a : W ⟶ T),
      (∃ b : W ⟶ X i, P.map a.op y = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ U) :
    ∃ c : (U : Scheme.{u}) ⟶ (X i).left, ∀ (V : Scheme.{u}) (e : V ⟶ (X i).left)
      (a : V ⟶ T.left), sigmaOverMk P e (ξ i) = sigmaOverMk P a y ↔
        ∃ d : V ⟶ U, d ≫ c = e ∧ d ≫ U.ι = a := by
  obtain ⟨b₀, hb₀⟩ := (hU (Over.mk (U.ι ≫ T.hom)) (Over.homMk U.ι rfl)).2
    (by simp [Scheme.Opens.range_ι])
  refine ⟨b₀.left, fun V e a ↦ ?_⟩
  have key (W : Over S) (d : W.left ⟶ U) (hd : d ≫ U.ι ≫ T.hom = W.hom) :
      P.map (Over.homMk (d ≫ b₀.left) (by simp [Over.w b₀, hd]) : W ⟶ X i).op (ξ i) =
        P.map (Over.homMk (d ≫ U.ι) (by simp [hd]) : W ⟶ T).op y := by
    have e₁ : (Over.homMk (d ≫ b₀.left) (by simp [Over.w b₀, hd]) : W ⟶ X i) =
        (Over.homMk d (by simp [hd]) : W ⟶ Over.mk (U.ι ≫ T.hom)) ≫ b₀ := by ext; simp
    have e₂ : (Over.homMk (d ≫ U.ι) (by simp [hd]) : W ⟶ T) =
        (Over.homMk d (by simp [hd]) : W ⟶ Over.mk (U.ι ≫ T.hom)) ≫
          Over.homMk U.ι rfl := by ext; simp
    rw [e₁, e₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hb₀]
  constructor
  · intro h
    have h₁ : e ≫ (X i).hom = a ≫ T.hom := congr_arg Sigma.fst h
    rw [sigmaOverMk_eq_iff P (W := Over.mk (a ≫ T.hom)) _ _ h₁ rfl] at h
    have hr : Set.range a ⊆ U := (hU (Over.mk (a ≫ T.hom)) (Over.homMk a rfl)).1 ⟨_, h.symm⟩
    let d := IsOpenImmersion.lift U.ι a (by rwa [Scheme.Opens.range_ι])
    have hd : d ≫ U.ι = a := IsOpenImmersion.lift_fac _ _ _
    refine ⟨d, ?_, hd⟩
    have := key (Over.mk (a ≫ T.hom)) d (by simp [← hd])
    have e₃ : (Over.homMk (d ≫ U.ι) (by simp [hd]) : Over.mk (a ≫ T.hom) ⟶ T) =
        Over.homMk a rfl := by ext; simp [hd]
    rw [e₃, ← h] at this
    exact congr_arg CommaMorphism.left (hinj i _ _ this)
  · rintro ⟨d, rfl, rfl⟩
    rw [sigmaOverMk_eq_iff P (W := Over.mk (d ≫ U.ι ≫ T.hom)) _ _ (by simp [Over.w b₀])
      (by simp)]
    exact key (Over.mk (d ≫ U.ι ≫ T.hom)) d rfl

end

lemma isRepresentable_of_isRepresentable_sigmaOver [(sigmaOver P).IsRepresentable] :
    P.IsRepresentable := by
  obtain ⟨Y, ⟨e⟩⟩ := Functor.IsRepresentable.has_representation (F := sigmaOver P)
  set u := e.homEquiv (𝟙 Y)
  let A : Over S := Over.mk u.1
  let y₀ : P.obj (op A) := (equivShrink _).symm u.2
  have he {T : Scheme.{u}} (a : T ⟶ Y) : e.homEquiv a = sigmaOverMk P (Y := A) a y₀ := by
    rw [← Category.comp_id a, e.homEquiv_comp]
    refine (congr_arg ((sigmaOver P).map a.op) (sigmaOverMk_id P u).symm).trans ?_
    rw [sigmaOver_map_sigmaOverMk, Category.comp_id]
  have hbij (W : Over S) : Function.Bijective (fun a : W ⟶ A ↦ P.map a.op y₀) := by
    refine ⟨fun a b h ↦ ?_, fun z ↦ ?_⟩
    · have h' : sigmaOverMk P a.left y₀ = sigmaOverMk P b.left y₀ :=
        (sigmaOverMk_eq_iff P (W := W) _ _ (Over.w a) (Over.w b) _ _).2 h
      rw [← he, ← he] at h'
      exact Over.OverMorphism.ext (e.homEquiv.injective h')
    · have hq := e.homEquiv.apply_symm_apply (sigmaOverMk P (𝟙 W.left) z)
      rw [he] at hq
      have h₁ : e.homEquiv.symm (sigmaOverMk P (𝟙 W.left) z) ≫ A.hom = W.hom := by
        simpa [sigmaOverMk] using congr_arg Sigma.fst hq
      refine ⟨Over.homMk _ h₁, ?_⟩
      replace hq := (sigmaOverMk_eq_iff P (W := W) _ _ h₁ (by simp) _ _).1 hq
      have e₁ : (Over.homMk (𝟙 W.left) (by simp) : W ⟶ W) = 𝟙 W := by ext; simp
      simpa [e₁] using hq
  exact ⟨A, ⟨{
    homEquiv := Equiv.ofBijective _ (hbij _)
    homEquiv_comp := fun f a ↦ by simp }⟩⟩

/-- A Zariski sheaf over a base, locally covered by representable open subfunctors,
is representable. -/
theorem isRepresentable_of_isSheaf_over (hP : Presheaf.IsSheaf (zariskiTopology.over S) P)
    {ι : Type u} (X : ι → Over S) (ξ : ∀ i, P.obj (op (X i)))
    (hinj : ∀ i {T : Over S} (a b : T ⟶ X i), P.map a.op (ξ i) = P.map b.op (ξ i) → a = b)
    (hopen : ∀ i (T : Over S) (x : P.obj (op T)), ∃ U : T.left.Opens,
      ∀ (W : Over S) (a : W ⟶ T),
        (∃ b : W ⟶ X i, P.map a.op x = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ U)
    (hcov : ∀ (T : Over S) (x : P.obj (op T)) (t : T.left),
      ∃ (i : ι) (W : Over S) (a : W ⟶ T) (b : W ⟶ X i),
        t ∈ Set.range a.left ∧ P.map a.op x = P.map b.op (ξ i)) :
    P.IsRepresentable := by
  let F : Sheaf zariskiTopology (Type u) := ⟨sigmaOver P, isSheaf_sigmaOver P hP⟩
  let f : (i : ι) → yoneda.obj (X i).left ⟶ F.obj := toSigmaOver X ξ
  have hpb (i : ι) (T : Scheme.{u}) (x : (sigmaOver P).obj (op T)) :
      ∃ (U : T.Opens) (c : (U : Scheme.{u}) ⟶ (X i).left),
        (∀ (V : Scheme.{u}) (e : V ⟶ (X i).left) (a : V ⟶ T),
          (f i).app (op V) e = (sigmaOver P).map a.op x ↔
            ∃ d : V ⟶ U, d ≫ c = e ∧ d ≫ U.ι = a) ∧
        ∀ t : T, (∃ (W : Over S) (a : W ⟶ Over.mk x.1) (b : W ⟶ X i),
          t ∈ Set.range a.left ∧ P.map a.op ((equivShrink _).symm x.2) = P.map b.op (ξ i)) →
            t ∈ U := by
    obtain ⟨U, hU⟩ := hopen i (Over.mk x.1) ((equivShrink _).symm x.2)
    obtain ⟨c, hc⟩ := exists_isPullback_toSigmaOver hinj hU
    refine ⟨U, c, fun V e a ↦ ?_, fun t ⟨W, a, b, ht, h⟩ ↦ (hU W a).1 ⟨b, h⟩ ht⟩
    rw [toSigmaOver_app, ← hc V e a]
    conv_lhs => rw [← sigmaOverMk_id P x]
    rw [sigmaOver_map_sigmaOverMk, Category.comp_id]
  have hf (i : ι) : IsOpenImmersion.presheaf (f i) := by
    refine MorphismProperty.relative.of_exists (fun T g ↦ ?_)
    obtain ⟨U, c, hc, -⟩ := hpb i T (yonedaEquiv g)
    refine ⟨U, yoneda.map c, U.ι, IsPullback.of_forall_isPullback_app (fun V ↦ ?_),
      inferInstance⟩
    rw [Types.isPullback_iff]
    refine ⟨?_, fun d d' ⟨_, h⟩ ↦ (cancel_mono U.ι).1 h, fun e a h ↦ ?_⟩
    · ext d : 3
      change (f i).app V (d ≫ c) = g.app V (d ≫ U.ι)
      rw [← map_yonedaEquiv g]
      exact (hc V.unop _ _).2 ⟨d, rfl, rfl⟩
    · replace h : (f i).app V e = g.app V a := h
      rw [← map_yonedaEquiv g] at h
      exact (hc V.unop e a).1 h
  have : Presheaf.IsLocallySurjective zariskiTopology (Sigma.desc f) := by
    refine ⟨fun {T} x ↦ ?_⟩
    have H (t : T) : ∃ (i : ι) (U : T.Opens) (c : (U : Scheme.{u}) ⟶ (X i).left),
        t ∈ U ∧ (f i).app (op U) c = (sigmaOver P).map U.ι.op x := by
      obtain ⟨i, W, a, b, ht, h⟩ := hcov (Over.mk x.1) ((equivShrink _).symm x.2) t
      obtain ⟨U, c, hc, hU⟩ := hpb i T x
      exact ⟨i, U, c, hU t ⟨W, a, b, ht, h⟩, (hc _ _ _).2 ⟨𝟙 _, by simp, by simp⟩⟩
    choose i U c ht hc using H
    rw [mem_grothendieckTopology_iff]
    refine ⟨Scheme.Cover.mkOfCovers T (fun t ↦ (U t : Scheme.{u})) (fun t ↦ (U t).ι)
      (fun t ↦ ⟨t, by
        have h : t ∈ Set.range (U t).ι := by rw [Scheme.Opens.range_ι]; exact ht t
        exact h⟩), ?_⟩
    rintro V g ⟨t⟩
    refine ⟨(Sigma.ι (fun i ↦ yoneda.obj (X i).left) (i t)).app _ (c t), ?_⟩
    refine Eq.trans ?_ (hc t)
    exact congr_arg
      (fun φ : yoneda.obj (X (i t)).left ⟶ F.obj ↦ φ.app (op (U t : Scheme)) (c t))
      (Sigma.ι_desc f (i t))
  have := Scheme.LocalRepresentability.isRepresentable (F := F) hf
  exact isRepresentable_of_isRepresentable_sigmaOver P

section Affine

variable {P} {ι : Type u} {X : ι → Over S} {ξ : ∀ i, P.obj (op (X i))}

lemma exists_map_eq_iff_exists_sigmaOverMk_eq {W T : Over S} (a : W ⟶ T) (x : P.obj (op T))
    (i : ι) : (∃ b : W ⟶ X i, P.map a.op x = P.map b.op (ξ i)) ↔
      ∃ c : W.left ⟶ (X i).left, sigmaOverMk P a.left x = sigmaOverMk P c (ξ i) := by
  constructor
  · rintro ⟨b, h⟩
    exact ⟨b.left, (sigmaOverMk_eq_iff P (W := W) _ _ (Over.w a) (Over.w b) _ _).2 h⟩
  · rintro ⟨c, h⟩
    have hc : c ≫ (X i).hom = W.hom := by
      rw [← Over.w a]
      exact (congr_arg Sigma.fst h).symm
    exact ⟨Over.homMk c hc, (sigmaOverMk_eq_iff P (W := W) _ _ (Over.w a) hc _ _).1 h⟩

lemma eq_of_sigmaOverMk_eq
    (hinj : ∀ i {T : Over S} [IsAffine T.left] (a b : T ⟶ X i),
      P.map a.op (ξ i) = P.map b.op (ξ i) → a = b)
    {i : ι} {T : Scheme.{u}} {c c' : T ⟶ (X i).left}
    (h : sigmaOverMk P c (ξ i) = sigmaOverMk P c' (ξ i)) : c = c' := by
  refine T.affineCover.hom_ext _ _ fun j ↦ ?_
  have h' := congr_arg ((sigmaOver P).map (T.affineCover.f j).op) h
  rw [sigmaOver_map_sigmaOverMk, sigmaOver_map_sigmaOverMk] at h'
  have h₁ : (T.affineCover.f j ≫ c') ≫ (X i).hom = (T.affineCover.f j ≫ c) ≫ (X i).hom :=
    (congr_arg Sigma.fst h').symm
  rw [sigmaOverMk_eq_iff P (W := Over.mk ((T.affineCover.f j ≫ c) ≫ (X i).hom)) _ _ rfl h₁]
    at h'
  have : IsAffine (Over.mk ((T.affineCover.f j ≫ c) ≫ (X i).hom)).left := by
    dsimp
    infer_instance
  exact congr_arg CommaMorphism.left (hinj i _ _ h')

lemma exists_sigmaOverMk_eq_of_openCover (hP : Presheaf.IsSheaf (zariskiTopology.over S) P)
    (hinj : ∀ i {T : Scheme.{u}} (c c' : T ⟶ (X i).left),
      sigmaOverMk P c (ξ i) = sigmaOverMk P c' (ξ i) → c = c')
    {i : ι} {T : Scheme.{u}} (s : (sigmaOver P).obj (op T))
    (𝒰 : Scheme.OpenCover.{u} T)
    (h : ∀ j, ∃ c : 𝒰.X j ⟶ (X i).left,
      (sigmaOver P).map (𝒰.f j).op s = sigmaOverMk P c (ξ i)) :
    ∃ c : T ⟶ (X i).left, s = sigmaOverMk P c (ξ i) := by
  choose c hc using h
  have hglue (j k : 𝒰.I₀) : pullback.fst (𝒰.f j) (𝒰.f k) ≫ c j = pullback.snd _ _ ≫ c k := by
    refine hinj i _ _ ?_
    rw [← sigmaOver_map_sigmaOverMk, ← sigmaOver_map_sigmaOverMk, ← hc, ← hc,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      pullback.condition]
  refine ⟨𝒰.glueMorphisms c hglue, ?_⟩
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_sigmaOver P hP)
  refine (hF.isSeparated (Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f))
    (mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩)).ext ?_
  rintro V _ ⟨Z, g, _, ⟨j⟩, rfl⟩
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hc, sigmaOver_map_sigmaOverMk,
    sigmaOver_map_sigmaOverMk, sigmaOver_map_sigmaOverMk, 𝒰.ι_glueMorphisms]

lemma exists_sigmaOverMk_eq_of_forall_mem (hP : Presheaf.IsSheaf (zariskiTopology.over S) P)
    (hinj : ∀ i {T : Scheme.{u}} (c c' : T ⟶ (X i).left),
      sigmaOverMk P c (ξ i) = sigmaOverMk P c' (ξ i) → c = c')
    {i : ι} {T : Scheme.{u}} (s : (sigmaOver P).obj (op T))
    (h : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ c : (U : Scheme.{u}) ⟶ (X i).left,
      (sigmaOver P).map U.ι.op s = sigmaOverMk P c (ξ i)) :
    ∃ c : T ⟶ (X i).left, s = sigmaOverMk P c (ξ i) := by
  choose U hU c hc using h
  let 𝒰 : Scheme.OpenCover.{u} T := {
    I₀ := T, X t := U t, f t := (U t).ι,
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      exact ⟨fun t ↦ ⟨t, by simpa using hU t⟩, inferInstance⟩ }
  exact exists_sigmaOverMk_eq_of_openCover hP hinj s 𝒰 fun t ↦ ⟨c t, hc t⟩

lemma exists_opens_sigmaOver (hP : Presheaf.IsSheaf (zariskiTopology.over S) P)
    (hinj : ∀ i {T : Scheme.{u}} (c c' : T ⟶ (X i).left),
      sigmaOverMk P c (ξ i) = sigmaOverMk P c' (ξ i) → c = c') {i : ι}
    (hopen : ∀ (T : Scheme.{u}) [IsAffine T] (s : (sigmaOver P).obj (op T)), ∃ U : T.Opens,
      ∀ (W : Scheme.{u}) [IsAffine W] (a : W ⟶ T),
        (∃ c : W ⟶ (X i).left, (sigmaOver P).map a.op s = sigmaOverMk P c (ξ i)) ↔
          Set.range a ⊆ U)
    {T : Scheme.{u}} (s : (sigmaOver P).obj (op T)) : ∃ U : T.Opens,
      ∀ (W : Scheme.{u}) (a : W ⟶ T),
        (∃ c : W ⟶ (X i).left, (sigmaOver P).map a.op s = sigmaOverMk P c (ξ i)) ↔
          Set.range a ⊆ U := by
  let L (V : T.Opens) : Prop :=
    ∃ c : (V : Scheme.{u}) ⟶ (X i).left, (sigmaOver P).map V.ι.op s = sigmaOverMk P c (ξ i)
  refine ⟨sSup {V | L V}, fun W a ↦ ⟨?_, fun ha ↦ ?_⟩⟩
  · rintro ⟨c, hc⟩ _ ⟨w, rfl⟩
    obtain ⟨V₀ : T.Opens, hV₀, hw, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.isBasis_affineOpens
        (show a w ∈ (⊤ : T.Opens) from trivial)
    have : IsAffine V₀ := hV₀
    obtain ⟨U₀, hU₀⟩ := hopen V₀ ((sigmaOver P).map V₀.ι.op s)
    refine (TopologicalSpace.Opens.mem_sSup).2 ⟨V₀.ι ''ᵁ U₀, ?_, ?_⟩
    ·
      obtain ⟨c', hc'⟩ : ∃ c' : (U₀ : Scheme.{u}) ⟶ (X i).left,
          (sigmaOver P).map (U₀.ι ≫ V₀.ι).op s = sigmaOverMk P c' (ξ i) := by
        refine exists_sigmaOverMk_eq_of_openCover hP hinj _ (U₀ : Scheme.{u}).affineCover
          fun j ↦ ?_
        rw [← Functor.map_comp_apply, ← op_comp, ← Category.assoc, op_comp,
          Functor.map_comp_apply]
        refine (hU₀ _ _).2 ?_
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, ← Scheme.Opens.range_ι U₀]
        exact Set.range_comp_subset_range _ _
      refine ⟨(V₀.ι.isoImage U₀).inv ≫ c', ?_⟩
      rw [← Scheme.Hom.isoImage_inv_ι, op_comp, Functor.map_comp_apply, hc',
        sigmaOver_map_sigmaOverMk]
    ·
      obtain ⟨W' : W.Opens, hW', hwW', hW'le⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.1 W.isBasis_affineOpens
        (show w ∈ a ⁻¹ᵁ V₀ from hw)
      have : IsAffine W' := hW'
      have hr : Set.range (a.resLE V₀ W' hW'le) ⊆ U₀ := by
        refine (hU₀ _ _).1 ⟨W'.ι ≫ c, ?_⟩
        rw [← Functor.map_comp_apply, ← op_comp, Scheme.Hom.resLE_comp_ι, op_comp,
          Functor.map_comp_apply, hc, sigmaOver_map_sigmaOverMk]
      refine ⟨a.resLE V₀ W' hW'le ⟨w, hwW'⟩, hr ⟨_, rfl⟩, ?_⟩
      simp
  · refine exists_sigmaOverMk_eq_of_forall_mem hP hinj _ fun w ↦ ?_
    obtain ⟨V, ⟨c, hc⟩, hV⟩ := (TopologicalSpace.Opens.mem_sSup).1 (ha ⟨w, rfl⟩)
    refine ⟨a ⁻¹ᵁ V, hV, a.resLE V (a ⁻¹ᵁ V) le_rfl ≫ c, ?_⟩
    rw [← Functor.map_comp_apply, ← op_comp, ← Scheme.Hom.resLE_comp_ι, op_comp,
      Functor.map_comp_apply, hc, sigmaOver_map_sigmaOverMk]

end Affine

/-- Representability by open charts can be checked on affine test schemes. -/
theorem isRepresentable_of_isSheaf_over_of_isAffine
    (hP : Presheaf.IsSheaf (zariskiTopology.over S) P)
    {ι : Type u} (X : ι → Over S) (ξ : ∀ i, P.obj (op (X i)))
    (hinj : ∀ i {T : Over S} [IsAffine T.left] (a b : T ⟶ X i),
      P.map a.op (ξ i) = P.map b.op (ξ i) → a = b)
    (hopen : ∀ i (T : Over S) [IsAffine T.left] (x : P.obj (op T)), ∃ U : T.left.Opens,
      ∀ (W : Over S) [IsAffine W.left] (a : W ⟶ T),
        (∃ b : W ⟶ X i, P.map a.op x = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ U)
    (hcov : ∀ (T : Over S) [IsAffine T.left] (x : P.obj (op T)) (t : T.left),
      ∃ (i : ι) (W : Over S) (a : W ⟶ T) (b : W ⟶ X i),
        t ∈ Set.range a.left ∧ P.map a.op x = P.map b.op (ξ i)) :
    P.IsRepresentable := by
  have hinj' (i : ι) {T : Scheme.{u}} (c c' : T ⟶ (X i).left)
      (h : sigmaOverMk P c (ξ i) = sigmaOverMk P c' (ξ i)) : c = c' :=
    eq_of_sigmaOverMk_eq hinj h
  have hmap {T : Scheme.{u}} (s : (sigmaOver P).obj (op T)) {W : Scheme.{u}} (a : W ⟶ T) :
      (sigmaOver P).map a.op s = sigmaOverMk P (Y := Over.mk s.1) a ((equivShrink _).symm s.2) := by
    conv_lhs => rw [← sigmaOverMk_id P s]
    rw [sigmaOver_map_sigmaOverMk, Category.comp_id]
  refine isRepresentable_of_isSheaf_over P hP X ξ (fun i T a b h ↦ ?_) (fun i T x ↦ ?_)
    (fun T x t ↦ ?_)
  · exact Over.OverMorphism.ext (hinj' i _ _
      ((sigmaOverMk_eq_iff P (W := T) _ _ (Over.w a) (Over.w b) _ _).2 h))
  ·
    obtain ⟨U, hU⟩ := exists_opens_sigmaOver hP hinj' (i := i) (fun T hT s ↦ by
      obtain ⟨U, hU⟩ := @hopen i (Over.mk s.1) hT ((equivShrink _).symm s.2)
      refine ⟨U, fun W hW a ↦ ?_⟩
      rw [hmap]
      exact (exists_map_eq_iff_exists_sigmaOverMk_eq _ _ i).symm.trans
        (@hU (Over.mk (a ≫ s.1)) hW (Over.homMk a rfl))) (sigmaOverMk P (𝟙 T.left) x)
    refine ⟨U, fun W a ↦ ?_⟩
    rw [exists_map_eq_iff_exists_sigmaOverMk_eq, ← hU, sigmaOver_map_sigmaOverMk,
      Category.comp_id]
  ·
    obtain ⟨V : T.left.Opens, hV, ht, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 T.left.isBasis_affineOpens
        (show t ∈ (⊤ : T.left.Opens) from trivial)
    have : IsAffine (Over.mk (V.ι ≫ T.hom)).left := hV
    let x' := P.map (Over.homMk V.ι rfl : Over.mk (V.ι ≫ T.hom) ⟶ T).op x
    obtain ⟨i, W, a, b, ⟨w, hw⟩, h⟩ := hcov (Over.mk (V.ι ≫ T.hom)) x' ⟨t, ht⟩
    refine ⟨i, W, a ≫ Over.homMk V.ι rfl, b, ⟨w, ?_⟩, ?_⟩
    · simpa using congr_arg Subtype.val hw
    · rw [op_comp, Functor.map_comp_apply, h]

end AlgebraicGeometry.Scheme.LocalRepresentability
