import Jacobian.AlgebraicGeometry.Modules.ZariskiDescent
import Jacobian.AlgebraicGeometry.Modules.PullbackSections

/-!
# The module sheaf of compatible descent sections

For a family of scheme morphisms, compatible local sections of a module descent
datum form a module sheaf. The maps `glueCounit` assemble into
`glueToDescentData`, and `toGlue` factors morphisms from the descent data of a
module through this sheaf. No covering hypothesis is needed for the construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

/-- The pullback along `y : Y ⟶ X` of a section `s` of `M` over `V`, restricted to an open `O`
of `Y` contained in `y ⁻¹ᵁ V`. -/
noncomputable def pullbackRestrict {X Y : Scheme.{u}} (y : Y ⟶ X) (M : X.Modules) {V : X.Opens}
    {O : Y.Opens} (h : O ≤ y ⁻¹ᵁ V) (s : Γ(M, V)) : Γ((pullback y).obj M, O) :=
  ((pullback y).obj M).presheaf.map (homOfLE h).op (pullbackUnitApp y M V s)

section pullbackRestrict

variable {X Y : Scheme.{u}} (y : Y ⟶ X) (M : X.Modules) {V : X.Opens} {O : Y.Opens}
  (h : O ≤ y ⁻¹ᵁ V)

@[simp]
lemma pullbackRestrict_zero : pullbackRestrict y M h 0 = 0 := by
  simp [pullbackRestrict]

@[simp]
lemma pullbackRestrict_add (s t : Γ(M, V)) :
    pullbackRestrict y M h (s + t) = pullbackRestrict y M h s + pullbackRestrict y M h t := by
  simp [pullbackRestrict]

@[simp]
lemma pullbackRestrict_neg (s : Γ(M, V)) :
    pullbackRestrict y M h (-s) = -pullbackRestrict y M h s := by
  simp [pullbackRestrict]

lemma pullbackRestrict_smul (r : Γ(X, V)) (s : Γ(M, V)) :
    pullbackRestrict y M h (r • s) =
      Y.presheaf.map (homOfLE h).op (y.app V r) • pullbackRestrict y M h s := by
  rw [pullbackRestrict, pullbackUnitApp_smul, map_smul]
  rfl

/-- Restricting `pullbackRestrict` to a smaller open. -/
lemma presheaf_map_pullbackRestrict {O' : Y.Opens} (i : O' ⟶ O) (s : Γ(M, V)) :
    ((pullback y).obj M).presheaf.map i.op (pullbackRestrict y M h s) =
      pullbackRestrict y M (i.le.trans h) s := by
  rw [pullbackRestrict, pullbackRestrict, presheaf_map_map_apply]
  rfl

/-- `pullbackRestrict` of a restricted section. -/
lemma pullbackRestrict_presheaf_map {V' : X.Opens} (i : V ⟶ V') (s : Γ(M, V')) :
    pullbackRestrict y M h (M.presheaf.map i.op s) =
      pullbackRestrict y M (h.trans (y.preimage_mono i.le)) s := by
  rw [pullbackRestrict, pullbackRestrict, pullbackUnitApp_presheaf_map, presheaf_map_map_apply]
  rfl

end pullbackRestrict

/-- Pulling back a function along `y` and `g` and restricting to `O` is pulling it back along
any `k = y ≫ g` and restricting to `O`. -/
lemma presheaf_map_app_app_eq_of_comp_eq {S X Y : Scheme.{u}} {y : Y ⟶ X} {g : X ⟶ S}
    {k : Y ⟶ S} (hk : y ≫ g = k) {V : S.Opens} {O : Y.Opens} (h : O ≤ y ⁻¹ᵁ g ⁻¹ᵁ V)
    (h' : O ≤ k ⁻¹ᵁ V) (r : Γ(S, V)) :
    Y.presheaf.map (homOfLE h).op (y.app _ (g.app V r)) =
      Y.presheaf.map (homOfLE h').op (k.app V r) := by
  subst hk
  rfl

/-- Pulling back functions along two morphisms with the same composite and restricting to an
open contained in both preimages gives the same result. -/
lemma presheaf_map_app_app_eq {S X₁ X₂ Y : Scheme.{u}} {y₁ : Y ⟶ X₁} {y₂ : Y ⟶ X₂}
    {g₁ : X₁ ⟶ S} {g₂ : X₂ ⟶ S} (h : y₁ ≫ g₁ = y₂ ≫ g₂) {V : S.Opens} {O : Y.Opens}
    (h₁ : O ≤ y₁ ⁻¹ᵁ g₁ ⁻¹ᵁ V) (h₂ : O ≤ y₂ ⁻¹ᵁ g₂ ⁻¹ᵁ V) (r : Γ(S, V)) :
    Y.presheaf.map (homOfLE h₁).op (y₁.app _ (g₁.app V r)) =
      Y.presheaf.map (homOfLE h₂).op (y₂.app _ (g₂.app V r)) := by
  rw [presheaf_map_app_app_eq_of_comp_eq h.symm h₂ h₁]
  rfl

/-- Two morphisms with the same composite to `S` have the same preimages of opens of `S`. -/
lemma preimage_preimage_eq_of_comp_eq {S X₁ X₂ Y : Scheme.{u}} {y₁ : Y ⟶ X₁} {y₂ : Y ⟶ X₂}
    {g₁ : X₁ ⟶ S} {g₂ : X₂ ⟶ S} (h : y₁ ≫ g₁ = y₂ ≫ g₂) (V : S.Opens) :
    y₁ ⁻¹ᵁ g₁ ⁻¹ᵁ V = y₂ ⁻¹ᵁ g₂ ⁻¹ᵁ V :=
  congrArg (fun k ↦ k ⁻¹ᵁ V) h

variable {S : Scheme.{u}} {J : Type u} {W : J → Scheme.{u}} {f : ∀ a, W a ⟶ S}
  (D : modulesPseudofunctor.DescentData f)

/-- The object `D.obj a` of a descent datum, as a sheaf of modules on `W a`. -/
abbrev descentObj (a : J) : (W a).Modules := D.obj a

/-- The morphisms `D.hom` of a descent datum, as morphisms of sheaves of modules. -/
def descentHom ⦃Y : Scheme.{u}⦄ (q : Y ⟶ S) ⦃a b : J⦄ (f₁ : Y ⟶ W a) (f₂ : Y ⟶ W b)
    (hf₁ : f₁ ≫ f a = q) (hf₂ : f₂ ≫ f b = q) :
    (pullback f₁).obj (descentObj D a) ⟶ (pullback f₂).obj (descentObj D b) :=
  D.hom q f₁ f₂ hf₁ hf₂

/-- Two sections `s` of `D a` and `t` of `D b` over the preimages of `V` are compatible if for
all `y₁ : Y ⟶ W a`, `y₂ : Y ⟶ W b` over `S` the descent datum `D.hom` sends the pullback of `s`
to the pullback of `t`, on every open of `Y` contained in both preimages of `V`. -/
def DescentCompat (V : S.Opens) {a b : J} (s : Γ(descentObj D a, f a ⁻¹ᵁ V))
    (t : Γ(descentObj D b, f b ⁻¹ᵁ V)) : Prop :=
  ∀ ⦃Y : Scheme.{u}⦄ (y₁ : Y ⟶ W a) (y₂ : Y ⟶ W b) (h : y₁ ≫ f a = y₂ ≫ f b) (O : Y.Opens)
    (h₁ : O ≤ y₁ ⁻¹ᵁ f a ⁻¹ᵁ V) (h₂ : O ≤ y₂ ⁻¹ᵁ f b ⁻¹ᵁ V),
    (D.hom (y₁ ≫ f a) y₁ y₂ rfl h.symm).app O
      (((pullback y₁).obj (descentObj D a)).presheaf.map (homOfLE h₁).op
        (pullbackUnitApp y₁ _ _ s)) =
      ((pullback y₂).obj (descentObj D b)).presheaf.map (homOfLE h₂).op
        (pullbackUnitApp y₂ _ _ t)

/-- `DescentCompat` in terms of `pullbackRestrict`. -/
lemma descentCompat_iff (V : S.Opens) {a b : J} (s : Γ(descentObj D a, f a ⁻¹ᵁ V))
    (t : Γ(descentObj D b, f b ⁻¹ᵁ V)) :
    DescentCompat D V s t ↔
      ∀ ⦃Y : Scheme.{u}⦄ (y₁ : Y ⟶ W a) (y₂ : Y ⟶ W b) (h : y₁ ≫ f a = y₂ ≫ f b) (O : Y.Opens)
        (h₁ : O ≤ y₁ ⁻¹ᵁ f a ⁻¹ᵁ V) (h₂ : O ≤ y₂ ⁻¹ᵁ f b ⁻¹ᵁ V),
        (descentHom D (y₁ ≫ f a) y₁ y₂ rfl h.symm).app O (pullbackRestrict y₁ _ h₁ s) =
          pullbackRestrict y₂ _ h₂ t :=
  Iff.rfl

namespace DescentCompat

variable {D} {V : S.Opens} {a b : J} {s s' : Γ(descentObj D a, f a ⁻¹ᵁ V)}
  {t t' : Γ(descentObj D b, f b ⁻¹ᵁ V)}

lemma zero : DescentCompat D V (0 : Γ(descentObj D a, f a ⁻¹ᵁ V))
    (0 : Γ(descentObj D b, f b ⁻¹ᵁ V)) := by
  rw [descentCompat_iff]
  intro Y y₁ y₂ h O h₁ h₂
  rw [pullbackRestrict_zero, pullbackRestrict_zero, map_zero]

lemma add (hs : DescentCompat D V s t) (hs' : DescentCompat D V s' t') :
    DescentCompat D V (s + s') (t + t') := by
  rw [descentCompat_iff] at *
  intro Y y₁ y₂ h O h₁ h₂
  rw [pullbackRestrict_add, pullbackRestrict_add, map_add, hs y₁ y₂ h O h₁ h₂,
    hs' y₁ y₂ h O h₁ h₂]

lemma neg (hs : DescentCompat D V s t) : DescentCompat D V (-s) (-t) := by
  rw [descentCompat_iff] at *
  intro Y y₁ y₂ h O h₁ h₂
  rw [pullbackRestrict_neg, pullbackRestrict_neg, map_neg, hs y₁ y₂ h O h₁ h₂]

lemma smul (hs : DescentCompat D V s t) (r : Γ(S, V)) :
    DescentCompat D V ((f a).app V r • s) ((f b).app V r • t) := by
  rw [descentCompat_iff] at *
  intro Y y₁ y₂ h O h₁ h₂
  rw [pullbackRestrict_smul, pullbackRestrict_smul, Hom.app_smul, hs y₁ y₂ h O h₁ h₂,
    presheaf_map_app_app_eq h h₁ h₂ r]

lemma map (hs : DescentCompat D V s t) {V' : S.Opens} (i : V' ⟶ V) :
    DescentCompat D V'
      ((descentObj D a).presheaf.map (homOfLE ((f a).preimage_mono i.le)).op s)
      ((descentObj D b).presheaf.map (homOfLE ((f b).preimage_mono i.le)).op t) := by
  rw [descentCompat_iff] at *
  intro Y y₁ y₂ h O h₁ h₂
  rw [pullbackRestrict_presheaf_map, pullbackRestrict_presheaf_map, hs y₁ y₂ h O _ _]

end DescentCompat

/-- The compatible families of sections of `D` over `V`. -/
def descentSections (V : S.Opens) :
    AddSubgroup (∀ a, Γ(descentObj D a, f a ⁻¹ᵁ V)) where
  carrier := {s | ∀ a b, DescentCompat D V (s a) (s b)}
  add_mem' hs ht a b := (hs a b).add (ht a b)
  zero_mem' _ _ := DescentCompat.zero
  neg_mem' hs a b := (hs a b).neg

variable {D} in
@[ext]
lemma descentSections.ext {V : S.Opens} {s t : descentSections D V}
    (h : ∀ a, s.1 a = t.1 a) : s = t :=
  Subtype.ext (funext h)

noncomputable instance (V : S.Opens) : SMul Γ(S, V) (descentSections D V) where
  smul r s := ⟨fun a ↦ (f a).app V r • s.1 a, fun a b ↦ (s.2 a b).smul r⟩

variable {D} in
@[simp]
lemma descentSections.smul_apply {V : S.Opens} (r : Γ(S, V)) (s : descentSections D V) (a : J) :
    (r • s).1 a = (f a).app V r • s.1 a :=
  rfl

noncomputable instance (V : S.Opens) : Module Γ(S, V) (descentSections D V) where
  one_smul s := by ext; simp
  mul_smul r r' s := by ext; simp [mul_smul]
  smul_zero r := by ext; simp
  smul_add r s s' := by ext; simp
  add_smul r r' s := by ext; simp [add_smul]
  zero_smul s := by ext; simp

/-- The presheaf of abelian groups underlying `descentGlue D`. -/
noncomputable def descentPresheaf : S.Opensᵒᵖ ⥤ Ab.{u} where
  obj V := AddCommGrpCat.of (descentSections D V.unop)
  map {V V'} i := AddCommGrpCat.ofHom
    { toFun s := ⟨fun a ↦ (descentObj D a).presheaf.map
          (homOfLE ((f a).preimage_mono i.unop.le)).op (s.1 a),
        fun a b ↦ (s.2 a b).map i.unop⟩
      map_zero' := by
        ext
        simp
      map_add' _ _ := by
        ext
        simp }
  map_id V := by
    ext s a
    exact presheaf_map_id_apply _ _
  map_comp i j := by
    ext s a
    exact (presheaf_map_map_apply _ _ _).symm

noncomputable instance (V : S.Opensᵒᵖ) :
    Module (S.ringCatSheaf.obj.obj V) ((descentPresheaf D).obj V) :=
  inferInstanceAs (Module Γ(S, V.unop) (descentSections D V.unop))

lemma descentPresheaf_map_smul {V V' : S.Opensᵒᵖ} (i : V ⟶ V')
    (r : S.ringCatSheaf.obj.obj V) (s : (descentPresheaf D).obj V) :
    (descentPresheaf D).map i (r • s) =
      S.ringCatSheaf.obj.map i r • (descentPresheaf D).map i s := by
  refine descentSections.ext fun a ↦ ?_
  have e := congr($((f a).naturality i) r)
  exact (map_smul _ _ _ _).trans (congrArg (· • _) e.symm)

lemma isSheaf_descentPresheaf : TopCat.Presheaf.IsSheaf (descentPresheaf D) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hc (a : J) : TopCat.Presheaf.IsCompatible (descentObj D a).presheaf
      (fun i ↦ f a ⁻¹ᵁ U i) (fun i ↦ (sf i).1 a) :=
    fun i j ↦ congr_arg (fun s : descentSections D (U i ⊓ U j) ↦ s.1 a) (hsf i j)
  choose t ht htu using fun a ↦ TopCat.Sheaf.existsUnique_gluing'
    ⟨(descentObj D a).presheaf, (descentObj D a).isSheaf⟩ (fun i ↦ f a ⁻¹ᵁ U i)
    (f a ⁻¹ᵁ iSup U) (fun i ↦ homOfLE ((f a).preimage_mono (le_iSup U i)))
    ((f a).preimage_iSup U).le _ (hc a)
  have hmem (a b : J) : DescentCompat D (iSup U) (t a) (t b) := by
    rw [descentCompat_iff]
    intro Y y₁ y₂ h O h₁ h₂
    refine TopCat.Sheaf.eq_of_locally_eq'
      ⟨((pullback y₂).obj (descentObj D b)).presheaf, isSheaf _⟩
      (fun i ↦ O ⊓ y₁ ⁻¹ᵁ f a ⁻¹ᵁ U i) O (fun i ↦ homOfLE inf_le_left) ?_ _ _ fun i ↦ ?_
    · intro x hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (h₁ hx)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
    · have hA : O ⊓ y₁ ⁻¹ᵁ f a ⁻¹ᵁ U i ≤ y₁ ⁻¹ᵁ f a ⁻¹ᵁ U i := inf_le_right
      have hB : O ⊓ y₁ ⁻¹ᵁ f a ⁻¹ᵁ U i ≤ y₂ ⁻¹ᵁ f b ⁻¹ᵁ U i :=
        inf_le_right.trans (preimage_preimage_eq_of_comp_eq h (U i)).le
      have ea : pullbackRestrict y₁ _ (inf_le_left.trans h₁) (t a) =
          pullbackRestrict y₁ _ hA ((sf i).1 a) := by
        rw [← ht a i, pullbackRestrict_presheaf_map]
      have eb : pullbackRestrict y₂ _ (inf_le_left.trans h₂) (t b) =
          pullbackRestrict y₂ _ hB ((sf i).1 b) := by
        rw [← ht b i, pullbackRestrict_presheaf_map]
      refine (Hom.app_presheaf_map (descentHom D (y₁ ≫ f a) y₁ y₂ rfl h.symm) _ _).symm.trans ?_
      rw [presheaf_map_pullbackRestrict, presheaf_map_pullbackRestrict, ea, eb]
      exact (sf i).2 a b y₁ y₂ h _ hA hB
  refine ⟨⟨t, hmem⟩, fun i ↦ descentSections.ext fun a ↦ ht a i,
    fun s hs ↦ descentSections.ext fun a ↦ htu a _ fun i ↦ ?_⟩
  exact congr_arg (fun s : descentSections D (U i) ↦ s.1 a) (hs i)

/-- The `𝒪_S`-module of compatible families of sections of a descent datum `D`. -/
noncomputable def descentGlue (D : modulesPseudofunctor.DescentData f) : S.Modules where
  val := PresheafOfModules.ofPresheaf (descentPresheaf D)
    fun _ _ i r s ↦ descentPresheaf_map_smul D i r s
  isSheaf := isSheaf_descentPresheaf D

/-- The component at `a` of a section of `descentGlue D`. -/
noncomputable def glueVal {V : S.Opens} (a : J) :
    Γ(descentGlue D, V) →+ Γ(descentObj D a, f a ⁻¹ᵁ V) :=
  (Pi.evalAddMonoidHom (fun a ↦ Γ(descentObj D a, f a ⁻¹ᵁ V)) a).comp
    (descentSections D V).subtype

variable {D}

lemma glueVal_compat {V : S.Opens} (s : Γ(descentGlue D, V)) (a b : J) :
    DescentCompat D V (glueVal D a s) (glueVal D b s) :=
  s.2 a b

lemma glueVal_ext {V : S.Opens} {s t : Γ(descentGlue D, V)}
    (h : ∀ a, glueVal D a s = glueVal D a t) : s = t :=
  Subtype.ext (funext h)

/-- Every compatible family of sections is a section of `descentGlue D`. -/
lemma exists_glueVal_eq {V : S.Opens} (s : ∀ a, Γ(descentObj D a, f a ⁻¹ᵁ V))
    (hs : ∀ a b, DescentCompat D V (s a) (s b)) :
    ∃ t : Γ(descentGlue D, V), ∀ a, glueVal D a t = s a :=
  ⟨⟨s, hs⟩, fun _ ↦ rfl⟩

lemma glueVal_smul {V : S.Opens} (r : Γ(S, V)) (s : Γ(descentGlue D, V)) (a : J) :
    glueVal D a (r • s) = (f a).app V r • glueVal D a s :=
  rfl

lemma glueVal_presheaf_map {V V' : S.Opens} (i : V' ⟶ V) (s : Γ(descentGlue D, V)) (a : J) :
    glueVal D a ((descentGlue D).presheaf.map i.op s) =
      (descentObj D a).presheaf.map (homOfLE ((f a).preimage_mono i.le)).op
        (glueVal D a s) :=
  rfl

/-- Naturality of `pullbackRestrict` in the module. -/
lemma pullback_map_app_pullbackRestrict {X Y : Scheme.{u}} (y : Y ⟶ X) {M N : X.Modules}
    (φ : M ⟶ N) {V : X.Opens} {O : Y.Opens} (h : O ≤ y ⁻¹ᵁ V) (s : Γ(M, V)) :
    ((pullback y).map φ).app O (pullbackRestrict y M h s) = pullbackRestrict y N h (φ.app V s) := by
  rw [pullbackRestrict, pullbackRestrict, Hom.app_presheaf_map]
  exact congrArg _ (pullbackUnit_naturality_apply y φ V s)

/-- The inverse of `pullbackCompOfEq` on the image of the unit, for an arbitrary factorization
`g ≫ f = fg`. -/
lemma pullbackCompOfEq_inv_app_pullbackUnitApp {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
    (fg : Z ⟶ X) (h : g ≫ f = fg) (M : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    ((pullbackCompOfEq g f fg h M).inv).app (fg ⁻¹ᵁ U) (pullbackUnitApp fg M U m) =
      pullbackRestrict g ((pullback f).obj M) (congrArg (fun k ↦ k ⁻¹ᵁ U) h.symm).le
        (pullbackUnitApp f M U m) := by
  subst h
  exact (pullbackCompOfEq_inv_app_pullbackUnit g f M U m).trans (presheaf_map_id_apply _ _).symm

/-- `pullbackRestrict` of a section in the image of the unit, in terms of `pullbackCompOfEq`. -/
lemma pullbackRestrict_pullbackUnitApp {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
    (fg : Z ⟶ X) (h : g ≫ f = fg) (M : X.Modules) {U : X.Opens} {O : Z.Opens}
    (h₁ : O ≤ g ⁻¹ᵁ f ⁻¹ᵁ U) (h₁' : O ≤ fg ⁻¹ᵁ U) (m : Γ(M, U)) :
    pullbackRestrict g ((pullback f).obj M) h₁ (pullbackUnitApp f M U m) =
      ((pullbackCompOfEq g f fg h M).inv).app O
        (((pullback fg).obj M).presheaf.map (homOfLE h₁').op (pullbackUnitApp fg M U m)) := by
  rw [Hom.app_presheaf_map, pullbackCompOfEq_inv_app_pullbackUnitApp,
    presheaf_map_pullbackRestrict]

variable (D) in
/-- The projection `descentGlue D ⟶ (f a)_* (D a)` to the `a`-th component. -/
noncomputable def glueProj (a : J) : descentGlue D ⟶ (pushforward (f a)).obj (descentObj D a) :=
  ⟨PresheafOfModules.homMk
    { app _ := AddCommGrpCat.ofHom (glueVal D a)
      naturality _ _ _ := rfl }
    fun _ _ _ ↦ rfl⟩

lemma glueProj_app (a : J) {V : S.Opens} (s : Γ(descentGlue D, V)) :
    (glueProj D a).app V s = glueVal D a s :=
  rfl

variable (D) in
/-- The counit `(f a)^* (descentGlue D) ⟶ D a`, adjoint to the projection to the `a`-th
component. -/
noncomputable def glueCounit (a : J) :
    (pullback (f a)).obj (descentGlue D) ⟶ descentObj D a :=
  ((pullbackPushforwardAdjunction (f a)).homEquiv _ _).symm (glueProj D a)

lemma glueCounit_app_pullbackUnitApp (a : J) {V : S.Opens} (s : Γ(descentGlue D, V)) :
    (glueCounit D a).app (f a ⁻¹ᵁ V) (pullbackUnitApp (f a) _ V s) = glueVal D a s := by
  have e := congr(Hom.app
    $(((pullbackPushforwardAdjunction (f a)).homEquiv _ _).apply_symm_apply (glueProj D a)) V s)
  rw [Adjunction.homEquiv_unit, Hom.comp_app, ConcreteCategory.comp_apply,
    pushforward_map_app] at e
  exact e

/-- The counits of `descentGlue D` are compatible with the descent data. -/
lemma pullback_map_glueCounit_comp_hom {Y : Scheme.{u}} (q : Y ⟶ S) {a b : J} (f₁ : Y ⟶ W a)
    (f₂ : Y ⟶ W b) (hf₁ : f₁ ≫ f a = q) (hf₂ : f₂ ≫ f b = q) :
    (pullback f₁).map (glueCounit D a) ≫ descentHom D q f₁ f₂ hf₁ hf₂ =
      (pullbackCompOfEq f₁ (f a) q hf₁ _).hom ≫ (pullbackCompOfEq f₂ (f b) q hf₂ _).inv ≫
        (pullback f₂).map (glueCounit D b) := by
  subst hf₁
  rw [← cancel_epi (pullbackCompOfEq f₁ (f a) _ rfl _).inv, Iso.inv_hom_id_assoc]
  refine pullback_hom_ext (f₁ ≫ f a) fun V m ↦ ?_
  have k := (descentCompat_iff D V _ _).1 (glueVal_compat m a b) f₁ f₂ hf₂.symm
    ((f₁ ≫ f a) ⁻¹ᵁ V) le_rfl (preimage_preimage_eq_of_comp_eq hf₂.symm V).le
  rw [← glueCounit_app_pullbackUnitApp, ← glueCounit_app_pullbackUnitApp,
    ← pullback_map_app_pullbackRestrict, ← pullback_map_app_pullbackRestrict,
    ← pullbackCompOfEq_inv_app_pullbackUnitApp f₁ (f a) _ rfl,
    ← pullbackCompOfEq_inv_app_pullbackUnitApp f₂ (f b) (f₁ ≫ f a) hf₂] at k
  rw [Hom.comp_app, Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact k

variable (D) in
/-- The counits `(f a)^* (descentGlue D) ⟶ D a` form a morphism of descent data. -/
noncomputable def glueToDescentData :
    (modulesPseudofunctor.toDescentData f).obj (descentGlue D) ⟶ D where
  hom a := glueCounit D a
  comm Y q a b f₁ f₂ hf₁ hf₂ := by
    rw [modulesPseudofunctor_toDescentData_obj_hom f (descentGlue D) q f₁ f₂ hf₁ hf₂,
      Category.assoc]
    exact pullback_map_glueCounit_comp_hom q f₁ f₂ hf₁ hf₂

lemma glueToDescentData_hom (a : J) : (glueToDescentData D).hom a = glueCounit D a :=
  rfl

/-- Sections `ψ a (f a ^* p)` are compatible if the morphisms `ψ a : (f a)^* P ⟶ D a` are
compatible with the descent data. -/
lemma descentCompat_app_pullbackUnitApp {P : S.Modules}
    (ψ : ∀ a, (pullback (f a)).obj P ⟶ descentObj D a) {a b : J}
    (hψ : ∀ ⦃Y : Scheme.{u}⦄ (y₁ : Y ⟶ W a) (y₂ : Y ⟶ W b) (h : y₁ ≫ f a = y₂ ≫ f b),
      (pullbackCompOfEq y₁ (f a) _ rfl P).inv ≫ (pullback y₁).map (ψ a) ≫
        descentHom D (y₁ ≫ f a) y₁ y₂ rfl h.symm =
      (pullbackCompOfEq y₂ (f b) _ h.symm P).inv ≫ (pullback y₂).map (ψ b))
    {V : S.Opens} (p : Γ(P, V)) :
    DescentCompat D V ((ψ a).app _ (pullbackUnitApp (f a) P V p))
      ((ψ b).app _ (pullbackUnitApp (f b) P V p)) := by
  rw [descentCompat_iff]
  intro Y y₁ y₂ h O h₁ h₂
  have h₁' : O ≤ (y₁ ≫ f a) ⁻¹ᵁ V := h₁
  have k := congr(Hom.app $(hψ y₁ y₂ h) O
    (((pullback (y₁ ≫ f a)).obj P).presheaf.map (homOfLE h₁').op
      (pullbackUnitApp (y₁ ≫ f a) P V p)))
  rw [Hom.comp_app, Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← pullbackRestrict_pullbackUnitApp y₁ (f a) _ rfl P h₁ h₁',
    ← pullbackRestrict_pullbackUnitApp y₂ (f b) _ h.symm P h₂ h₁',
    pullback_map_app_pullbackRestrict, pullback_map_app_pullbackRestrict] at k
  exact k

/-- The sections `φ a (f a ^* p)` attached to a morphism of descent data
`φ : (toDescentData f).obj P ⟶ D` are compatible. -/
lemma descentCompat_hom_app_pullbackUnitApp {P : S.Modules}
    (φ : (modulesPseudofunctor.toDescentData f).obj P ⟶ D) {V : S.Opens} (p : Γ(P, V))
    (a b : J) :
    DescentCompat D V ((φ.hom a).app _ (pullbackUnitApp (f a) P V p))
      ((φ.hom b).app _ (pullbackUnitApp (f b) P V p)) := by
  refine descentCompat_app_pullbackUnitApp (P := P) φ.hom (fun Y y₁ y₂ h ↦ ?_) p
  have hc := φ.comm (y₁ ≫ f a) y₁ y₂ rfl h.symm
  rw [modulesPseudofunctor_toDescentData_obj_hom] at hc
  calc _ = (pullbackCompOfEq y₁ (f a) _ rfl P).inv ≫ ((pullbackCompOfEq y₁ (f a) _ rfl P).hom ≫
        (pullbackCompOfEq y₂ (f b) _ h.symm P).inv) ≫ (pullback y₂).map (φ.hom b) :=
      congrArg ((pullbackCompOfEq y₁ (f a) _ rfl P).inv ≫ ·) hc
    _ = _ := by
      simp
      rfl

/-- The sections of `descentGlue D` attached to a morphism of descent data
`φ : (toDescentData f).obj P ⟶ D`. -/
noncomputable def toGlueSections {P : S.Modules}
    (φ : (modulesPseudofunctor.toDescentData f).obj P ⟶ D) (V : S.Opens) :
    Γ(P, V) →+ Γ(descentGlue D, V) where
  toFun p :=⟨fun a ↦ (φ.hom a).app _ (pullbackUnitApp (f a) P V p),
    fun a b ↦ descentCompat_hom_app_pullbackUnitApp φ p a b⟩
  map_zero' := glueVal_ext fun a ↦ by
    simp [glueVal]
    rfl
  map_add' _ _ := glueVal_ext fun a ↦ by
    simp [glueVal]
    rfl

lemma glueVal_toGlueSections {P : S.Modules}
    (φ : (modulesPseudofunctor.toDescentData f).obj P ⟶ D) {V : S.Opens} (p : Γ(P, V)) (a : J) :
    glueVal D a (toGlueSections φ V p) = (φ.hom a).app _ (pullbackUnitApp (f a) P V p) :=
  rfl

lemma toGlueSections_presheaf_map {P : S.Modules}
    (φ : (modulesPseudofunctor.toDescentData f).obj P ⟶ D) {V V' : S.Opens} (i : V' ⟶ V)
    (p : Γ(P, V)) :
    toGlueSections φ V' (P.presheaf.map i.op p) =
      (descentGlue D).presheaf.map i.op (toGlueSections φ V p) := by
  refine glueVal_ext fun a ↦ ?_
  rw [glueVal_presheaf_map, glueVal_toGlueSections, glueVal_toGlueSections,
    pullbackUnitApp_presheaf_map]
  exact Hom.app_presheaf_map (φ.hom a) _ _

lemma toGlueSections_smul {P : S.Modules}
    (φ : (modulesPseudofunctor.toDescentData f).obj P ⟶ D) {V : S.Opens} (r : Γ(S, V))
    (p : Γ(P, V)) :
    toGlueSections φ V (r • p) = r • toGlueSections φ V p := by
  refine glueVal_ext fun a ↦ ?_
  rw [glueVal_smul, glueVal_toGlueSections, glueVal_toGlueSections, pullbackUnitApp_smul,
    Hom.app_smul]

/-- The morphism `P ⟶ descentGlue D` induced by a morphism of descent data
`φ : (toDescentData f).obj P ⟶ D`: a section `p` is sent to the family `φ a (f a ^* p)`. -/
noncomputable def toGlue {P : S.Modules}
    (φ : (modulesPseudofunctor.toDescentData f).obj P ⟶ D) : P ⟶ descentGlue D :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom (toGlueSections φ V.unop)
      naturality V V' i := by
        ext p
        exact toGlueSections_presheaf_map φ i.unop p }
    fun V r p ↦ toGlueSections_smul φ r p⟩

lemma glueVal_toGlue_app {P : S.Modules} (φ : (modulesPseudofunctor.toDescentData f).obj P ⟶ D)
    {V : S.Opens} (p : Γ(P, V)) (a : J) :
    glueVal D a ((toGlue φ).app V p) = (φ.hom a).app _ (pullbackUnitApp (f a) P V p) :=
  rfl

lemma pullback_map_toGlue_comp_glueCounit {P : S.Modules}
    (φ : (modulesPseudofunctor.toDescentData f).obj P ⟶ D) (a : J) :
    (pullback (f a)).map (toGlue φ) ≫ glueCounit D a = φ.hom a := by
  refine pullback_hom_ext (f a) fun V p ↦ ?_
  rw [Hom.comp_app, ConcreteCategory.comp_apply, pullbackUnit_naturality_apply]
  exact glueCounit_app_pullbackUnitApp a _

end AlgebraicGeometry.Scheme.Modules
