import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import Jacobian.AlgebraicGeometry.Picard.NormalizedDescent.Basic
import Jacobian.AlgebraicGeometry.Picard.Normalized

/-!
# Descent data from normalized transition maps

Unique normalized transition maps satisfy the identity and cocycle conditions on double and triple overlaps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

open Scheme

section ChosenPullbacks

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The fibre product of `X_A ⟶ X_C ⟵ X_B` for morphisms `u : A ⟶ C`, `v : B ⟶ C` of schemes
over `S`, chosen to be `X_{A ×_C B}`. -/
noncomputable abbrev chosenPullbackBaseChangeMap {A B C : Over S} (u : A ⟶ C) (v : B ⟶ C) :
    ChosenPullback (baseChangeMap f u) (baseChangeMap f v) where
  pullback := pullback f (pullback u v).hom
  p₁ := baseChangeMap f (pullback.fst u v)
  p₂ := baseChangeMap f (pullback.snd u v)
  condition := (isPullback_baseChangeMap_of_isPullback f
    ((IsPullback.of_hasPullback u v).map (Over.forget S))).w
  isLimit := (isPullback_baseChangeMap_of_isPullback f
    ((IsPullback.of_hasPullback u v).map (Over.forget S))).isLimit

variable {T : Over S} {ι : Type*} {T' : ι → Over S} (g : ∀ i, T' i ⟶ T)

/-- The triple fibre products `X_{T i ×_T T j ×_T T k}`. -/
noncomputable abbrev chosenPullback₃BaseChangeMap (i j k : ι) :
    ChosenPullback₃ (chosenPullbackBaseChangeMap f (g i) (g j))
      (chosenPullbackBaseChangeMap f (g j) (g k)) (chosenPullbackBaseChangeMap f (g i) (g k)) where
  chosenPullback := chosenPullbackBaseChangeMap f (pullback.snd (g i) (g j))
    (pullback.fst (g j) (g k))
  l :=
    { f := baseChangeMap f (pullback.lift (pullback.fst _ _ ≫ pullback.fst (g i) (g j))
        (pullback.snd _ _ ≫ pullback.snd (g j) (g k)) (by
          simp [pullback.condition, pullback.condition_assoc]))
      f_p₁ := by
        simp only [chosenPullbackBaseChangeMap, ← baseChangeMap_comp, pullback.lift_fst]
      f_p₂ := by
        simp only [chosenPullbackBaseChangeMap, ← baseChangeMap_comp, pullback.lift_snd]
      f_p := by
        simp only [chosenPullbackBaseChangeMap, ← baseChangeMap_comp, pullback.lift_fst_assoc,
          Category.assoc] }

end ChosenPullbacks

section DescentDatum

variable {F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1}} {X S : Scheme.{u}}
  {f : X ⟶ S} {s : ∀ Y : Over S, Y.left ⟶ pullback f Y.hom}
  (hsb : ∀ {Y Z : Over S} (w : Y ⟶ Z), s Y ≫ baseChangeMap f w = w.left ≫ s Z)
  {T : Over S} {ι : Type*} {T' : ι → Over S} {g : ∀ i, T' i ⟶ T}
  {N : F.obj (.mk (op T.left))} {L : ∀ i, F.obj (.mk (op (pullback f (T' i).hom)))}
  {α : ∀ i, (F.map (s (T' i)).op.toLoc).toFunctor.obj (L i) ≅
    (F.map (g i).left.op.toLoc).toFunctor.obj N}
  (hrigid : ∀ {Y : Over S} {i j : ι} {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom} {t₁ : Y.left ⟶ (T' i).left}
    {t₂ : Y.left ⟶ (T' j).left} {q : Y.left ⟶ T.left}
    {h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)} {h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j)}
    {hq₁ : t₁ ≫ (g i).left = q} {hq₂ : t₂ ≫ (g j).left = q}
    {φ ψ : (F.map v₁.op.toLoc).toFunctor.obj (L i) ⟶ (F.map v₂.op.toLoc).toFunctor.obj (L j)},
    IsIso ψ → IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ φ →
      IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ ψ → φ = ψ)
  (hom : ∀ i j,
    (F.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₁.op.toLoc).toFunctor.obj (L i) ⟶
      (F.map (chosenPullbackBaseChangeMap f (g i) (g j)).p₂.op.toLoc).toFunctor.obj (L j))
  [hiso : ∀ i j, IsIso (hom i j)]
  (hhom : ∀ i j, IsSectionNormalized s g α (hsb (pullback.fst (g i) (g j)))
      (hsb (pullback.snd (g i) (g j))) (q := (pullback.fst (g i) (g j) ≫ g i).left) rfl
      (by rw [← Over.comp_left, ← pullback.condition]) (hom i j))

omit hiso in
include hhom in
/-- The pullbacks of normalized gluing morphisms to fibre products are normalized. -/
lemma isSectionNormalized_pullHom {i j : ι} {Y : Over S}
    (w : Y ⟶ pullback (g i) (g j)) {v₁ : pullback f Y.hom ⟶ pullback f (T' i).hom}
    {v₂ : pullback f Y.hom ⟶ pullback f (T' j).hom}
    (hv₁ : baseChangeMap f w ≫ (chosenPullbackBaseChangeMap f (g i) (g j)).p₁ = v₁)
    (hv₂ : baseChangeMap f w ≫ (chosenPullbackBaseChangeMap f (g i) (g j)).p₂ = v₂)
    {t₁ : Y.left ⟶ (T' i).left} {t₂ : Y.left ⟶ (T' j).left} {q : Y.left ⟶ T.left}
    (ht₁ : (w ≫ pullback.fst (g i) (g j)).left = t₁)
    (ht₂ : (w ≫ pullback.snd (g i) (g j)).left = t₂)
    (hq : (w ≫ pullback.fst (g i) (g j) ≫ g i).left = q)
    (h₁ : s Y ≫ v₁ = t₁ ≫ s (T' i)) (h₂ : s Y ≫ v₂ = t₂ ≫ s (T' j))
    (hq₁ : t₁ ≫ (g i).left = q) (hq₂ : t₂ ≫ (g j).left = q) :
    IsSectionNormalized s g α h₁ h₂ hq₁ hq₂ (pullHom (hom i j) (baseChangeMap f w) v₁ v₂ hv₁ hv₂) :=
  ((hhom i j).pullHom w (baseChangeMap f w) (hsb w) hv₁ hv₂
    (by rw [← hv₁, ← Category.assoc, hsb, Category.assoc, hsb, Category.assoc])
    (by rw [← hv₂, ← Category.assoc, hsb, Category.assoc, hsb, Category.assoc]) rfl
    (by rw [Category.assoc, ← Over.comp_left, ← pullback.condition])).congr ht₁ ht₂ hq

include hrigid hhom in
/-- The descent datum given by normalized gluing isomorphisms: the cocycle condition holds by
rigidity. -/
noncomputable def descentDataOfIsSectionNormalized :
    F.DescentData' (fun i j ↦ chosenPullbackBaseChangeMap f (g i) (g j))
      (fun i j k ↦ chosenPullback₃BaseChangeMap f g i j k) where
  obj := L
  hom := hom
  pullHom'_hom_self i := by
    let Δ : T' i ⟶ pullback (g i) (g i) := pullback.lift (𝟙 _) (𝟙 _) rfl
    rw [Pseudofunctor.DescentData'.pullHom'_eq_pullHom _ _ _ _ (baseChangeMap f Δ) (by simp)
      (by simp) (by simp [← baseChangeMap_comp, Δ]) (by simp [← baseChangeMap_comp, Δ])]
    exact hrigid inferInstance
      (isSectionNormalized_pullHom hsb hom hhom Δ _ _ (t₁ := 𝟙 _) (t₂ := 𝟙 _)
        (q := (g i).left) (by simp [Δ]) (by simp [Δ]) (by simp [Δ]) (by simp) (by simp)
        (by simp) (by simp))
      isSectionNormalized_id
  pullHom'_hom_comp i j k := by
    rw [Pseudofunctor.DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃,
      Pseudofunctor.DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃,
      Pseudofunctor.DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃]
    let a : pullback (pullback.snd (g i) (g j)) (pullback.fst (g j) (g k)) ⟶
      pullback (g i) (g j) := pullback.fst _ _
    let b : pullback (pullback.snd (g i) (g j)) (pullback.fst (g j) (g k)) ⟶
      pullback (g j) (g k) := pullback.snd _ _
    let c : pullback (pullback.snd (g i) (g j)) (pullback.fst (g j) (g k)) ⟶
      pullback (g i) (g k) := pullback.lift (a ≫ pullback.fst _ _) (b ≫ pullback.snd _ _)
        (by simp [a, b, pullback.condition, pullback.condition_assoc])
    have e₂ : (b ≫ pullback.fst (g j) (g k)).left = (a ≫ pullback.snd (g i) (g j)).left :=
      congrArg CommaMorphism.left pullback.condition.symm
    have eq₂ : (b ≫ pullback.fst (g j) (g k) ≫ g j).left =
        (a ≫ pullback.fst (g i) (g j) ≫ g i).left := by
      refine congrArg CommaMorphism.left ?_
      rw [← Category.assoc, ← pullback.condition, Category.assoc, ← pullback.condition]
    have ec₁ : (c ≫ pullback.fst (g i) (g k)).left = (a ≫ pullback.fst (g i) (g j)).left := by
      simp [c]
    have ec₃ : (c ≫ pullback.snd (g i) (g k)).left = (b ≫ pullback.snd (g j) (g k)).left := by
      simp [c]
    have eqc : (c ≫ pullback.fst (g i) (g k) ≫ g i).left =
        (a ≫ pullback.fst (g i) (g j) ≫ g i).left := by
      simp [c]
    have h₁ : s _ ≫ (chosenPullback₃BaseChangeMap f g i j k).p₁ =
        (a ≫ pullback.fst (g i) (g j)).left ≫ s (T' i) := by
      change s _ ≫ baseChangeMap f a ≫ baseChangeMap f _ = _
      rw [← baseChangeMap_comp, hsb]
    have h₂ : s _ ≫ (chosenPullback₃BaseChangeMap f g i j k).p₂ =
        (a ≫ pullback.snd (g i) (g j)).left ≫ s (T' j) := by
      change s _ ≫ baseChangeMap f a ≫ baseChangeMap f _ = _
      rw [← baseChangeMap_comp, hsb]
    have h₃ : s _ ≫ (chosenPullback₃BaseChangeMap f g i j k).p₃ =
        (b ≫ pullback.snd (g j) (g k)).left ≫ s (T' k) := by
      change s _ ≫ baseChangeMap f b ≫ baseChangeMap f _ = _
      rw [← baseChangeMap_comp, hsb]
    have hq₂ : (a ≫ pullback.snd (g i) (g j)).left ≫ (g j).left =
        (a ≫ pullback.fst (g i) (g j) ≫ g i).left := by
      rw [← e₂, ← eq₂]
      rfl
    have hq₃ : (b ≫ pullback.snd (g j) (g k)).left ≫ (g k).left =
        (a ≫ pullback.fst (g i) (g j) ≫ g i).left := by
      rw [← eq₂, ← Over.comp_left, Category.assoc, ← pullback.condition]
    exact hrigid inferInstance
      ((isSectionNormalized_pullHom hsb hom hhom a _ _ rfl rfl rfl h₁ h₂ rfl hq₂).comp
        (isSectionNormalized_pullHom hsb hom hhom b _ _ e₂ rfl eq₂ h₂ h₃ hq₂ hq₃))
      (isSectionNormalized_pullHom hsb hom hhom c _ _ ec₁ ec₃ eqc h₁ h₃ rfl hq₃)

end DescentDatum

end AlgebraicGeometry
