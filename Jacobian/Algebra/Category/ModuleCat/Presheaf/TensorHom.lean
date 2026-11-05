import Jacobian.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit

/-!
# Tensor products and internal homs of presheaves

The canonical map `Hom(M, R) ⊗ N ⟶ Hom(M, N)` is natural in both arguments.
It is bijective on sections wherever the source is finite free or the
target is free of rank one.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory Limits Opposite

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (M P : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

section SumEvaluation

variable {D : Type*} [Category D] {S : Dᵒᵖ ⥤ RingCat.{u}}

private lemma sum_app_apply {M N : PresheafOfModules.{u} S} {ι : Type*} (t : Finset ι) (f : ι → (M ⟶ N))
    (X : Dᵒᵖ) (x : M.obj X) : (∑ i ∈ t, f i).app X x = ∑ i ∈ t, (f i).app X x :=
  map_sum ({ toFun f := f.app X x, map_zero' := rfl, map_add' _ _ := rfl } :
    (M ⟶ N) →+ N.obj X) f t

end SumEvaluation

private lemma app_unit_eq_smul {A : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} {U : C} (s : (restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj A)
    (W : (Over U)ᵒᵖ) (r : R.obj (op W.unop.left)) :
    s.app W r = r • (show A.obj (op W.unop.left) from
      A.map W.unop.hom.op (s.app (op (Over.mk (𝟙 U))) (1 : R.obj (op U)))) := by
  have h1 : s.app W (1 : R.obj (op W.unop.left)) =
      A.map W.unop.hom.op (s.app (op (Over.mk (𝟙 U))) (1 : R.obj (op U))) :=
    (congrArg (s.app W) (unit_map_one (R := R ⋙ forget₂ _ _) W.unop.hom.op).symm).trans
      (naturality_apply s
        (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 U)).op _)
  refine (congrArg (s.app W) (mul_one r).symm).trans ?_
  refine ((s.app W).hom.map_smul r (1 : R.obj (op W.unop.left))).trans ?_
  exact congrArg (fun y : A.obj (op W.unop.left) ↦ r • y) h1

private lemma restrictOverMap_sum {U : C} {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} {V : C} (g : V ⟶ U)
    {ι : Type*} (t : Finset ι) (f : ι → ((restrictOver R U).obj M ⟶ (restrictOver R U).obj N)) :
    restrictOverMap g (∑ i ∈ t, f i) = ∑ i ∈ t, restrictOverMap g (f i) :=
  map_sum ({ toFun := restrictOverMap g, map_zero' := rfl, map_add' _ _ := rfl } :
    ((restrictOver R U).obj M ⟶ (restrictOver R U).obj N) →+
      ((restrictOver R V).obj M ⟶ (restrictOver R V).obj N)) f t

/-- The morphism `Hom(M, R) ⊗ P ⟶ Hom(M, P)` of presheaves of modules, sending `φ ⊗ p` to
`m ↦ φ(m) • p`. -/
noncomputable def dualTensorHom : homObj M (unit _) ⊗ P ⟶ homObj M P :=
  tensorHomCurry ((α_ M (homObj M (unit _)) P).inv ≫ tensorHomUncurry (𝟙 _) ▷ P ≫ (λ_ P).hom)

/-- `Hom(M, R) ⊗ P ⟶ Hom(M, P)` sends `φ ⊗ p` to `m ↦ φ(m) • p`. -/
lemma dualTensorHom_app_tmul_app_apply {U : C} (φ : (homObj M (unit _)).obj (op U))
    (p : P.obj (op U)) (W : (Over U)ᵒᵖ) (m : M.obj (op W.unop.left)) :
    (((dualTensorHom M P).app (op U) (φ ⊗ₜ p)).app W) m =
      (show R.obj (op W.unop.left) from (φ.app W) m) • P.map W.unop.hom.op p := by
  refine (?_ : _ = (show R.obj (op W.unop.left) from
    (φ.app (op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom)))) m) • P.map W.unop.hom.op p).trans ?_
  · rfl
  · rw [restrictOver_hom_app_congr φ (Category.id_comp W.unop.hom) m]
    rfl

variable {M P} in
/-- The morphism `Hom(M, R) ⊗ P ⟶ Hom(M, P)` is bijective on sections over `U` if `P` is free of
rank one over `U`, with basis `p₀` and coordinate `φ₀`. -/
lemma dualTensorHom_app_bijective {U : C} (p₀ : P.obj (op U))
    (φ₀ : (restrictOver R U).obj P ⟶ (restrictOver R U).obj (unit _))
    (hφ₀ : ∀ (V : (Over U)ᵒᵖ) (r : R.obj (op V.unop.left)),
      (φ₀.app V) (r • P.map V.unop.hom.op p₀) = r)
    (hgen : ∀ (V : (Over U)ᵒᵖ) (x : P.obj (op V.unop.left)),
      ∃ r : R.obj (op V.unop.left), x = r • P.map V.unop.hom.op p₀) :
    Function.Bijective ((dualTensorHom M P).app (op U)) := by
  have hp₀ : ∀ p : P.obj (op U), ∃ r : (R ⋙ forget₂ CommRingCat RingCat).obj (op U),
      p = r • p₀ := fun p ↦ by
    obtain ⟨r, hr⟩ := hgen (op (Over.mk (𝟙 U))) p
    refine ⟨r, hr.trans (congrArg (fun q : P.obj (op U) ↦ r • q) ?_)⟩
    change P.map (𝟙 (op U)) p₀ = p₀
    rw [PresheafOfModules.map_id]
    rfl
  have key (t : ((homObj M (unit _)) ⊗ P).obj (op U)) :
      ∃ φ : (homObj M (unit _)).obj (op U), t = φ ⊗ₜ p₀ := by
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul φ p =>
      obtain ⟨a, rfl⟩ := hp₀ p
      exact ⟨a • φ, (TensorProduct.smul_tmul _ _ _).symm⟩
    | add t t' ht ht' =>
      obtain ⟨φ, rfl⟩ := ht
      obtain ⟨φ', rfl⟩ := ht'
      exact ⟨φ + φ', (TensorProduct.add_tmul _ _ _).symm⟩
  refine ⟨?_, fun ψ ↦ ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨φ, rfl⟩ := key t
    suffices hφ : φ = 0 by rw [hφ, TensorProduct.zero_tmul]
    refine hom_ext fun V ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
    have h := congrArg (fun ξ : (restrictOver R U).obj M ⟶ (restrictOver R U).obj P ↦
      φ₀.app V (ξ.app V m)) ht
    simp only at h
    rw [dualTensorHom_app_tmul_app_apply, hφ₀] at h
    exact h.trans (map_zero (φ₀.app V).hom)
  · refine ⟨(ψ ≫ φ₀) ⊗ₜ p₀, hom_ext fun V ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)⟩
    rw [dualTensorHom_app_tmul_app_apply]
    obtain ⟨r, hr⟩ := hgen V (ψ.app V m)
    change (φ₀.app V (ψ.app V m)) • _ = _
    rw [hr, hφ₀]

variable {M P} in
/-- **`Hom(M, R) ⊗ P ≅ Hom(M, P)` for `M` free of finite rank.** If `M|_U` is a finite direct sum
of copies of `R|_U`, with inclusions `s i` and projections `c i`, then `Hom(M, R) ⊗ P ⟶ Hom(M, P)`
is bijective on sections over `U`: both sides are `⨁ᵢ P(U)`, through `ψ ↦ (ψ(s i 1))ᵢ` and
`∑ᵢ c i ⊗ pᵢ ↤ (pᵢ)ᵢ`. -/
lemma dualTensorHom_app_bijective_of_free {U : C} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ((restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj M))
    (c : ι → ((restrictOver R U).obj M ⟶ (restrictOver R U).obj (unit _)))
    (hsc : ∀ i j, s j ≫ c i = if j = i then 𝟙 _ else 0)
    (htot : ∑ i, c i ≫ s i = 𝟙 _) :
    Function.Bijective ((dualTensorHom M P).app (op U)) := by
  let T : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let m : ι → M.obj (op U) := fun i ↦ (s i).app T (1 : R.obj (op U))
  have hspan (W : (Over U)ᵒᵖ) (x : M.obj (op W.unop.left)) :
      x = ∑ i, (show R.obj (op W.unop.left) from (c i).app W x) •
        (show M.obj (op W.unop.left) from M.map W.unop.hom.op (m i)) := by
    have h : ∑ i, (c i ≫ s i).app W x = x :=
      (sum_app_apply Finset.univ (fun i ↦ c i ≫ s i) W x).symm.trans
        (congrArg (fun f ↦ f.app W x) htot)
    exact h.symm.trans (Finset.sum_congr rfl fun i _ ↦ app_unit_eq_smul (s i) W _)
  have hcm (i j : ι) : (c i).app T (m j) = if j = i then (1 : R.obj (op U)) else 0 := by
    have h := congrArg (fun f ↦ f.app T (1 : R.obj (op U))) (hsc i j)
    refine h.trans ?_
    split_ifs <;> rfl
  have hval {Q : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
      (ψ : (restrictOver R U).obj M ⟶ (restrictOver R U).obj Q) (W : (Over U)ᵒᵖ)
      (x : M.obj (op W.unop.left)) :
      ψ.app W x = ∑ i, (show R.obj (op W.unop.left) from (c i).app W x) •
        (show Q.obj (op W.unop.left) from Q.map W.unop.hom.op (ψ.app T (m i))) := by
    refine (congrArg (ψ.app W) (hspan W x)).trans ?_
    refine (map_sum (ψ.app W).hom _ _).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    refine ((ψ.app W).hom.map_smul _ _).trans (congrArg (_ • ·) ?_)
    exact naturality_apply ψ
      (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 U)).op (m i)
  let c' : ι → (homObj M (unit _)).obj (op U) := c
  let a (φ : (homObj M (unit _)).obj (op U)) (i : ι) :
      (R ⋙ forget₂ CommRingCat RingCat).obj (op U) :=
    (show R.obj (op U) from φ.app T (m i))
  have hdual (φ : (homObj M (unit _)).obj (op U)) : φ = ∑ i, a φ i • c' i := by
    refine hom_ext (M₁ := (restrictOver R U).obj M) (M₂ := (restrictOver R U).obj (unit _))
      fun W ↦ ?_
    ext y
    refine (hval φ W y).trans ?_
    refine Eq.trans ?_ (sum_app_apply _ _ W y).symm
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    refine Eq.trans ?_ (restrictOver_smul_app_apply _ (c i) W y).symm
    change (show R.obj (op W.unop.left) from (c i).app W y) *
        (show R.obj (op W.unop.left) from R.map W.unop.hom.op (φ.app T (m i))) =
      R.map W.unop.hom.op (φ.app T (m i)) * (show R.obj (op W.unop.left) from (c i).app W y)
    exact mul_comm _ _
  have key (t : ((homObj M (unit _)) ⊗ P).obj (op U)) :
      ∃ p : ι → P.obj (op U), t = ∑ i, c' i ⊗ₜ p i := by
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul φ q =>
      refine ⟨fun i ↦ a φ i • q, ?_⟩
      conv_lhs => rw [hdual φ]
      rw [TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun i _ ↦ TensorProduct.smul_tmul _ _ _
    | add t t' ht ht' =>
      obtain ⟨p, rfl⟩ := ht
      obtain ⟨p', rfl⟩ := ht'
      exact ⟨p + p', by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩
  have hsingle (i j : ι) (p : P.obj (op U)) :
      ((dualTensorHom M P).app (op U) (c' i ⊗ₜ p)).app T (m j) = if j = i then p else 0 := by
    rw [dualTensorHom_app_tmul_app_apply, hcm]
    split_ifs
    · exact (one_smul _ _).trans (P.map_id_apply' p)
    · exact zero_smul _ _
  have himage (p : ι → P.obj (op U)) (j : ι) :
      ((dualTensorHom M P).app (op U) (∑ i, c' i ⊗ₜ p i)).app T (m j) = p j := by
    rw [map_sum, sum_app_apply]
    simp only [hsingle]
    simp
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨p, rfl⟩ := key t
    have hp (j : ι) : p j = 0 := by
      rw [← himage p j, ht]
      rfl
    simp [hp]
  · intro ψ
    refine ⟨∑ i, c' i ⊗ₜ ψ.app T (m i), ?_⟩
    refine hom_ext (M₁ := (restrictOver R U).obj M) (M₂ := (restrictOver R U).obj P)
      fun W ↦ ?_
    ext x
    rw [map_sum, sum_app_apply, hval ψ W x]
    exact Finset.sum_congr rfl fun i _ ↦ dualTensorHom_app_tmul_app_apply M P _ _ W x

variable {M P} in
/-- If `M` is free of finite rank on `U`, then `Hom(M, R) ⊗ P ⟶ Hom(M, P)` is bijective on
sections over every `V ⟶ U`. -/
lemma dualTensorHom_app_bijective_of_hom {U : C} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ((restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj M))
    (c : ι → ((restrictOver R U).obj M ⟶ (restrictOver R U).obj (unit _)))
    (hsc : ∀ i j, s j ≫ c i = if j = i then 𝟙 _ else 0)
    (htot : ∑ i, c i ≫ s i = 𝟙 _) {V : C} (g : V ⟶ U) :
    Function.Bijective ((dualTensorHom M P).app (op V)) := by
  refine dualTensorHom_app_bijective_of_free (fun i ↦ restrictOverMap g (s i))
    (fun i ↦ restrictOverMap g (c i)) (fun i j ↦ ?_) ?_
  · change restrictOverMap g (s j ≫ c i) = _
    rw [hsc]
    split_ifs
    · exact restrictOverMap_id (R := R) (M := unit _) (N := unit _) (𝟙 _)
    · rfl
  · change ∑ i, restrictOverMap g (c i ≫ s i) = _
    rw [← restrictOverMap_sum, htot]
    rfl

variable {M} in
/-- `Hom(M, R) ⊗ P ⟶ Hom(M, P)` is natural in `M`: for `f : M ⟶ M'` the square
```
  Hom(M', R) ⊗ P ---> Hom(M', P)
        |                  |
  f^* ⊗ P                 f^*
        v                  v
  Hom(M, R) ⊗ P  ---> Hom(M, P)
```
commutes. -/
lemma dualTensorHom_naturality {M' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (f : M ⟶ M') :
    homObjMap f (𝟙 (unit _)) ▷ P ≫ dualTensorHom M P =
      dualTensorHom M' P ≫ homObjMap f (𝟙 P) := by
  ext U : 1
  refine ModuleCat.MonoidalCategory.tensor_ext fun φ p ↦ ?_
  refine hom_ext fun W ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
  exact (dualTensorHom_app_tmul_app_apply M P _ p W m).trans
    (dualTensorHom_app_tmul_app_apply M' P φ p W _).symm

variable {P} in
/-- `Hom(M, R) ⊗ P ⟶ Hom(M, P)` is natural in `P`: for `g : P ⟶ P'` the square
```
  Hom(M, R) ⊗ P  ---> Hom(M, P)
        |                 |
  Hom(M, R) ⊗ g          g_*
        v                 v
  Hom(M, R) ⊗ P' ---> Hom(M, P')
```
commutes. -/
lemma dualTensorHom_naturality_right {P' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    (g : P ⟶ P') :
    homObj M (unit _) ◁ g ≫ dualTensorHom M P' = dualTensorHom M P ≫ homObjMap (𝟙 M) g := by
  ext U : 1
  refine ModuleCat.MonoidalCategory.tensor_ext fun φ p ↦ ?_
  refine hom_ext fun W ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ ?_)
  refine (dualTensorHom_app_tmul_app_apply M P' φ (g.app _ p) W m).trans ?_
  change _ = g.app (op W.unop.left) ((((dualTensorHom M P).app U (φ ⊗ₜ p)).app W) m)
  rw [dualTensorHom_app_tmul_app_apply, (g.app _).hom.map_smul, naturality_apply]
end PresheafOfModules
