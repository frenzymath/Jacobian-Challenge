import Mathlib.Data.Int.Interval
import Jacobian.AlgebraicGeometry.Modules.FreeComplexSplit
import Jacobian.LinearAlgebra.Matrix.ComplementaryMinors

/-!
# The locus where a complex of matrices has prescribed cohomology

Let `C` be a bounded complex of finite free modules over `Γ(X, ⊤)`, given by matrices
`C n m : Γ(X, ⊤)^{ι n} → Γ(X, ⊤)^{ι m}`. For `i : ℤ` and `k : ℕ`, the *rank condition* at a point
`y` says that the fibre of `C` at `y` has cohomology of dimension `k` in degree `i` and no other
cohomology: `rank C_{q-1}(y) + rank C_q(y) + [q = i] k = |ι q|` for all `q`.

* Near a point satisfying the rank condition, the complex `C` splits: there is an open
  neighbourhood `W` such that after pulling back along any `g : Z ⟶ X` with image in `W`, the
  middle term in every degree `q` is split, with cohomology free of rank `[q = i] k`
  (`AlgebraicGeometry.Scheme.exists_opens_hasSplitHomology`).
* In particular, the rank condition defines an open subset of `X`
  (`AlgebraicGeometry.Scheme.isOpen_setOf_rankCondition`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- A global function whose basic open contains the image of `g` pulls back to a unit. -/
lemma isUnit_appTop_of_range_subset {Z : Scheme.{u}} (g : Z ⟶ X) (s : Γ(X, ⊤))
    (hs : Set.range g ⊆ X.basicOpen s) : IsUnit (g.appTop s) := by
  refine isUnit_of_le_basicOpen ?_
  rw [← preimage_basicOpen_top]
  intro z _
  exact hs ⟨z, rfl⟩

lemma mem_finset_inf {ι : Type*} {s : Finset ι} {W : ι → X.Opens} {y : X}
    (h : ∀ q ∈ s, y ∈ W q) : y ∈ s.inf W := by
  classical
  induction s using Finset.induction_on with
  | empty => trivial
  | insert a s _ ih =>
    rw [Finset.inf_insert]
    exact ⟨h a (Finset.mem_insert_self _ _), ih fun q hq ↦ h q (Finset.mem_insert_of_mem hq)⟩

/-- **Splitting near a point with complementary ranks.** Let `B * A = 0` for matrices of global
functions whose ranks at a point `y` add up to the size of the middle term. Then on an open
neighbourhood `W` of `y`, after pulling back along any `g : Z ⟶ X` with image in `W`, `A` and `B`
have split rank factorisations with `L₁ L₁' + M₂' M₂ = 1`. -/
theorem exists_opens_split_of_rank_add_eq {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁]
    [Fintype ι₂] [DecidableEq ι₁] (A : Matrix ι₁ ι₀ Γ(X, ⊤)) (B : Matrix ι₂ ι₁ Γ(X, ⊤))
    (hBA : B * A = 0) (y : X)
    (h : (A.map (X.fromSpecResidueField y).appTop).rank +
      (B.map (X.fromSpecResidueField y).appTop).rank = Fintype.card ι₁) :
    ∃ W : X.Opens, y ∈ W ∧ ∀ {Z : Scheme.{u}} (g : Z ⟶ X), Set.range g ⊆ W →
      ∃ (L₁ : Matrix ι₁ (Fin (A.map (X.fromSpecResidueField y).appTop).rank) Γ(Z, ⊤))
        (M₁ : Matrix (Fin (A.map (X.fromSpecResidueField y).appTop).rank) ι₀ Γ(Z, ⊤))
        (L₁' : Matrix (Fin (A.map (X.fromSpecResidueField y).appTop).rank) ι₁ Γ(Z, ⊤))
        (M₁' : Matrix ι₀ (Fin (A.map (X.fromSpecResidueField y).appTop).rank) Γ(Z, ⊤))
        (L₂ : Matrix ι₂ (Fin (B.map (X.fromSpecResidueField y).appTop).rank) Γ(Z, ⊤))
        (M₂ : Matrix (Fin (B.map (X.fromSpecResidueField y).appTop).rank) ι₁ Γ(Z, ⊤))
        (L₂' : Matrix (Fin (B.map (X.fromSpecResidueField y).appTop).rank) ι₂ Γ(Z, ⊤))
        (M₂' : Matrix ι₁ (Fin (B.map (X.fromSpecResidueField y).appTop).rank) Γ(Z, ⊤)),
        (A.map g.appTop = L₁ * M₁ ∧ L₁' * L₁ = 1 ∧ M₁ * M₁' = 1) ∧
          (B.map g.appTop = L₂ * M₂ ∧ L₂' * L₂ = 1 ∧ M₂ * M₂' = 1) ∧
            L₁ * L₁' + M₂' * M₂ = 1 := by
  obtain ⟨x⟩ : Nonempty (Spec (X.residueField y)) := inferInstance
  obtain ⟨e₁, e₀, h₁⟩ := (Modules.le_rank_map_appTop_iff (Modules.isField_Γ_Spec_residueField y)
    (X.fromSpecResidueField y) x A _).1 le_rfl
  obtain ⟨f₂, f₁, h₂⟩ := (Modules.le_rank_map_appTop_iff (Modules.isField_Γ_Spec_residueField y)
    (X.fromSpecResidueField y) x B _).1 le_rfl
  rw [Modules.fromSpecResidueField_base_apply] at h₁ h₂
  refine ⟨X.basicOpen (A.submatrix e₁ e₀).det ⊓ X.basicOpen (B.submatrix f₂ f₁).det, ⟨h₁, h₂⟩,
    fun g hg ↦ ?_⟩
  have u₁ : IsUnit ((A.map g.appTop).submatrix e₁ e₀).det := by
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_appTop_of_range_subset g _ fun z hz ↦ (hg hz).1
  have u₂ : IsUnit ((B.map g.appTop).submatrix f₂ f₁).det := by
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_appTop_of_range_subset g _ fun z hz ↦ (hg hz).2
  exact Matrix.exists_split_of_isUnit_det_submatrix _ _
    (by rw [← Matrix.map_mul, hBA, Matrix.map_zero _ (map_zero _)]) e₁ e₀ u₁ f₂ f₁ u₂
    (by simpa using h)

section Complex

variable {ι : ℤ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
  (C : ∀ n m : ℤ, Matrix (ι m) (ι n) Γ(X, ⊤))

/-- The **rank condition** at a point `y` for a complex of matrices of global functions: the
fibre at `y` has cohomology of dimension `k` in degree `i` and vanishing cohomology in the other
degrees, `rank C_{q-1}(y) + rank C_q(y) + [q = i] k = |ι q|`. -/
def RankCondition (i : ℤ) (k : ℕ) (y : X) : Prop :=
  ∀ q : ℤ, ((C (q - 1) q).map (X.fromSpecResidueField y).appTop).rank +
    ((C q (q + 1)).map (X.fromSpecResidueField y).appTop).rank + (if q = i then k else 0) =
      Fintype.card (ι q)

variable {C}

/-- Near a point satisfying the rank condition, the complex is split in a given degree `q`, with
cohomology free of rank `[q = i] k`. -/
theorem exists_opens_hasSplitHomology_degree (hC : ∀ n m l, C m l * C n m = 0) {i : ℤ} {k : ℕ}
    {y : X} (hy : RankCondition C i k y) (q : ℤ) :
    ∃ W : X.Opens, y ∈ W ∧ (IsEmpty (ι q) → W = ⊤) ∧ ∀ {Z : Scheme.{u}} (g : Z ⟶ X),
      Set.range g ⊆ W → Matrix.HasSplitHomology ((C (q - 1) q).map g.appTop)
        ((C q (q + 1)).map g.appTop) (Fin (if q = i then k else 0)) := by
  by_cases hq : IsEmpty (ι q)
  · refine ⟨⊤, trivial, fun _ ↦ rfl, fun g _ ↦ ?_⟩
    have hk : (if q = i then k else 0) = 0 := by
      have := hy q
      rw [Fintype.card_eq_zero] at this
      omega
    have : IsEmpty (Fin (if q = i then k else 0)) := by rw [hk]; infer_instance
    exact ⟨0, 0, 0, 0, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
      Subsingleton.elim _ _⟩
  by_cases hqi : q ≠ i
  · have h := hy q
    rw [if_neg hqi, add_zero] at h
    obtain ⟨W, hyW, hW⟩ := exists_opens_split_of_rank_add_eq _ _ (hC _ _ _) y h
    refine ⟨W, hyW, fun h ↦ absurd h hq, fun g hg ↦ ?_⟩
    have : IsEmpty (Fin (if q = i then k else 0)) := by rw [if_neg hqi]; infer_instance
    obtain ⟨L₁, M₁, L₁', M₁', L₂, M₂, L₂', M₂', s₁, s₂, s⟩ := hW g hg
    exact Matrix.hasSplitHomology_of_add_eq_one s₁ s₂ s
  rw [not_not] at hqi
  subst hqi

  have hlo := hy (q - 1)
  rw [if_neg (by omega), add_zero, show q - 1 + 1 = q by omega] at hlo
  have hhi := hy (q + 1)
  rw [if_neg (by omega), add_zero, show q + 1 - 1 = q by omega] at hhi
  obtain ⟨Wa, hya, ha⟩ := exists_opens_split_of_rank_add_eq _ _ (hC _ _ _) y hlo
  obtain ⟨Wb, hyb, hb⟩ := exists_opens_split_of_rank_add_eq _ _ (hC _ _ _) y hhi
  set W₁ := Wa ⊓ Wb with hW₁
  obtain ⟨-, -, -, -, L₁, M₁, L₁', M₁', -, s₁, -⟩ := ha W₁.ι (by
    rw [Opens.range_ι]
    exact fun z hz ↦ hz.1)
  obtain ⟨L₂, M₂, L₂', M₂', -, -, -, -, s₂, -, -⟩ := hb W₁.ι (by
    rw [Opens.range_ι]
    exact fun z hz ↦ hz.2)
  have hA : (C q (q + 1)).map W₁.ι.appTop * (C (q - 1) q).map W₁.ι.appTop = 0 := by
    rw [← Matrix.map_mul, hC, Matrix.map_zero _ (map_zero _)]
  have hML := Matrix.mul_eq_zero_of_split hA s₁.1 s₁.2.2 s₂.1 s₂.2.1
  set ε := Matrix.splitIdempotent L₁ L₁' M₂ M₂' with hε
  have he : ε * ε = ε := Matrix.splitIdempotent_mul_self s₁.2.1 s₂.2.2 hML
  set y₁ : W₁.toScheme := ⟨y, hya, hyb⟩

  have hrank : (ε.map (W₁.toScheme.fromSpecResidueField y₁).appTop).rank = k := by
    let := (Modules.isField_Γ_Spec_residueField y₁).toField
    have := Matrix.rank_splitIdempotent_map hA s₁ s₂
      (W₁.toScheme.fromSpecResidueField y₁).appTop.hom
    have h₀ := hy q
    rw [if_pos rfl] at h₀
    rw [hε]
    change _ = k
    convert this using 1
    omega
  have hrank' : (ε.map (W₁.toScheme.fromSpecResidueField y₁).appTop).rank +
      ((1 - ε).map (W₁.toScheme.fromSpecResidueField y₁).appTop).rank = Fintype.card (ι q) := by
    let := (Modules.isField_Γ_Spec_residueField y₁).toField
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.rank_add_rank_one_sub (by rw [← Matrix.map_mul, he])
  obtain ⟨W₂, hyW₂, hc⟩ := exists_opens_split_of_rank_add_eq ε (1 - ε)
    (by rw [Matrix.sub_mul, he, Matrix.one_mul, sub_self]) y₁ hrank'
  refine ⟨W₁.ι ''ᵁ W₂, ⟨y₁, hyW₂, rfl⟩, fun h ↦ absurd h hq, fun g hg ↦ ?_⟩
  have hg₁ : Set.range g ⊆ Set.range W₁.ι := by
    refine hg.trans ?_
    rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  set g₁ := IsOpenImmersion.lift W₁.ι g hg₁
  have hfac : g₁ ≫ W₁.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hg₂ : Set.range g₁ ⊆ W₂ := by
    rintro _ ⟨z, rfl⟩
    rw [← Hom.preimage_image_eq W₁.ι W₂]
    change W₁.ι (g₁ z) ∈ W₁.ι ''ᵁ W₂
    rw [← Hom.comp_apply, hfac]
    exact hg ⟨z, rfl⟩
  obtain ⟨L₃, M₃, L₃', M₃', -, -, -, -, s₃, -, -⟩ := hc g₁ hg₂

  have t₁ := Matrix.split_map g₁.appTop.hom s₁
  have t₂ := Matrix.split_map g₁.appTop.hom s₂
  have c₁ : ((C (q - 1) q).map W₁.ι.appTop).map g₁.appTop.hom = (C (q - 1) q).map g.appTop := by
    rw [← hfac, Modules.map_appTop_comp]
  have c₂ : ((C q (q + 1)).map W₁.ι.appTop).map g₁.appTop.hom = (C q (q + 1)).map g.appTop := by
    rw [← hfac, Modules.map_appTop_comp]
  rw [c₁] at t₁
  rw [c₂] at t₂
  have hε₃ := s₃.1
  have hεmap : ε.map g₁.appTop = Matrix.splitIdempotent (L₁.map g₁.appTop.hom)
      (L₁'.map g₁.appTop.hom) (M₂.map g₁.appTop.hom) (M₂'.map g₁.appTop.hom) :=
    Matrix.splitIdempotent_map _
  rw [hεmap] at hε₃
  have h₃ : M₃ * L₃ = 1 := by
    refine Matrix.mul_eq_one_of_isIdempotentElem ?_ s₃.2.1 s₃.2.2
    rw [← s₃.1, ← Matrix.map_mul, he]
  have hA' : (C q (q + 1)).map g.appTop * (C (q - 1) q).map g.appTop = 0 := by
    rw [← Matrix.map_mul, hC, Matrix.map_zero _ (map_zero _)]
  refine (Matrix.hasSplitHomology_of_splitIdempotent hA' t₁ t₂ hε₃ h₃).of_equiv
    (finCongr ?_)
  rw [hrank, if_pos rfl]

/-- **Splitting near a point satisfying the rank condition.** Let `C` be a bounded complex of
finite free `Γ(X, ⊤)`-modules, and `y` a point satisfying the rank condition for `i` and `k`.
Then on an open neighbourhood `W` of `y`, after pulling back along any `g : Z ⟶ X` with image in
`W`, the complex is split in every degree `q`, with cohomology free of rank `[q = i] k`. -/
theorem exists_opens_hasSplitHomology (hC : ∀ n m l, C m l * C n m = 0) (N : ℕ)
    (hN : ∀ n : ℤ, n < 0 ∨ N < n → IsEmpty (ι n)) {i : ℤ} {k : ℕ} {y : X}
    (hy : RankCondition C i k y) :
    ∃ W : X.Opens, y ∈ W ∧ ∀ {Z : Scheme.{u}} (g : Z ⟶ X), Set.range g ⊆ W → ∀ q : ℤ,
      Matrix.HasSplitHomology ((C (q - 1) q).map g.appTop) ((C q (q + 1)).map g.appTop)
        (Fin (if q = i then k else 0)) := by
  choose W hyW hWtop hW using exists_opens_hasSplitHomology_degree hC hy
  refine ⟨(Finset.Icc (0 : ℤ) N).inf W, mem_finset_inf fun q _ ↦ hyW q, fun g hg q ↦ ?_⟩
  by_cases hq : q ∈ Finset.Icc (0 : ℤ) N
  · exact hW q g (hg.trans (Finset.inf_le (f := W) hq))
  · refine hW q g ?_
    rw [hWtop q (hN q (by simp only [Finset.mem_Icc, not_and_or, not_le] at hq; exact hq))]
    exact fun _ _ ↦ trivial

omit [∀ n, DecidableEq (ι n)] in
/-- **The rank condition is open.** -/
theorem isOpen_setOf_rankCondition (hC : ∀ n m l, C m l * C n m = 0) (N : ℕ)
    (hN : ∀ n : ℤ, n < 0 ∨ N < n → IsEmpty (ι n)) (i : ℤ) (k : ℕ) :
    IsOpen {y : X | RankCondition C i k y} := by
  classical
  refine isOpen_iff_forall_mem_open.2 fun y hy ↦ ?_
  obtain ⟨W, hyW, hW⟩ := exists_opens_hasSplitHomology hC N hN hy
  refine ⟨W, fun z hz q ↦ ?_, W.isOpen, hyW⟩
  have h := hW (X.fromSpecResidueField z) (by
    rw [range_fromSpecResidueField]
    simpa using hz) q
  let := (Modules.isField_Γ_Spec_residueField z).toField
  have := h.rank_add_rank_add_card
    (by rw [← Matrix.map_mul, hC, Matrix.map_zero _ (map_zero _)])
  simpa using this

omit [∀ n, DecidableEq (ι n)] in
/-- The rank condition for the pullback of a complex of matrices along `f : X ⟶ Y` at a point `x`
is the rank condition at `f x`. -/
lemma RankCondition.of_map {Y : Scheme.{u}} (f : X ⟶ Y) {C : ∀ n m : ℤ, Matrix (ι m) (ι n) Γ(Y, ⊤)}
    {i : ℤ} {k : ℕ} {x : X} (h : RankCondition (fun n m ↦ (C n m).map f.appTop) i k x) :
    RankCondition C i k (f x) := by
  intro q
  rw [← h q]
  obtain ⟨p⟩ : Nonempty (Spec (X.residueField x)) := inferInstance
  obtain ⟨p'⟩ : Nonempty (Spec (Y.residueField (f x))) := inferInstance
  have e (n m : ℤ) : ((C n m).map (Y.fromSpecResidueField (f x)).appTop).rank =
      (((C n m).map f.appTop).map (X.fromSpecResidueField x).appTop).rank := by
    rw [← Modules.map_appTop_comp]
    refine Modules.rank_map_appTop_eq_of_base_eq (Modules.isField_Γ_Spec_residueField _)
      (Modules.isField_Γ_Spec_residueField _) _ _ p' p ?_ _
    rw [Modules.fromSpecResidueField_base_apply, Hom.comp_apply,
      Modules.fromSpecResidueField_base_apply]
  rw [e, e]

end Complex

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

open SheafOfModules

lemma isZero_free_of_isEmpty {X : Scheme.{u}} (I : Type u) [IsEmpty I] :
    IsZero (free (R := X.ringCatSheaf) I) :=
  (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun i ↦ isEmptyElim i)


end AlgebraicGeometry.Scheme.Modules
