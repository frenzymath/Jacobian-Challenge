import Mathlib.Data.Matrix.ColumnRowPartitioned
import Jacobian.LinearAlgebra.Matrix.SplitFactorization
import Jacobian.LinearAlgebra.Matrix.Rank

/-!
# Complexes of finite free modules split by complementary minors

Let `R^{ι₀}
ring, `B * A = 0`. If `A` has an invertible `a × a` minor and `B` an invertible `b × b` minor with
`a + b = |ι₁|`, then both matrices have split rank factorisations `A = L₁ M₁`, `B = L₂ M₂` with
`L₁ L₁' + M₂' M₂ = 1`; in particular the complex is split exact at `R^{ι₁}`
(`Matrix.exists_split_of_isUnit_det_submatrix`).

Over a ring `S` with a ring homomorphism `ψ : S →+* K` to a field such that every element not
killed by `ψ` is a unit (for instance a local ring and its residue field), this applies as soon as
the ranks of `A` and `B` at `ψ` add up to `|ι₁|` (`Matrix.exists_split_of_rank_map_add_eq`).
Conversely, for a complex of finite free `S`-modules which is exact except in one degree `i`,
where its cohomology is free of rank `k` (in a matrix form), the ranks at `ψ` satisfy
`rank A_{q-1} + rank A_q + [q = i] k = |ι_q|`
(`Matrix.rank_map_add_rank_map_add_eq_of_exact`): the fibre of the complex at `ψ` has cohomology
of dimension `k` in degree `i` only.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open Matrix

namespace Matrix

section Ring

variable {R : Type*} [CommRing R] {ι₀ ι₁ ι₂ α β : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]
  [Fintype α] [Fintype β] [DecidableEq ι₁] [DecidableEq α]
  [DecidableEq β]

/-- **Splitting a complex of free modules by complementary invertible minors.** Let `B * A = 0`
for matrices `A : R^{ι₀} → R^{ι₁}` and `B : R^{ι₁} → R^{ι₂}` over a commutative ring. If an
`a × a` minor of `A` and a `b × b` minor of `B` are units, with `a + b = |ι₁|`, then `A` and `B`
have split rank factorisations `A = L₁ M₁` through `R^a` and `B = L₂ M₂` through `R^b`, with
`L₁ L₁' + M₂' M₂ = 1`. -/
theorem exists_split_of_isUnit_det_submatrix (A : Matrix ι₁ ι₀ R) (B : Matrix ι₂ ι₁ R)
    (hBA : B * A = 0) (e₁ : α → ι₁) (e₀ : α → ι₀) (hA : IsUnit (A.submatrix e₁ e₀).det)
    (f₂ : β → ι₂) (f₁ : β → ι₁) (hB : IsUnit (B.submatrix f₂ f₁).det)
    (hcard : Fintype.card α + Fintype.card β = Fintype.card ι₁) :
    ∃ (L₁ : Matrix ι₁ α R) (M₁ : Matrix α ι₀ R) (L₁' : Matrix α ι₁ R) (M₁' : Matrix ι₀ α R)
      (L₂ : Matrix ι₂ β R) (M₂ : Matrix β ι₁ R) (L₂' : Matrix β ι₂ R) (M₂' : Matrix ι₁ β R),
      (A = L₁ * M₁ ∧ L₁' * L₁ = 1 ∧ M₁ * M₁' = 1) ∧
        (B = L₂ * M₂ ∧ L₂' * L₂ = 1 ∧ M₂ * M₂' = 1) ∧ L₁ * L₁' + M₂' * M₂ = 1 := by
  classical
  set A' : Matrix ι₁ α R := A.submatrix id e₀
  set B' : Matrix β ι₁ R := B.submatrix f₂ id
  set L : Matrix α ι₁ R := (A.submatrix e₁ e₀)⁻¹ * (1 : Matrix ι₁ ι₁ R).submatrix e₁ id
  set S : Matrix ι₁ β R := (1 : Matrix ι₁ ι₁ R).submatrix id f₁ * (B.submatrix f₂ f₁)⁻¹
  set s₀ : Matrix ι₀ α R := (1 : Matrix ι₀ ι₀ R).submatrix id e₀
  set t₂ : Matrix β ι₂ R := (1 : Matrix ι₂ ι₂ R).submatrix f₂ id
  have hAs : A * s₀ = A' := mul_one_submatrix_id e₀ A
  have htB : t₂ * B = B' := one_submatrix_id_mul f₂ B
  have hLA : L * A' = 1 := by
    have : (1 : Matrix ι₁ ι₁ R).submatrix e₁ id * A' = A.submatrix e₁ e₀ := by
      rw [one_submatrix_id_mul]
      rfl
    rw [Matrix.mul_assoc, this, Matrix.nonsing_inv_mul _ hA]
  have hBS : B' * S = 1 := by
    have : B' * (1 : Matrix ι₁ ι₁ R).submatrix id f₁ = B.submatrix f₂ f₁ := by
      rw [mul_one_submatrix_id]
      rfl
    rw [← Matrix.mul_assoc, this, Matrix.mul_nonsing_inv _ hB]
  have hBA' : B' * A' = 0 := by
    rw [← hAs, ← htB, Matrix.mul_assoc, ← Matrix.mul_assoc B, hBA, Matrix.zero_mul,
      Matrix.mul_zero]
  set X := L - L * S * B' with hX
  have hXA : X * A' = 1 := by
    rw [hX, Matrix.sub_mul, hLA, Matrix.mul_assoc, hBA', Matrix.mul_zero, sub_zero]
  have hXS : X * S = 0 := by
    rw [hX, Matrix.sub_mul, Matrix.mul_assoc (L * S), hBS, Matrix.mul_one, sub_self]
  have h1 : fromRows X B' * fromCols A' S = 1 := by
    rw [fromRows_mul_fromCols, hXA, hXS, hBA', hBS, fromBlocks_one]
  obtain ⟨e⟩ : Nonempty (ι₁ ≃ α ⊕ β) :=
    ⟨Fintype.equivOfCardEq (by rw [Fintype.card_sum, hcard])⟩
  have h2 : fromCols A' S * fromRows X B' = 1 :=
    (fromCols_mul_fromRows_eq_one_comm e _ _ _ _).2 h1
  rw [fromCols_mul_fromRows] at h2
  have hB'A : B' * A = 0 := by rw [← htB, Matrix.mul_assoc, hBA, Matrix.mul_zero]
  have hBA'' : B * A' = 0 := by rw [← hAs, ← Matrix.mul_assoc, hBA, Matrix.zero_mul]
  refine ⟨A', X * A, X, s₀, B * S, B', t₂, S, ⟨?_, hXA, ?_⟩, ⟨?_, ?_, hBS⟩, h2⟩
  · calc A = (A' * X + S * B') * A := by rw [h2, Matrix.one_mul]
      _ = A' * (X * A) := by
        rw [Matrix.add_mul, Matrix.mul_assoc S, hB'A, Matrix.mul_zero, add_zero,
          Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, hAs, hXA]
  · calc B = B * (A' * X + S * B') := by rw [h2, Matrix.mul_one]
      _ = B * S * B' := by
        rw [Matrix.mul_add, ← Matrix.mul_assoc B A', hBA'', Matrix.zero_mul, zero_add]
        exact (Matrix.mul_assoc _ _ _).symm
  · rw [← Matrix.mul_assoc, htB, hBS]

end Ring

section Field

variable {K : Type*} [Field K] {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]

omit [Fintype ι₂] in
/-- Over a field, the ranks of two matrices with vanishing product `B * A = 0` add up to at most
the size of the middle term. -/
lemma rank_add_rank_le_of_mul_eq_zero (A : Matrix ι₁ ι₀ K) (B : Matrix ι₂ ι₁ K)
    (hBA : B * A = 0) : A.rank + B.rank ≤ Fintype.card ι₁ := by
  have := rank_add_rank_add_rank_le (0 : Matrix ι₁ ι₁ K) A B (by simp) (by simp) (by simp) hBA
  simpa using this

/-- **Ranks in a split complex over a field.** Let `B * A = 0` over a field, and suppose that the
middle term `K^{ι₁}` is split by matrices `I`, `P` with `P I = 1`, `B I = 0`, `P A = 0` and
`I P + A σ + τ B = 1`. Then `rank A + rank B + |k| = |ι₁|`: the cohomology has dimension `|k|`. -/
theorem rank_add_rank_add_card_eq {k : Type*} [Fintype k] [DecidableEq k] [DecidableEq ι₁]
    (A : Matrix ι₁ ι₀ K) (B : Matrix ι₂ ι₁ K) (I : Matrix ι₁ k K) (P : Matrix k ι₁ K)
    (σ : Matrix ι₀ ι₁ K) (τ : Matrix ι₁ ι₂ K) (hBA : B * A = 0) (hPI : P * I = 1)
    (hBI : B * I = 0) (hPA : P * A = 0) (h : I * P + A * σ + τ * B = 1) :
    A.rank + B.rank + Fintype.card k = Fintype.card ι₁ := by
  have hk : (I * P).rank = Fintype.card k := by
    refine le_antisymm ((rank_mul_le_right _ _).trans (rank_le_card_height P)) ?_
    calc Fintype.card k = (1 : Matrix k k K).rank := (rank_one).symm
      _ = (P * (I * P) * I).rank := by
        rw [← Matrix.mul_assoc, hPI, Matrix.one_mul, hPI]
      _ ≤ (I * P).rank := (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  have hle := rank_add_rank_add_rank_le (I * P) A B
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, hPI, Matrix.one_mul])
    (by rw [Matrix.mul_assoc, hPA, Matrix.mul_zero])
    (by rw [← Matrix.mul_assoc, hBI, Matrix.zero_mul]) hBA
  have hge := card_le_rank_add_rank_add_rank _ _ _ h
  have h₁ := rank_mul_le_left A σ
  have h₂ := rank_mul_le_right τ B
  omega

omit [Fintype ι₁] in
/-- The rank of a matrix with zero rows appended is its rank. -/
lemma rank_fromRows_zero [Finite ι₁] {κ : Type*} [Finite κ] (A : Matrix ι₁ ι₀ K) :
    (fromRows A (0 : Matrix κ ι₀ K)).rank = A.rank := by
  classical
  have := Fintype.ofFinite ι₁
  have := Fintype.ofFinite κ
  refine le_antisymm ?_ ?_
  · have : fromRows A (0 : Matrix κ ι₀ K) = fromRows 1 0 * A := by
      rw [fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
    rw [this]
    exact rank_mul_le_right _ _
  · have : A = fromCols (1 : Matrix ι₁ ι₁ K) (0 : Matrix ι₁ κ K) *
        fromRows A (0 : Matrix κ ι₀ K) := by
      rw [fromCols_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero]
    conv_lhs => rw [this]
    exact rank_mul_le_right _ _

omit [Fintype ι₁] in
/-- The rank of a matrix with columns appended is at most its rank plus the number of new
columns. -/
lemma rank_fromCols_le {κ : Type*} [Fintype κ] (A : Matrix ι₁ ι₀ K) (D : Matrix ι₁ κ K) :
    (fromCols A D).rank ≤ A.rank + Fintype.card κ := by
  classical
  have : fromCols A D = A * fromCols (1 : Matrix ι₀ ι₀ K) 0 + D * fromCols 0 1 := by
    rw [mul_fromCols, mul_fromCols, Matrix.mul_one, Matrix.mul_zero, Matrix.mul_zero,
      Matrix.mul_one]
    ext a (b | b) <;> simp
  rw [this]
  refine (rank_add_le _ _).trans (Nat.add_le_add (rank_mul_le_left _ _) ?_)
  exact (rank_mul_le_left _ _).trans (rank_le_card_width D)

end Field

section Exact

variable {S K : Type*} [CommRing S] [Field K] (ψ : S →+* K)
  {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]

/-- **Splitting at a point where the ranks are complementary.** Let `ψ : S →+* K` be a ring
homomorphism to a field such that every element not killed by `ψ` is a unit. If `B * A = 0` and
the ranks of `A` and `B` at `ψ` add up to `|ι₁|`, then `A` and `B` have split rank factorisations
of these ranks, with `L₁ L₁' + M₂' M₂ = 1`. -/
theorem exists_split_of_rank_map_add_eq [DecidableEq ι₁]
    (hψ : ∀ s, ψ s ≠ 0 → IsUnit s) (A : Matrix ι₁ ι₀ S)
    (B : Matrix ι₂ ι₁ S) (hBA : B * A = 0)
    (h : (A.map ψ).rank + (B.map ψ).rank = Fintype.card ι₁) :
    ∃ (L₁ : Matrix ι₁ (Fin (A.map ψ).rank) S) (M₁ : Matrix (Fin (A.map ψ).rank) ι₀ S)
      (L₁' : Matrix (Fin (A.map ψ).rank) ι₁ S) (M₁' : Matrix ι₀ (Fin (A.map ψ).rank) S)
      (L₂ : Matrix ι₂ (Fin (B.map ψ).rank) S) (M₂ : Matrix (Fin (B.map ψ).rank) ι₁ S)
      (L₂' : Matrix (Fin (B.map ψ).rank) ι₂ S) (M₂' : Matrix ι₁ (Fin (B.map ψ).rank) S),
      (A = L₁ * M₁ ∧ L₁' * L₁ = 1 ∧ M₁ * M₁' = 1) ∧
        (B = L₂ * M₂ ∧ L₂' * L₂ = 1 ∧ M₂ * M₂' = 1) ∧ L₁ * L₁' + M₂' * M₂ = 1 := by
  obtain ⟨e₁, e₀, h₁⟩ := (le_rank_map_iff A ψ _).1 le_rfl
  obtain ⟨f₂, f₁, h₂⟩ := (le_rank_map_iff B ψ _).1 le_rfl
  exact exists_split_of_isUnit_det_submatrix A B hBA e₁ e₀ (hψ _ h₁) f₂ f₁ (hψ _ h₂)
    (by simpa using h)

/-- The rank at `ψ` of a matrix with a split rank factorisation through `ρ` is `|ρ|`. -/
lemma rank_map_eq_of_split {ρ : Type*} [Fintype ρ] [DecidableEq ρ] {B : Matrix ι₂ ι₁ S}
    {L : Matrix ι₂ ρ S} {M : Matrix ρ ι₁ S} {L' : Matrix ρ ι₂ S} {M' : Matrix ι₁ ρ S}
    (hB : B = L * M ∧ L' * L = 1 ∧ M * M' = 1) : (B.map ψ).rank = Fintype.card ρ := by
  obtain ⟨k, kL, kM⟩ := split_map ψ hB
  refine le_antisymm ?_ ?_
  · rw [k]
    exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  · have : L'.map ψ * B.map ψ * M'.map ψ = 1 := by
      rw [k, Matrix.mul_assoc, Matrix.mul_assoc, kM, Matrix.mul_one, kL]
    calc Fintype.card ρ = (1 : Matrix ρ ρ K).rank := rank_one.symm
      _ ≤ (B.map ψ).rank := by
        rw [← this]
        exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

/-- **Ranks at a point of an exact complex.** Let `B * A = 0`, where `B = L M` has a split rank
factorisation, and suppose that the complex is exact at `S^{ι₁}`: every square matrix `K` with
`B K = 0` is of the form `A V`. Then for every ring homomorphism `ψ` to a field, the ranks of `A`
and `B` at `ψ` add up to `|ι₁|`. -/
theorem rank_map_add_rank_map_eq_of_exact (A : Matrix ι₁ ι₀ S) (B : Matrix ι₂ ι₁ S)
    (hBA : B * A = 0) {ρ : Type*} [Fintype ρ] [DecidableEq ρ] {L : Matrix ι₂ ρ S}
    {M : Matrix ρ ι₁ S} {L' : Matrix ρ ι₂ S} {M' : Matrix ι₁ ρ S}
    (hB : B = L * M ∧ L' * L = 1 ∧ M * M' = 1)
    (hex : ∀ K : Matrix ι₁ ι₁ S, B * K = 0 → ∃ V : Matrix ι₀ ι₁ S, A * V = K) :
    (A.map ψ).rank + (B.map ψ).rank = Fintype.card ι₁ := by
  classical
  have rB := rank_map_eq_of_split ψ hB
  obtain ⟨V, hV⟩ := hex (1 - M' * M) (by
    rw [hB.1, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, ← Matrix.mul_assoc M M',
      hB.2.2, Matrix.one_mul, sub_self])
  have h₁ : ((1 - M' * M).map ψ).rank ≤ (A.map ψ).rank := by
    rw [← hV, Matrix.map_mul]
    exact rank_mul_le_left _ _
  have h₂ : Fintype.card ι₁ ≤ ((1 - M' * M).map ψ).rank + ((M' * M).map ψ).rank := by
    rw [← rank_one (R := K) (n := ι₁)]
    refine le_of_eq_of_le ?_ (rank_add_le _ _)
    rw [← Matrix.map_add _ (map_add ψ), sub_add_cancel, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have h₃ : ((M' * M).map ψ).rank ≤ Fintype.card ρ := by
    rw [Matrix.map_mul]
    exact (rank_mul_le_left _ _).trans (rank_le_card_width _)
  have h₄ := rank_add_rank_le_of_mul_eq_zero (A.map ψ) (B.map ψ)
    (by rw [← Matrix.map_mul, hBA, Matrix.map_zero _ (map_zero ψ)])
  omega

end Exact

/-- After mapping to a field, the split homology idempotent has rank equal to the
middle dimension minus the ranks of the two split differentials. -/
lemma rank_splitIdempotent_map {R K : Type*} [CommRing R] [Field K]
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] [DecidableEq b]
    {ρ₁ ρ₂ : ℕ} {A₁ : Matrix b a R} {A₂ : Matrix c b R}
    {L₁ : Matrix b (Fin ρ₁) R} {M₁ : Matrix (Fin ρ₁) a R}
    {L₁' : Matrix (Fin ρ₁) b R} {M₁' : Matrix a (Fin ρ₁) R}
    {L₂ : Matrix c (Fin ρ₂) R} {M₂ : Matrix (Fin ρ₂) b R}
    {L₂' : Matrix (Fin ρ₂) c R} {M₂' : Matrix b (Fin ρ₂) R}
    (h : A₂ * A₁ = 0)
    (h₁ : A₁ = L₁ * M₁ ∧ L₁' * L₁ = 1 ∧ M₁ * M₁' = 1)
    (h₂ : A₂ = L₂ * M₂ ∧ L₂' * L₂ = 1 ∧ M₂ * M₂' = 1) (φ : R →+* K) :
    ((splitIdempotent L₁ L₁' M₂ M₂').map φ).rank = Fintype.card b - ρ₁ - ρ₂ := by
  have hML := mul_eq_zero_of_split h h₁.1 h₁.2.2 h₂.1 h₂.2.1
  obtain ⟨k₁, kL₁, -⟩ := split_map φ h₁
  obtain ⟨k₂, -, kM₂⟩ := split_map φ h₂
  have kML : M₂.map φ * L₁.map φ = 0 := by
    rw [← Matrix.map_mul, hML, Matrix.map_zero _ (map_zero φ)]
  have kA : A₂.map φ * A₁.map φ = 0 := by
    rw [← Matrix.map_mul, h, Matrix.map_zero _ (map_zero φ)]
  rw [splitIdempotent_map]
  have r₁ : (A₁.map φ).rank = ρ₁ := by simpa using rank_map_eq_of_split φ h₁
  have r₂ : (A₂.map φ).rank = ρ₂ := by simpa using rank_map_eq_of_split φ h₂
  have hle := rank_add_rank_add_rank_le _ (A₁.map φ) (A₂.map φ)
    (splitIdempotent_mul_self kL₁ kM₂ kML) (splitIdempotent_mul k₁ kL₁ kML)
    (mul_splitIdempotent k₂ kM₂ kML) kA
  have hge := card_le_rank_add_rank_add_rank _ _ _
    (add_splitIdempotent_add (L₁ := L₁.map φ) (L₁' := L₁'.map φ)
      (M₂ := M₂.map φ) (M₂' := M₂'.map φ))
  have p₁ : (L₁.map φ * L₁'.map φ).rank ≤ ρ₁ :=
    (rank_mul_le_left _ _).trans ((rank_le_card_width _).trans (by simp))
  have p₂ : ((1 - L₁.map φ * L₁'.map φ) * (M₂'.map φ * M₂.map φ)).rank ≤ ρ₂ :=
    (rank_mul_le_right _ _).trans
      ((rank_mul_le_left _ _).trans ((rank_le_card_width _).trans (by simp)))
  omega

section Complex

variable {S K : Type*} [CommRing S] [Field K] (ψ : S →+* K) {ι : ℤ → Type u}
  [∀ n, Fintype (ι n)] (C : ∀ n m : ℤ, Matrix (ι m) (ι n) S)

/-- **The fibre of a complex of finite free modules with free cohomology in one degree.** Let
`ψ : S →+* K` be a ring homomorphism to a field such that every element not killed by `ψ` is a
unit (e.g. a local ring and its residue field). Let `C` be a bounded complex of finite free
`S`-modules, given by matrices `C n m : S^{ι n} → S^{ι m}`, which is exact in every degree
`q ≠ i`, and whose cohomology in degree `i` is free on the columns of a matrix `D` with
`C i (i + 1) * D = 0`: every cycle is a boundary plus a combination of the columns of `D` (`ha`),
uniquely so (`hb`). Then in every degree `q`,
`rank C_{q-1} + rank C_q + [q = i] |κ| = |ι q|` at `ψ`: the fibre of the complex at `ψ` has
cohomology of dimension `|κ|` in degree `i` and vanishing cohomology in the other degrees.

The proof is a descending induction on `q`: in the degrees above `i`, the split factorisation of
the outgoing matrix and exactness give the rank equality, and the rank equality gives the split
factorisation of the incoming matrix (`Matrix.exists_split_of_rank_map_add_eq`). In degrees `i`
and `i - 1` the same argument is run on the complex obtained by adding `S^κ` in degree `i - 1`,
mapping by `D`, which is exact in these two degrees. -/
theorem rank_map_add_rank_map_add_eq_of_exact (hψ : ∀ s, ψ s ≠ 0 → IsUnit s)
    (hC : ∀ n m l, C m l * C n m = 0) (N : ℤ) (hN : ∀ n, N < n → IsEmpty (ι n)) (i : ℤ)
    {κ : Type u} [Fintype κ]
    (hex : ∀ q, q ≠ i → ∀ (c : Type u) [Finite c] (K : Matrix (ι q) c S),
      C q (q + 1) * K = 0 → ∃ V : Matrix (ι (q - 1)) c S, C (q - 1) q * V = K)
    (D : Matrix (ι i) κ S) (hD : C i (i + 1) * D = 0)
    (ha : ∀ K : Matrix (ι i) (ι i) S, C i (i + 1) * K = 0 →
      ∃ (V : Matrix (ι (i - 1)) (ι i) S) (V' : Matrix κ (ι i) S), C (i - 1) i * V + D * V' = K)
    (hb : ∀ (U : Matrix (ι (i - 1)) (ι (i - 1) ⊕ κ) S) (V' : Matrix κ (ι (i - 1) ⊕ κ) S),
      C (i - 1) i * U + D * V' = 0 → V' = 0) (q : ℤ) :
    ((C (q - 1) q).map ψ).rank + ((C q (q + 1)).map ψ).rank + (if q = i then Fintype.card κ else 0)
      = Fintype.card (ι q) := by
  classical

  let P (q : ℤ) : Prop := ((C (q - 1) q).map ψ).rank + ((C q (q + 1)).map ψ).rank +
    (if q = i then Fintype.card κ else 0) = Fintype.card (ι q)

  have split (q : ℤ) (hq : q + 1 ≠ i) (h : P (q + 1)) :
      ∃ (ρ : Type) (_ : Fintype ρ) (_ : DecidableEq ρ) (L : Matrix (ι (q + 1)) ρ S)
        (M : Matrix ρ (ι q) S) (L' : Matrix ρ (ι (q + 1)) S) (M' : Matrix (ι q) ρ S),
        C q (q + 1) = L * M ∧ L' * L = 1 ∧ M * M' = 1 := by
    have h' : ((C q (q + 1)).map ψ).rank + ((C (q + 1) (q + 1 + 1)).map ψ).rank =
        Fintype.card (ι (q + 1)) := by
      have := h
      simp only [P, if_neg hq, add_zero] at this
      rwa [show q + 1 - 1 = q by omega] at this
    obtain ⟨L, M, L', M', -, -, -, -, hs, -, -⟩ :=
      exists_split_of_rank_map_add_eq ψ hψ _ _ (hC _ _ _) h'
    exact ⟨_, inferInstance, inferInstance, L, M, L', M', hs⟩

  have step (q : ℤ) (hq : q ≠ i) (hq' : q + 1 ≠ i) (h : P (q + 1)) : P q := by
    obtain ⟨ρ, _, _, L, M, L', M', hs⟩ := split q hq' h
    have := rank_map_add_rank_map_eq_of_exact ψ (C (q - 1) q) (C q (q + 1)) (hC _ _ _) hs
      (fun K hK ↦ hex q hq _ K hK)
    simp only [P, if_neg hq, add_zero]
    exact this

  have stepi (h : P (i + 1)) : P i ∧ P (i - 1) := by
    obtain ⟨ρ, _, _, L, M, L', M', hs⟩ := split i (by omega) h
    set A := fromCols (C (i - 1) i) D with hA
    have hBA : C i (i + 1) * A = 0 := by
      rw [hA, mul_fromCols, hC, hD, fromCols_zero]
    have r₁ := rank_map_add_rank_map_eq_of_exact ψ A (C i (i + 1)) hBA hs (fun K hK ↦ by
      obtain ⟨V, V', hV⟩ := ha K hK
      exact ⟨fromRows V V', by rw [hA, fromCols_mul_fromRows, hV]⟩)
    obtain ⟨L₁, M₁, L₁', M₁', -, -, -, -, hs₁, -, -⟩ :=
      exists_split_of_rank_map_add_eq ψ hψ _ _ hBA r₁
    set A' := fromRows (C (i - 1 - 1) (i - 1)) (0 : Matrix κ (ι (i - 1 - 1)) S) with hA'
    have hAA' : A * A' = 0 := by
      rw [hA, hA', fromCols_mul_fromRows, hC, Matrix.mul_zero, add_zero]
    have r₂ := rank_map_add_rank_map_eq_of_exact ψ A' A hAA' ⟨hs₁.1, hs₁.2.1, hs₁.2.2⟩
      (fun K hK ↦ by
        rw [← fromRows_toRows K, hA, fromCols_mul_fromRows] at hK
        have h₂ := hb _ _ hK
        rw [h₂, Matrix.mul_zero, add_zero] at hK
        obtain ⟨V, hV⟩ := hex (i - 1) (by omega) _ K.toRows₁ (by
          rw [show i - 1 + 1 = i by omega]
          exact hK)
        refine ⟨V, ?_⟩
        rw [hA', fromRows_mul, hV, Matrix.zero_mul, ← h₂, fromRows_toRows])
    have e₁ : (A'.map ψ).rank = ((C (i - 1 - 1) (i - 1)).map ψ).rank := by
      rw [hA', fromRows_map, Matrix.map_zero _ (map_zero ψ), rank_fromRows_zero]
    have e₂ : (A.map ψ).rank ≤ ((C (i - 1) i).map ψ).rank + Fintype.card κ := by
      rw [hA, fromCols_map]
      exact rank_fromCols_le _ _
    have e₃ := rank_add_rank_le_of_mul_eq_zero ((C (i - 1 - 1) (i - 1)).map ψ)
      ((C (i - 1) i).map ψ) (by rw [← Matrix.map_mul, hC, Matrix.map_zero _ (map_zero ψ)])
    rw [Fintype.card_sum] at r₂
    constructor
    · change _ + _ + (if i = i then _ else _) = _
      rw [if_pos rfl]
      omega
    · simp only [P, if_neg (show i - 1 ≠ i by omega), add_zero]
      rw [show i - 1 + 1 = i by omega]
      omega

  have top (q : ℤ) (hq : max N i < q) : P q := by
    have := hN q (lt_of_le_of_lt (le_max_left _ _) hq)
    simp only [P, if_neg (show q ≠ i by omega), add_zero, Fintype.card_eq_zero, Nat.add_eq_zero_iff]
    exact ⟨Nat.le_zero.1 ((rank_le_card_height _).trans_eq Fintype.card_eq_zero),
      Nat.le_zero.1 ((rank_le_card_width _).trans_eq Fintype.card_eq_zero)⟩
  have key (n : ℕ) : ∀ q, max N i + 1 - n ≤ q → P q := by
    induction n with
    | zero => exact fun q hq ↦ top q (by omega)
    | succ n ih =>
      intro q hq
      rcases lt_or_eq_of_le hq with hq | rfl
      · exact ih q (by omega)
      by_cases h₁ : max N i + 1 - (n + 1 : ℕ) = i
      · rw [h₁]
        exact (stepi (ih _ (by omega))).1
      by_cases h₂ : max N i + 1 - (n + 1 : ℕ) + 1 = i
      · rw [show max N i + 1 - (n + 1 : ℕ) = i - 1 by omega]
        exact (stepi (ih _ (by omega))).2
      exact step _ h₁ h₂ (ih _ (by omega))
  exact key (max N i + 1 - q).toNat q (by omega)

end Complex

section SplitHomology

variable {R : Type*} [CommRing R] {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]
  [DecidableEq ι₁]

/-- `HasSplitHomology A₁ A₂ k` says that the middle term `R^{ι₁}` of the composable matrices
`A₁ : R^{ι₀} → R^{ι₁}` and `A₂ : R^{ι₁} → R^{ι₂}` is split by matrices `I`, `P` with `P I = 1`,
`A₂ I = 0`, `P A₁ = 0` and `I P + A₁ σ + τ A₂ = 1`: the cohomology is free on `k`, split off by
`I` and `P`. -/
def HasSplitHomology (A₁ : Matrix ι₁ ι₀ R) (A₂ : Matrix ι₂ ι₁ R) (k : Type*) [Fintype k]
    [DecidableEq k] : Prop :=
  ∃ (I : Matrix ι₁ k R) (P : Matrix k ι₁ R) (σ : Matrix ι₀ ι₁ R) (τ : Matrix ι₁ ι₂ R),
    P * I = 1 ∧ A₂ * I = 0 ∧ P * A₁ = 0 ∧ I * P + A₁ * σ + τ * A₂ = 1

variable {A₁ : Matrix ι₁ ι₀ R} {A₂ : Matrix ι₂ ι₁ R} {k : Type*} [Fintype k] [DecidableEq k]

lemma HasSplitHomology.map {S : Type*} [CommRing S] (f : R →+* S)
    (h : HasSplitHomology A₁ A₂ k) : HasSplitHomology (A₁.map f) (A₂.map f) k := by
  obtain ⟨I, P, σ, τ, h₁, h₂, h₃, h₄⟩ := h
  refine ⟨I.map f, P.map f, σ.map f, τ.map f, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, h₁, Matrix.map_one _ (map_zero f) (map_one f)]
  · rw [← Matrix.map_mul, h₂, Matrix.map_zero _ (map_zero f)]
  · rw [← Matrix.map_mul, h₃, Matrix.map_zero _ (map_zero f)]
  · rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add f),
      ← Matrix.map_add _ (map_add f), h₄, Matrix.map_one _ (map_zero f) (map_one f)]

lemma HasSplitHomology.of_equiv {k' : Type*} [Fintype k'] [DecidableEq k'] (e : k ≃ k')
    (h : HasSplitHomology A₁ A₂ k) : HasSplitHomology A₁ A₂ k' := by
  obtain ⟨I, P, σ, τ, h₁, h₂, h₃, h₄⟩ := h
  refine ⟨I.submatrix id e.symm, P.submatrix e.symm id, σ, τ, ?_, ?_, ?_, ?_⟩
  · rw [show P.submatrix e.symm id * I.submatrix id e.symm = (P * I).submatrix e.symm e.symm by
      ext; simp [Matrix.mul_apply], h₁, submatrix_one_equiv]
  · rw [show A₂ * I.submatrix id e.symm = (A₂ * I).submatrix id e.symm by
      ext; simp [Matrix.mul_apply], h₂, submatrix_zero]
    rfl
  · rw [show P.submatrix e.symm id * A₁ = (P * A₁).submatrix e.symm id by
      ext; simp [Matrix.mul_apply], h₃, submatrix_zero]
    rfl
  · rw [show I.submatrix id e.symm * P.submatrix e.symm id = I * P by
      ext a b
      simp only [Matrix.mul_apply, submatrix_apply, id]
      exact Fintype.sum_equiv e.symm _ _ fun _ ↦ rfl, h₄]

/-- Split factorisations of two composable matrices with `L₁ L₁' + M₂' M₂ = 1` exhibit the
middle term as split exact. -/
lemma hasSplitHomology_of_add_eq_one [IsEmpty k] {ρ₁ ρ₂ : Type*} [Fintype ρ₁]
    [Fintype ρ₂] {L₁ : Matrix ι₁ ρ₁ R} {M₁ : Matrix ρ₁ ι₀ R} {L₁' : Matrix ρ₁ ι₁ R}
    {M₁' : Matrix ι₀ ρ₁ R} {L₂ : Matrix ι₂ ρ₂ R} {M₂ : Matrix ρ₂ ι₁ R} {L₂' : Matrix ρ₂ ι₂ R}
    {M₂' : Matrix ι₁ ρ₂ R} [DecidableEq ρ₁] [DecidableEq ρ₂]
    (h₁ : A₁ = L₁ * M₁ ∧ L₁' * L₁ = 1 ∧ M₁ * M₁' = 1)
    (h₂ : A₂ = L₂ * M₂ ∧ L₂' * L₂ = 1 ∧ M₂ * M₂' = 1) (h : L₁ * L₁' + M₂' * M₂ = 1) :
    HasSplitHomology A₁ A₂ k := by
  refine ⟨0, 0, M₁' * L₁', M₂' * L₂', Subsingleton.elim _ _, by simp, by simp, ?_⟩
  rw [Matrix.zero_mul, zero_add, ← h, h₁.1, h₂.1, Matrix.mul_assoc, ← Matrix.mul_assoc M₁,
    h₁.2.2, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.mul_assoc L₂', h₂.2.1, Matrix.one_mul]

/-- Split factorisations of two composable matrices and a split factorisation `ε = L₃ M₃`,
`M₃ L₃ = 1`, of the idempotent `ε = (1 - L₁ L₁') (1 - M₂' M₂)` exhibit the cohomology as free
on `k`. -/
lemma hasSplitHomology_of_splitIdempotent {ρ₁ ρ₂ : Type*} [Fintype ρ₁]
    [Fintype ρ₂] {L₁ : Matrix ι₁ ρ₁ R} {M₁ : Matrix ρ₁ ι₀ R} {L₁' : Matrix ρ₁ ι₁ R}
    {M₁' : Matrix ι₀ ρ₁ R} {L₂ : Matrix ι₂ ρ₂ R} {M₂ : Matrix ρ₂ ι₁ R} {L₂' : Matrix ρ₂ ι₂ R}
    {M₂' : Matrix ι₁ ρ₂ R} [DecidableEq ρ₁] [DecidableEq ρ₂] (hA : A₂ * A₁ = 0)
    (h₁ : A₁ = L₁ * M₁ ∧ L₁' * L₁ = 1 ∧ M₁ * M₁' = 1)
    (h₂ : A₂ = L₂ * M₂ ∧ L₂' * L₂ = 1 ∧ M₂ * M₂' = 1) {L₃ : Matrix ι₁ k R}
    {M₃ : Matrix k ι₁ R} (hε : splitIdempotent L₁ L₁' M₂ M₂' = L₃ * M₃) (h₃ : M₃ * L₃ = 1) :
    HasSplitHomology A₁ A₂ k := by
  obtain ⟨k₁, k₂, k₃⟩ := split_homology_data hA h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2 hε h₃
  exact ⟨L₃, M₃, _, _, h₃, k₁, k₂, k₃⟩

end SplitHomology

section SplitHomologyField

variable {K : Type*} [Field K] {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]
  [DecidableEq ι₁] {A₁ : Matrix ι₁ ι₀ K} {A₂ : Matrix ι₂ ι₁ K} {k : Type*} [Fintype k]
  [DecidableEq k]

/-- Over a field, split cohomology on `k` has dimension `|k|`. -/
lemma HasSplitHomology.rank_add_rank_add_card (hA : A₂ * A₁ = 0)
    (h : HasSplitHomology A₁ A₂ k) : A₁.rank + A₂.rank + Fintype.card k = Fintype.card ι₁ := by
  obtain ⟨I, P, σ, τ, h₁, h₂, h₃, h₄⟩ := h
  exact rank_add_rank_add_card_eq A₁ A₂ I P σ τ hA h₁ h₂ h₃ h₄

omit [Fintype ι₀] [Fintype ι₂] in
/-- Over a field, the ranks of an idempotent matrix `e` and of `1 - e` add up to the size. -/
lemma rank_add_rank_one_sub {e : Matrix ι₁ ι₁ K} (he : e * e = e) :
    e.rank + (1 - e).rank = Fintype.card ι₁ := by
  refine le_antisymm ?_ ?_
  · exact rank_add_rank_le_of_mul_eq_zero e (1 - e) (by rw [Matrix.sub_mul, he, Matrix.one_mul,
      sub_self])
  · rw [← rank_one (R := K) (n := ι₁)]
    conv_lhs => rw [← add_sub_cancel e (1 : Matrix ι₁ ι₁ K)]
    exact rank_add_le _ _

end SplitHomologyField

end Matrix
