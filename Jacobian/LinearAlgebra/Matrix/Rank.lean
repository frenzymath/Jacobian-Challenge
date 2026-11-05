import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrix rank detected by minors

The rank of a finite matrix over a field is detected by its nonzero minors. After a ring homomorphism to a field, the same criterion uses the images of the original determinants.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Module

namespace Matrix

variable {K : Type*} [Field K] {m n : Type*} [Fintype n]

/-- A matrix of rank at least `r` over a field has `r` linearly independent columns. -/
theorem exists_linearIndependent_col_of_le_rank (A : Matrix m n K) {r : ℕ} (h : r ≤ A.rank) :
    ∃ e : Fin r → n, LinearIndependent K fun i ↦ A.col (e i) := by
  classical
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (Set.range A.col)
  have : Fintype b := ((Set.finite_range _).subset hb).fintype
  have hcard : Fintype.card b = A.rank := by
    rw [rank_eq_finrank_span_cols, ← hspan, finrank_span_set_eq_card hli, Set.toFinset_card]
  let φ : Fin r → b := fun i ↦ (Fintype.equivFin b).symm (Fin.castLE (hcard ▸ h) i)
  have hφ : Function.Injective φ :=
    (Fintype.equivFin b).symm.injective.comp (Fin.castLE_injective _)
  choose e he using fun i ↦ hb (φ i).2
  refine ⟨e, ?_⟩
  simp_rw [he]
  exact hli.comp φ hφ

/-- A matrix of rank at least `r` over a field has a nonvanishing `r × r` minor. -/
theorem exists_submatrix_det_ne_zero_of_le_rank [Finite m] (A : Matrix m n K) {r : ℕ}
    (h : r ≤ A.rank) : ∃ (e₁ : Fin r → m) (e₂ : Fin r → n), (A.submatrix e₁ e₂).det ≠ 0 := by
  have := Fintype.ofFinite m
  obtain ⟨e₂, h₂⟩ := A.exists_linearIndependent_col_of_le_rank h
  have hB : r ≤ (A.submatrix id e₂)ᵀ.rank := by
    have hc : (A.submatrix id e₂).col = fun i ↦ A.col (e₂ i) := rfl
    rw [rank_transpose, rank_eq_finrank_span_cols, hc, finrank_span_eq_card h₂, Fintype.card_fin]
  obtain ⟨e₁, h₁⟩ := (A.submatrix id e₂)ᵀ.exists_linearIndependent_col_of_le_rank hB
  exact ⟨e₁, e₂, ((isUnit_iff_isUnit_det _).1 (linearIndependent_rows_iff_isUnit.1 h₁)).ne_zero⟩

/-- A matrix over a field with a nonvanishing `r × r` minor has rank at least `r`. -/
theorem le_rank_of_submatrix_det_ne_zero (A : Matrix m n K) {r : ℕ} (e₁ : Fin r → m)
    (e₂ : Fin r → n) (h : (A.submatrix e₁ e₂).det ≠ 0) : r ≤ A.rank := by
  have := rank_of_det_ne_zero h
  rw [Fintype.card_fin] at this
  exact this ▸ rank_submatrix_le A e₁ e₂

/-- The image of a matrix `A` over a ring in a field `K` has rank at least `r` if and only if some
`r × r` minor of `A` is not killed by the ring homomorphism `ψ` to `K`. -/
theorem le_rank_map_iff [Finite m] {R : Type*} [CommRing R] (A : Matrix m n R) (ψ : R →+* K)
    (r : ℕ) :
    r ≤ (A.map ψ).rank ↔ ∃ (e₁ : Fin r → m) (e₂ : Fin r → n), ψ (A.submatrix e₁ e₂).det ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨e₁, e₂, h⟩ ↦ le_rank_of_submatrix_det_ne_zero _ e₁ e₂ ?_⟩
  · obtain ⟨e₁, e₂, h⟩ := exists_submatrix_det_ne_zero_of_le_rank _ h
    exact ⟨e₁, e₂, by rwa [RingHom.map_det]⟩
  · rwa [RingHom.map_det] at h

end Matrix
