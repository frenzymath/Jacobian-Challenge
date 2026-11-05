import Jacobian.AlgebraicGeometry.ProjectiveSpace.TwistSections

/-!
# Products and restrictions of Laurent monomial functions

Degree-zero Laurent monomials multiply and restrict according to their exponent
vectors on the standard affine intersections of polynomial projective space.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : Type v} [Fintype n] {R : Type (max u v)} [CommRing R] {s : Set n}

/-- The product of two Laurent monomials is the Laurent monomial of the sum of the exponents. -/
lemma awayMonomial_mul (e e' e'' : laurentExponents s 0) (h : e''.1 = e.1 + e'.1) :
    awayMonomial R s e * awayMonomial R s e' = awayMonomial R s e'' := by
  apply HomogeneousLocalization.val_injective
  have h0 := indicator_one_nonneg s
  have ha := add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1)
  have ha' := add_nsmul_indicator_nonneg e'.2.2 (neg_le_negExponentSum e'.1)
  have ha'' := add_nsmul_indicator_nonneg e''.2.2 (neg_le_negExponentSum e''.1)
  rw [HomogeneousLocalization.val_mul, awayMonomial, awayMonomial, awayMonomial, Away.val_mk,
    Away.val_mk, Away.val_mk, Localization.mk_mul]
  refine mk_eq_mk_of_monomialToNat (add_nonneg ha ha')
    (add_nonneg (nsmul_nonneg h0 (negExponentSum e.1)) (nsmul_nonneg h0 (negExponentSum e'.1)))
    ha'' (nsmul_nonneg h0 (negExponentSum e''.1)) (monomialToNat_mul ha ha') ?_ rfl ?_ ?_
  · simp only [Submonoid.coe_mul, monomialToNat_pow h0]
    exact monomialToNat_mul (nsmul_nonneg h0 _) (nsmul_nonneg h0 _)
  · simp only [monomialToNat_pow h0]
  · rw [h]
    abel

/-- The Laurent monomial with exponent `0` is `1`. -/
lemma awayMonomial_zero (e : laurentExponents s 0) (h : e.1 = 0) : awayMonomial R s e = 1 := by
  apply HomogeneousLocalization.val_injective
  have h0 := indicator_one_nonneg s
  rw [HomogeneousLocalization.val_one, awayMonomial, Away.val_mk, ← Localization.mk_one]
  refine mk_eq_mk_of_monomialToNat (add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1))
    (nsmul_nonneg h0 (negExponentSum e.1)) le_rfl le_rfl rfl ?_ monomialToNat_zero.symm
    monomialToNat_zero.symm ?_
  · simp only [monomialToNat_pow h0]
  · rw [h]
    simp

/-- The `m`-th power of a Laurent monomial is the Laurent monomial of `m` times the exponent. -/
lemma awayMonomial_pow (e : laurentExponents s 0) (m : ℕ) (e' : laurentExponents s 0)
    (h : e'.1 = m • e.1) : awayMonomial R s e' = awayMonomial R s e ^ m := by
  induction m generalizing e' with
  | zero => exact (awayMonomial_zero (R := R) e' (by simpa using h)).trans (pow_zero _).symm
  | succ m ih =>
    let e₀ : laurentExponents s 0 := ⟨m • e.1, by
      simp only [Pi.smul_apply, nsmul_eq_mul, ← Finset.mul_sum, e.2.1, mul_zero], fun i hi ↦
      nsmul_nonneg (e.2.2 i hi) m⟩
    rw [pow_succ, ← ih e₀ rfl, awayMonomial_mul e₀ e e' (by rw [h, succ_nsmul])]

private lemma awayToSection_awayMonomial_restriction_val {t : Set n} (hts : t ⊆ s)
    (e : laurentExponents t 0)
    (point : Proj.basicOpen (homogeneousSubmodule n R)
      (monomialToNat R (s.indicator 1))) :
    ((Proj.awayToSection _ _ (awayMonomial R t e)).1
        ⟨point.1, basicOpen_monomialToNat_indicator_mono (R := R) hts point.2⟩).val =
      ((Proj.awayToSection _ _
        (awayMonomial R s ⟨e.1, e.2.1, fun i hi ↦ e.2.2 i fun h ↦ hi (hts h)⟩)).1
          point).val := by
  rw [val_awayToSection_awayMonomial_apply, val_awayToSection_awayMonomial_apply]
  have h0 := indicator_one_nonneg s
  have h0' := indicator_one_nonneg t
  refine mk_monomialToNat_eq_mk (add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1))
    (nsmul_nonneg h0' _) (add_nsmul_indicator_nonneg (fun i hi ↦ e.2.2 i fun h ↦ hi (hts h))
      (neg_le_negExponentSum e.1)) (nsmul_nonneg h0 _) ?_ _ _
  abel

/-- The function `xᵉ` on `D₊(∏_{i ∈ t} Xᵢ)` restricts to the function `xᵉ` on the smaller open
`D₊(∏_{i ∈ s} Xᵢ)`, for `t ⊆ s`. -/
lemma presheaf_map_awayToSection_awayMonomial {t : Set n} (hts : t ⊆ s)
    (e : laurentExponents t 0) :
    (Proj (homogeneousSubmodule n R)).presheaf.map
        (homOfLE (basicOpen_monomialToNat_indicator_mono (R := R) hts)).op
        (Proj.awayToSection _ _ (awayMonomial R t e)) =
      Proj.awayToSection _ _
        (awayMonomial R s ⟨e.1, e.2.1, fun i hi ↦ e.2.2 i fun h ↦ hi (hts h)⟩) := by
  apply Subtype.ext
  funext point
  apply HomogeneousLocalization.val_injective
  exact awayToSection_awayMonomial_restriction_val hts e point

end AlgebraicGeometry.Proj
