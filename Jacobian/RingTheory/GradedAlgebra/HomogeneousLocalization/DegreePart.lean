import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Homogeneous degree parts of a localization

The degree parts of a localization of an `ℕ`-graded ring are modules over its
homogeneous localization. They form a `ℤ`-graded multiplicative family, whose
zeroth part is canonically the homogeneous localization itself.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HomogeneousLocalization

section DegreePart

variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (x : Submonoid A)

/-- `y` is a homogeneous fraction of degree `m` in `Localization x`: it is `a / b` with `a` of
degree `i`, `b ∈ x` of degree `j`, and `i = j + m`. -/
def IsFractionOfDegree (m : ℤ) (y : Localization x) : Prop :=
  ∃ (i j : ℕ) (a b : A) (hb : b ∈ x), a ∈ 𝒜 i ∧ b ∈ 𝒜 j ∧ (i : ℤ) = j + m ∧
    y = Localization.mk a ⟨b, hb⟩

variable {𝒜 x} in
lemma IsFractionOfDegree.mul {m n : ℤ} {y z : Localization x}
    (hy : IsFractionOfDegree 𝒜 x m y) (hz : IsFractionOfDegree 𝒜 x n z) :
    IsFractionOfDegree 𝒜 x (m + n) (y * z) := by
  obtain ⟨i, j, a, b, hb, ha, hb', hij, rfl⟩ := hy
  obtain ⟨i', j', a', b', hb₂, ha', hb₂', hij', rfl⟩ := hz
  exact ⟨i + i', j + j', a * a', b * b', mul_mem hb hb₂, SetLike.mul_mem_graded ha ha',
    SetLike.mul_mem_graded hb' hb₂', by omega, Localization.mk_mul _ _ _ _⟩

variable {𝒜 x} in
lemma IsFractionOfDegree.add {m : ℤ} {y z : Localization x}
    (hy : IsFractionOfDegree 𝒜 x m y) (hz : IsFractionOfDegree 𝒜 x m z) :
    IsFractionOfDegree 𝒜 x m (y + z) := by
  obtain ⟨i, j, a, b, hb, ha, hb', hij, rfl⟩ := hy
  obtain ⟨i', j', a', b', hb₂, ha', hb₂', hij', rfl⟩ := hz
  have h : j + i' = j' + i := by omega
  exact ⟨j + i', j + j', b * a' + b' * a, b * b', mul_mem hb hb₂,
    add_mem (SetLike.mul_mem_graded hb' ha') (h ▸ SetLike.mul_mem_graded hb₂' ha),
    SetLike.mul_mem_graded hb' hb₂', by omega, Localization.add_mk _ _ _ _⟩

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
variable {𝒜 x} in
/-- The value of an element of the homogeneous localization is a fraction of degree `0`. -/
lemma isFractionOfDegree_val (p : HomogeneousLocalization 𝒜 x) :
    IsFractionOfDegree 𝒜 x 0 p.val :=
  ⟨p.deg, p.deg, p.num, p.den, p.den_mem, p.num_mem_deg, p.den_mem_deg, by simp,
    p.eq_num_div_den⟩

/-- The degree-`m` part of the localization `Localization x` of a graded ring, for `m : ℤ`: the
fractions `a / b` with `a ∈ 𝒜 i`, `b ∈ x ∩ 𝒜 j` and `i = j + m` (together with `0`, which need
not be such a fraction when `m < 0` and `x` has no elements of degree `-m`).

It is a module over the degree-`0` part `HomogeneousLocalization 𝒜 x`, acting on
`Localization x` through `homogeneousLocalizationAlgebra`. For `m = 0` it is the image of
`HomogeneousLocalization.val` (`HomogeneousLocalization.degreePart_zero`), and the
twisting sheaves `𝒪(m)` on `Proj 𝒜` are built from `degreePart 𝒜 x m` at the points `x`.

We restrict to `ℕ`-graded rings, the case needed for `Proj`; the definition works verbatim for a
grading by an additive group `ι`, with `m : ι`. -/
def degreePart (m : ℤ) : Submodule (HomogeneousLocalization 𝒜 x) (Localization x) where
  carrier := {y | y = 0 ∨ IsFractionOfDegree 𝒜 x m y}
  zero_mem' := .inl rfl
  add_mem' := by
    rintro y z (rfl | hy) (rfl | hz)
    · exact .inl (add_zero 0)
    · exact .inr (by rwa [zero_add])
    · exact .inr (by rwa [add_zero])
    · exact .inr (hy.add hz)
  smul_mem' := by
    rintro p y (rfl | hy)
    · exact .inl (smul_zero p)
    · exact .inr (zero_add m ▸ (isFractionOfDegree_val p).mul hy)

variable {𝒜 x}

lemma mem_degreePart {m : ℤ} {y : Localization x} :
    y ∈ degreePart 𝒜 x m ↔ y = 0 ∨ IsFractionOfDegree 𝒜 x m y :=
  Iff.rfl

/-- Multiplication maps the degree-`m` part times the degree-`n` part into the
degree-`(m + n)` part. -/
lemma mul_mem_degreePart {m n : ℤ} {y z : Localization x} (hy : y ∈ degreePart 𝒜 x m)
    (hz : z ∈ degreePart 𝒜 x n) : y * z ∈ degreePart 𝒜 x (m + n) := by
  obtain rfl | hy := hy
  · exact .inl (zero_mul z)
  obtain rfl | hz := hz
  · exact .inl (mul_zero y)
  exact .inr (hy.mul hz)

lemma val_mem_degreePart_zero (p : HomogeneousLocalization 𝒜 x) : p.val ∈ degreePart 𝒜 x 0 :=
  .inr (isFractionOfDegree_val p)

lemma one_mem_degreePart : (1 : Localization x) ∈ degreePart 𝒜 x 0 := by
  simpa using val_mem_degreePart_zero (1 : HomogeneousLocalization 𝒜 x)

/-- The degree parts of `Localization x` form a `ℤ`-graded monoid. -/
instance : SetLike.GradedMonoid (degreePart 𝒜 x) where
  one_mem := one_mem_degreePart
  mul_mem _ _ _ _ := mul_mem_degreePart

/-- The fraction `a / b` as an element of the degree-`m` part, for `a ∈ 𝒜 i`, `b ∈ x ∩ 𝒜 j`
and `i = j + m`. -/
def degreePart.mk {m : ℤ} {i j : ℕ} (a : 𝒜 i) (b : 𝒜 j) (hb : (b : A) ∈ x)
    (h : (i : ℤ) = j + m) : degreePart 𝒜 x m :=
  ⟨Localization.mk a ⟨b, hb⟩, .inr ⟨i, j, a, b, hb, a.2, b.2, h, rfl⟩⟩

@[simp]
lemma degreePart.coe_mk {m : ℤ} {i j : ℕ} (a : 𝒜 i) (b : 𝒜 j) (hb : (b : A) ∈ x)
    (h : (i : ℤ) = j + m) :
    (degreePart.mk a b hb h : Localization x) = Localization.mk (a : A) ⟨b, hb⟩ :=
  rfl

/-- The degree-`0` part of `Localization x` is the image of `HomogeneousLocalization 𝒜 x`. -/
lemma degreePart_zero : degreePart 𝒜 x 0 = 1 := by
  ext y
  rw [Submodule.mem_one]
  refine ⟨?_, ?_⟩
  · rintro (rfl | ⟨i, j, a, b, hb, ha, hb', h, rfl⟩)
    · exact ⟨0, map_zero _⟩
    · obtain rfl : i = j := by omega
      exact ⟨mk ⟨i, ⟨a, ha⟩, ⟨b, hb'⟩, hb⟩, val_mk _⟩
  · rintro ⟨p, rfl⟩
    exact val_mem_degreePart_zero p

/-- The degree-`0` part of `Localization x` is `HomogeneousLocalization 𝒜 x` itself, as a module
over it. -/
noncomputable def degreePart.zeroEquiv :
    HomogeneousLocalization 𝒜 x ≃ₗ[HomogeneousLocalization 𝒜 x] degreePart 𝒜 x 0 :=
  (LinearEquiv.ofInjective (Algebra.linearMap (HomogeneousLocalization 𝒜 x) (Localization x))
    (val_injective x)).trans
    (LinearEquiv.ofEq _ _ (Submodule.one_eq_range.symm.trans degreePart_zero.symm))

@[simp]
lemma degreePart.coe_zeroEquiv_apply (p : HomogeneousLocalization 𝒜 x) :
    (degreePart.zeroEquiv p : Localization x) = p.val :=
  rfl

end DegreePart

end HomogeneousLocalization
