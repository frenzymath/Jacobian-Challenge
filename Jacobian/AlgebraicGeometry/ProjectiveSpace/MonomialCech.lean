import Jacobian.Algebra.Homology.CochainComplex.ModuleCat
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homology of the monomial Čech complex

For a finite set of coordinates and a prescribed total degree, the monomial
Čech complex consists of finitely supported functions on Laurent exponent
vectors, indexed by ordered tuples of coordinates. Its differential is the
alternating sum of the restriction maps.

Inserting a coordinate with nonnegative exponent defines a contracting homotopy
in positive degrees. With `d + 1` coordinates, the intermediate homology groups
vanish, degree-zero homology is the space of homogeneous polynomials in
nonnegative total degree, and top homology is free on the strictly negative
exponent vectors, except when `d = 0` and `m ≥ 0`: top homology is then the
degree-zero polynomial module instead. Consequently its homology is finite
over the coefficient ring in degrees at most `d`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

variable (n : Type v) [Fintype n] (A : Type (max u v)) [CommRing A] (m : ℤ)

/-- The exponent vectors of the Laurent monomials of degree `m` that are sections of `𝒪(m)`
over the intersection `U_{σ 0} ∩ ⋯ ∩ U_{σ p}` of standard opens: those with `∑ eᵢ = m` and
`eᵢ ≥ 0` for every `i` not in the range of `σ`. -/
def monomialCechSupport {p : ℕ} (σ : Fin (p + 1) → n) : Set (n → ℤ) :=
  {e | ∑ i, e i = m ∧ ∀ i, i ∉ Set.range σ → 0 ≤ e i}

variable {n m} in
lemma monomialCechSupport_mono {p q : ℕ} (σ : Fin (p + 1) → n) (θ : Fin (q + 1) → Fin (p + 1)) :
    monomialCechSupport n m (σ ∘ θ) ⊆ monomialCechSupport n m σ :=
  fun _ ⟨he, he'⟩ ↦ ⟨he, fun i hi ↦ he' i fun ⟨a, ha⟩ ↦ hi ⟨θ a, ha⟩⟩

/-- The monomial Čech cochains of degree `p`: families, indexed by the tuples
`σ : Fin (p + 1) → n`, of sections of `𝒪(m)` over `U_{σ 0} ∩ ⋯ ∩ U_{σ p}`, each written as
a finitely supported function on the exponent vectors of its Laurent monomials. -/
abbrev MonomialCechCochain (p : ℕ) : Type (max u v) :=
  ∀ σ : Fin (p + 1) → n, Finsupp.supported A A (monomialCechSupport n m σ)

/-- The face and degeneracy maps of the monomial Čech complex: a map `θ` of the simplex
category acts on cochains by `c ↦ (σ ↦ c (σ ∘ θ))`, a Laurent polynomial on a bigger
intersection being restricted to a smaller one by the identity. -/
@[simps]
def monomialCechCochainMap {p q : ℕ} (θ : Fin (q + 1) → Fin (p + 1)) :
    MonomialCechCochain n A m q →ₗ[A] MonomialCechCochain n A m p where
  toFun c σ := ⟨c (σ ∘ θ), Finsupp.supported_mono (monomialCechSupport_mono σ θ) (c _).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The monomial Čech cosimplicial module. In degree `p` it is `MonomialCechCochain n A m p`,
and a map `θ` of the simplex category acts by `monomialCechCochainMap`. -/
@[simps]
def monomialCechCosimplicialObject : CosimplicialObject (ModuleCat.{max u v} A) where
  obj k := ModuleCat.of A (MonomialCechCochain n A m k.len)
  map θ := ModuleCat.ofHom (monomialCechCochainMap n A m θ.toOrderHom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The monomial Čech complex** of `𝒪(m)` on the standard covering of `ℙ = Proj A[xᵢ]`: the
alternating coface map complex of `monomialCechCosimplicialObject n A m`. Its differential is
`(d c) σ = ∑ i, (-1) ^ i • c (σ ∘ Fin.succAbove i)` (`monomialCechComplex_d_apply`). -/
def monomialCechComplex : CochainComplex (ModuleCat.{max u v} A) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{max u v} A)).obj
    (monomialCechCosimplicialObject n A m)

variable {n A m}

/-- The coefficient of the Laurent monomial `xᵉ` in the component `c σ` of a cochain. -/
abbrev MonomialCechCochain.coeff {p : ℕ} (c : MonomialCechCochain n A m p)
    (σ : Fin (p + 1) → n) (e : n → ℤ) : A :=
  (c σ : (n → ℤ) →₀ A) e

lemma MonomialCechCochain.ext_coeff {p : ℕ} {c c' : MonomialCechCochain n A m p}
    (h : ∀ σ e, c.coeff σ e = c'.coeff σ e) : c = c' :=
  funext fun σ ↦ Subtype.ext (Finsupp.ext (h σ))

@[simp]
lemma MonomialCechCochain.coeff_zero {p : ℕ} (σ : Fin (p + 1) → n) (e : n → ℤ) :
    MonomialCechCochain.coeff (A := A) (m := m) 0 σ e = 0 :=
  rfl

@[simp]
lemma MonomialCechCochain.coeff_add {p : ℕ} (c c' : MonomialCechCochain n A m p)
    (σ : Fin (p + 1) → n) (e : n → ℤ) : (c + c').coeff σ e = c.coeff σ e + c'.coeff σ e :=
  rfl

@[simp]
lemma MonomialCechCochain.coeff_sub {p : ℕ} (c c' : MonomialCechCochain n A m p)
    (σ : Fin (p + 1) → n) (e : n → ℤ) : (c - c').coeff σ e = c.coeff σ e - c'.coeff σ e :=
  rfl

@[simp]
lemma MonomialCechCochain.coeff_smul {p : ℕ} (a : A) (c : MonomialCechCochain n A m p)
    (σ : Fin (p + 1) → n) (e : n → ℤ) : (a • c).coeff σ e = a * c.coeff σ e :=
  rfl

lemma MonomialCechCochain.coeff_eq_zero_of_notMem {p : ℕ} (c : MonomialCechCochain n A m p)
    (σ : Fin (p + 1) → n) {e : n → ℤ} (he : e ∉ monomialCechSupport n m σ) : c.coeff σ e = 0 :=
  Finsupp.notMem_support_iff.mp fun h ↦ he ((c σ).2 h)

/-- The coefficient of `xᵉ` in a component of a cochain vanishes unless `e` is nonnegative
outside the range of the tuple. -/
lemma MonomialCechCochain.coeff_eq_zero_of_neg {p : ℕ} (c : MonomialCechCochain n A m p)
    (σ : Fin (p + 1) → n) {e : n → ℤ} {i : n} (hi : i ∉ Set.range σ) (he : e i < 0) :
    c.coeff σ e = 0 :=
  c.coeff_eq_zero_of_notMem σ fun h ↦ (h.2 i hi).not_gt he

/-- The coefficient of `xᵉ` in a component of a cochain vanishes unless `∑ eᵢ = m`. -/
lemma MonomialCechCochain.coeff_eq_zero_of_sum_ne {p : ℕ} (c : MonomialCechCochain n A m p)
    (σ : Fin (p + 1) → n) {e : n → ℤ} (he : ∑ i, e i ≠ m) : c.coeff σ e = 0 :=
  c.coeff_eq_zero_of_notMem σ fun h ↦ he h.1

/-- The differential of the monomial Čech complex is the alternating sum of the faces. -/
lemma monomialCechComplex_d_apply (p : ℕ) (c : MonomialCechCochain n A m p)
    (σ : Fin (p + 2) → n) (e : n → ℤ) :
    MonomialCechCochain.coeff (m := m) ((monomialCechComplex n A m).d p (p + 1) c) σ e =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • c.coeff (σ ∘ i.succAbove) e := by
  have h : (monomialCechComplex n A m).d p (p + 1) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (monomialCechCosimplicialObject n A m).δ i :=
    CochainComplex.of_d _ (AlgebraicTopology.AlternatingCofaceMapComplex.objD _) p
  rw [h]
  change ((∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
    (monomialCechCosimplicialObject n A m).δ i).hom c σ : (n → ℤ) →₀ A) e = _
  rw [ModuleCat.hom_sum, LinearMap.sum_apply, Finset.sum_apply,
    Submodule.coe_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ModuleCat.hom_zsmul, LinearMap.smul_apply, Pi.smul_apply]
  rfl

/-! ### The contracting homotopy -/

/-- Deleting the entry `i + 1` of `Fin.cons r σ` is the same as deleting the entry `i` of
`σ`. -/
private lemma cons_comp_succ_succAbove {α : Type*} {p : ℕ} (r : α) (σ : Fin (p + 1) → α)
    (i : Fin (p + 1)) :
    (Fin.cons r σ : Fin (p + 2) → α) ∘ i.succ.succAbove = Fin.cons r (σ ∘ i.succAbove) := by
  funext l
  cases l using Fin.cases <;> simp

private lemma cons_comp_zero_succAbove {α : Type*} {p : ℕ} (r : α) (σ : Fin (p + 1) → α) :
    (Fin.cons r σ : Fin (p + 2) → α) ∘ (0 : Fin (p + 2)).succAbove = σ := by
  funext l
  simp

/-- The coefficients of the contracting homotopy: for an exponent vector `e` with a
nonnegative coordinate `r`, the coefficient of `xᵉ` in `(h c) σ` is that in `c (Fin.cons r σ)`;
it is zero for the other exponent vectors. -/
def monomialCechHomotopyCoeff {p : ℕ} (c : MonomialCechCochain n A m (p + 1))
    (σ : Fin (p + 1) → n) (e : n → ℤ) : A :=
  if h : ∃ i, 0 ≤ e i then c.coeff (Fin.cons h.choose σ) e else 0

lemma monomialCechHomotopyCoeff_mem_support {p : ℕ} (c : MonomialCechCochain n A m (p + 1))
    (σ : Fin (p + 1) → n) (e : n → ℤ) (he : monomialCechHomotopyCoeff c σ e ≠ 0) :
    e ∈ Finset.univ.biUnion fun j ↦ (c (Fin.cons j σ) : (n → ℤ) →₀ A).support := by
  unfold monomialCechHomotopyCoeff at he
  split_ifs at he with h
  · exact Finset.mem_biUnion.2 ⟨h.choose, Finset.mem_univ _, Finsupp.mem_support_iff.2 he⟩
  · exact absurd rfl he

lemma monomialCechHomotopyCoeff_support {p : ℕ} (c : MonomialCechCochain n A m (p + 1))
    (σ : Fin (p + 1) → n) (e : n → ℤ) (he : monomialCechHomotopyCoeff c σ e ≠ 0) :
    e ∈ monomialCechSupport n m σ := by
  unfold monomialCechHomotopyCoeff at he
  split_ifs at he with h
  swap
  · exact absurd rfl he
  obtain ⟨hs, hr⟩ := (c (Fin.cons h.choose σ)).2 (Finsupp.mem_support_iff.2 he)
  refine ⟨hs, fun i hi ↦ ?_⟩
  by_cases hir : i = h.choose
  · exact hir ▸ h.choose_spec
  · refine hr i ?_
    rw [Fin.range_cons]
    exact fun h' ↦ (Set.mem_insert_iff.1 h').elim hir hi

/-- **The contracting homotopy** of the monomial Čech complex in positive degrees: on the
summand of an exponent vector `e` with a nonnegative coordinate `r`, it inserts `r` in the
first slot, `(h c) σ = c (Fin.cons r σ)`. -/
def monomialCechHomotopy (p : ℕ) :
    MonomialCechCochain n A m (p + 1) →ₗ[A] MonomialCechCochain n A m p where
  toFun c σ := ⟨Finsupp.onFinset _ (monomialCechHomotopyCoeff c σ)
      (monomialCechHomotopyCoeff_mem_support c σ), fun e he ↦
    monomialCechHomotopyCoeff_support c σ e (by
      rwa [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.onFinset_apply] at he)⟩
  map_add' c c' := MonomialCechCochain.ext_coeff fun σ e ↦ by
    change monomialCechHomotopyCoeff (c + c') σ e =
      monomialCechHomotopyCoeff c σ e + monomialCechHomotopyCoeff c' σ e
    unfold monomialCechHomotopyCoeff
    split_ifs <;> first | rfl | simp
  map_smul' a c := MonomialCechCochain.ext_coeff fun σ e ↦ by
    change monomialCechHomotopyCoeff (a • c) σ e = a • monomialCechHomotopyCoeff c σ e
    unfold monomialCechHomotopyCoeff
    split_ifs <;> first | rfl | simp

lemma monomialCechHomotopy_coeff {p : ℕ} (c : MonomialCechCochain n A m (p + 1))
    (σ : Fin (p + 1) → n) (e : n → ℤ) :
    (monomialCechHomotopy p c).coeff σ e = monomialCechHomotopyCoeff c σ e :=
  rfl

lemma monomialCechHomotopy_coeff_of_exists {p : ℕ} (c : MonomialCechCochain n A m (p + 1))
    (σ : Fin (p + 1) → n) {e : n → ℤ} (he : ∃ i, 0 ≤ e i) :
    (monomialCechHomotopy p c).coeff σ e = c.coeff (Fin.cons he.choose σ) e := by
  rw [monomialCechHomotopy_coeff, monomialCechHomotopyCoeff, dif_pos he]

lemma monomialCechHomotopy_coeff_of_forall {p : ℕ} (c : MonomialCechCochain n A m (p + 1))
    (σ : Fin (p + 1) → n) {e : n → ℤ} (he : ∀ i, e i < 0) :
    (monomialCechHomotopy p c).coeff σ e = 0 := by
  rw [monomialCechHomotopy_coeff, monomialCechHomotopyCoeff,
    dif_neg fun ⟨i, hi⟩ ↦ (he i).not_ge hi]

/-- **The homotopy identity** `d h + h d = 1` in positive degrees, on the summand of an exponent
vector with a nonnegative coordinate. -/
lemma monomialCechComplex_d_homotopy_add (p : ℕ) (c : MonomialCechCochain n A m (p + 1))
    (σ : Fin (p + 2) → n) {e : n → ℤ} (he : ∃ i, 0 ≤ e i) :
    MonomialCechCochain.coeff (m := m)
        ((monomialCechComplex n A m).d p (p + 1) (monomialCechHomotopy p c)) σ e +
      (monomialCechHomotopy (p + 1)
        ((monomialCechComplex n A m).d (p + 1) (p + 2) c)).coeff σ e = c.coeff σ e := by
  rw [monomialCechHomotopy_coeff_of_exists _ _ he, monomialCechComplex_d_apply,
    monomialCechComplex_d_apply, Fin.sum_univ_succ (n := p + 2), Fin.val_zero, pow_zero, one_smul,
    cons_comp_zero_succAbove]
  simp only [monomialCechHomotopy_coeff_of_exists _ _ he, cons_comp_succ_succAbove, Fin.val_succ,
    pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib]
  abel

/-- A tuple `Fin (p + 1) → n` with `p + 1` less than the number of coordinates misses some
coordinate. -/
private lemma exists_notMem_range_of_lt {p : ℕ} (σ : Fin (p + 1) → n)
    (h : p + 1 < Fintype.card n) :
    ∃ i, i ∉ Set.range σ := by
  by_contra! h'
  have := Fintype.card_le_of_surjective σ fun i ↦ h' i
  simp only [Fintype.card_fin] at this
  omega

variable (n A m) in
/-- **The monomial Čech complex is exact in the middle degrees**: with `d + 1` coordinates, it
is exact in every degree `q` with `0 < q < d`. On the summand of an exponent vector with a
nonnegative coordinate this is the contracting homotopy `monomialCechHomotopy`; the summands of
the strictly negative exponent vectors vanish below degree `d`. -/
theorem exactAt_monomialCechComplex {d : ℕ} (hn : Fintype.card n = d + 1) (q : ℕ)
    (hq : q + 1 < d) : (monomialCechComplex n A m).ExactAt (q + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro c hc
  refine ⟨monomialCechHomotopy q c,
    MonomialCechCochain.ext_coeff fun (σ : Fin (q + 2) → n) e ↦ ?_⟩
  change MonomialCechCochain.coeff (m := m)
    ((monomialCechComplex n A m).d q (q + 1) (monomialCechHomotopy q c)) σ e = c.coeff σ e
  by_cases he : ∃ i, 0 ≤ e i
  · have hc' : (monomialCechComplex n A m).d (q + 1) (q + 2) c = 0 := hc
    rw [← monomialCechComplex_d_homotopy_add q c σ he, hc', map_zero]
    exact (add_zero _).symm
  · push Not at he
    obtain ⟨i, hi⟩ := exists_notMem_range_of_lt σ (by omega)
    rw [c.coeff_eq_zero_of_neg σ hi (he i), monomialCechComplex_d_apply]
    simp [monomialCechHomotopy_coeff_of_forall _ _ he]

/-! ### Degree zero -/

variable (n m) in
/-- The exponent vectors of the monomials of degree `m`: the nonnegative ones of sum `m`. -/
def monomialExponents : Set (n → ℤ) :=
  {e | ∑ i, e i = m ∧ ∀ i, 0 ≤ e i}

lemma monomialExponents_subset {p : ℕ} (σ : Fin (p + 1) → n) :
    monomialExponents n m ⊆ monomialCechSupport n m σ :=
  fun _ he ↦ ⟨he.1, fun i _ ↦ he.2 i⟩

/-- The tuple `Fin 1 → n` with value `i`. -/
abbrev monomialCechVertex (i : n) : Fin 1 → n := fun _ ↦ i

/-- A `0`-cocycle has the same component on all the standard opens. -/
lemma monomialCech_cocycle_zero {c : MonomialCechCochain n A m 0}
    (hc : (monomialCechComplex n A m).d 0 1 c = 0) (i j : n) :
    (c (monomialCechVertex i) : (n → ℤ) →₀ A) = c (monomialCechVertex j) := by
  refine Finsupp.ext fun e ↦ ?_
  have h := congrArg (fun c' ↦ MonomialCechCochain.coeff (m := m) c'
    (Fin.cons j (monomialCechVertex i)) e) hc
  simp only at h
  rw [monomialCechComplex_d_apply, Fin.sum_univ_two, cons_comp_zero_succAbove] at h
  have h1 : (Fin.cons j (monomialCechVertex i) : Fin 2 → n) ∘ (1 : Fin 2).succAbove =
      monomialCechVertex j := by
    funext l
    fin_cases l
    rfl
  rw [h1] at h
  have h' : c.coeff (monomialCechVertex i) e - c.coeff (monomialCechVertex j) e = 0 := by
    simpa [sub_eq_add_neg] using h.trans (rfl : _ = (0 : A))
  exact sub_eq_zero.1 h'

/-- The components of a `0`-cocycle are polynomials of degree `m`, provided `m ≥ 0`. -/
lemma monomialCech_cocycle_zero_mem (hm : 0 ≤ m) {c : MonomialCechCochain n A m 0}
    (hc : (monomialCechComplex n A m).d 0 1 c = 0) (i : n) :
    (c (monomialCechVertex i) : (n → ℤ) →₀ A) ∈ Finsupp.supported A A (monomialExponents n m) := by
  intro e he
  obtain ⟨hs, hr⟩ := (c (monomialCechVertex i)).2 he
  refine ⟨hs, fun l ↦ ?_⟩
  by_cases hl : l = i
  · subst hl
    by_cases h : ∃ j, j ≠ l
    · obtain ⟨j, hj⟩ := h
      rw [monomialCech_cocycle_zero hc l j] at he
      exact ((c (monomialCechVertex j)).2 he).2 l fun ⟨_, h'⟩ ↦ hj h'
    · push Not at h
      rw [← hs, Fintype.sum_eq_single l fun j hj ↦ absurd (h j) hj] at hm
      exact hm
  · exact hr l fun ⟨_, h'⟩ ↦ hl h'.symm

/-- If there are at least two coordinates, the components of a `0`-cocycle are polynomials of
degree `m`, for every `m`. -/
lemma monomialCech_cocycle_zero_mem_of_ne {c : MonomialCechCochain n A m 0}
    (hc : (monomialCechComplex n A m).d 0 1 c = 0) {i j : n} (hij : i ≠ j) :
    (c (monomialCechVertex i) : (n → ℤ) →₀ A) ∈ Finsupp.supported A A (monomialExponents n m) := by
  intro e he
  obtain ⟨hs, hr⟩ := (c (monomialCechVertex i)).2 he
  refine ⟨hs, fun l ↦ ?_⟩
  by_cases hl : l = i
  · subst hl
    rw [monomialCech_cocycle_zero hc l j] at he
    exact ((c (monomialCechVertex j)).2 he).2 l fun ⟨_, h'⟩ ↦ hij h'.symm
  · exact hr l fun ⟨_, h'⟩ ↦ hl h'.symm

variable (n) in
/-- There are no monomials of negative degree. -/
lemma monomialExponents_eq_empty (hm : m < 0) : monomialExponents n m = ∅ := by
  ext e
  simp only [monomialExponents, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
    not_forall, not_le]
  intro hs
  by_contra! h
  exact hm.not_ge (hs ▸ Finset.sum_nonneg fun i _ ↦ h i)

variable (n A) in
/-- **`H⁰` of the monomial Čech complex in negative degree**: for `m < 0` and at least two
coordinates, the `0`-th cohomology of the monomial Čech complex of `𝒪(m)` vanishes. -/
lemma subsingleton_monomialCechComplex_homology_zero [Nontrivial n] (hm : m < 0) :
    Subsingleton ((monomialCechComplex n A m).homology 0) := by
  refine (monomialCechComplex n A m).homologyZeroLinearEquiv.toEquiv.subsingleton_congr.2
    ⟨fun c c' ↦ ?_⟩
  suffices h : ∀ c : LinearMap.ker ((monomialCechComplex n A m).d 0 1).hom, c = 0 by
    rw [h c, h c']
  intro c
  refine Subtype.ext (MonomialCechCochain.ext_coeff fun σ e ↦ ?_)
  obtain ⟨j, hj⟩ := exists_ne (σ 0)
  have hσ : σ = monomialCechVertex (σ 0) := funext fun l ↦ by fin_cases l; rfl
  have h := monomialCech_cocycle_zero_mem_of_ne (A := A) c.2 hj.symm
  rw [monomialExponents_eq_empty n hm, Finsupp.supported_empty, Submodule.mem_bot] at h
  change (c.1 σ : (n → ℤ) →₀ A) e = 0
  rw [hσ, h]
  rfl

/-- A family of sections all equal to the same polynomial is a `0`-cocycle. -/
lemma monomialCechComplex_d_const (g : Finsupp.supported A A (monomialExponents n m)) :
    (monomialCechComplex n A m).d 0 1
      (fun σ ↦ ⟨g, Finsupp.supported_mono (monomialExponents_subset σ) g.2⟩ :
        MonomialCechCochain n A m 0) = 0 := by
  refine MonomialCechCochain.ext_coeff (p := 1) fun σ e ↦ ?_
  rw [monomialCechComplex_d_apply, Fin.sum_univ_two]
  change _ = (0 : A)
  simp

variable (n A m) in
/-- The `0`-cocycles of the monomial Čech complex, for `m ≥ 0`, are the polynomials of degree
`m`: a cocycle is determined by its component on any standard open `U_{i₀}`. -/
def monomialCechCocycleZeroEquiv (hm : 0 ≤ m) (i₀ : n) :
    LinearMap.ker ((monomialCechComplex n A m).d 0 1).hom ≃ₗ[A]
      Finsupp.supported A A (monomialExponents n m) where
  toFun c := ⟨c.1 (monomialCechVertex i₀), monomialCech_cocycle_zero_mem hm c.2 i₀⟩
  invFun g := ⟨fun σ ↦ ⟨g, Finsupp.supported_mono (monomialExponents_subset σ) g.2⟩,
    monomialCechComplex_d_const g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv c := Subtype.ext (funext fun σ ↦ by
    have hσ : σ = monomialCechVertex (σ 0) := funext fun l ↦ by fin_cases l; rfl
    refine Subtype.ext ?_
    change (c.1 (monomialCechVertex i₀) : (n → ℤ) →₀ A) = c.1 σ
    rw [hσ, monomialCech_cocycle_zero c.2 (σ 0) i₀])
  right_inv _ := rfl

variable (n) in
/-- The nonnegative exponent vectors of sum `D` are the exponent vectors `n →₀ ℕ` of the
monomials of degree `D`. -/
def monomialExponentsEquiv (D : ℕ) :
    monomialExponents n (D : ℤ) ≃ {s : n →₀ ℕ | s.degree = D} where
  toFun e := ⟨Finsupp.equivFunOnFinite.symm fun i ↦ (e.1 i).toNat, by
    have h := e.2.1
    change Finsupp.degree _ = D
    rw [Finsupp.degree_eq_sum]
    apply Nat.cast_injective (R := ℤ)
    rw [Nat.cast_sum]
    refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans h
    simpa using e.2.2 i⟩
  invFun s := ⟨fun i ↦ (s.1 i : ℤ), by
    refine ⟨?_, fun i ↦ by positivity⟩
    have h : Finsupp.degree s.1 = D := s.2
    rw [Finsupp.degree_eq_sum] at h
    change ∑ i, ((s.1 i : ℕ) : ℤ) = (D : ℤ)
    exact_mod_cast h⟩
  left_inv e := Subtype.ext (funext fun i ↦ by simpa using e.2.2 i)
  right_inv s := by
    apply Subtype.ext
    ext i
    simp

variable (n A) in
/-- The monomial basis of the module `A[xᵢ]_D` of homogeneous polynomials of degree `D`. -/
def homogeneousSubmoduleBasis (D : ℕ) :
    Module.Basis {s : n →₀ ℕ | s.degree = D} A (MvPolynomial.homogeneousSubmodule n A D) :=
  (MvPolynomial.basisRestrictSupport A {s : n →₀ ℕ | s.degree = D}).map
    (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported n A D).symm)

variable (n A) in
/-- **`H⁰` of the monomial Čech complex**: for `m ≥ 0`, the `0`-th cohomology of the monomial
Čech complex of `𝒪(m)` is the module `A[xᵢ]ₘ` of homogeneous polynomials of degree `m`. -/
def monomialCechComplexHomologyZeroLinearEquiv [Nonempty n] (D : ℕ) :
    (monomialCechComplex n A D).homology 0 ≃ₗ[A] MvPolynomial.homogeneousSubmodule n A D :=
  (monomialCechComplex n A D).homologyZeroLinearEquiv ≪≫ₗ
    monomialCechCocycleZeroEquiv n A D (Int.natCast_nonneg D) (Classical.arbitrary n) ≪≫ₗ
    Finsupp.supportedEquivFinsupp _ ≪≫ₗ
    Finsupp.domLCongr (monomialExponentsEquiv n D) ≪≫ₗ
    (homogeneousSubmoduleBasis n A D).repr.symm

/-! ### The top degree: alternating cochains -/

/-- The value of `p.succAbove i`, as a natural number. -/
private lemma val_succAbove_eq_ite {k : ℕ} (p : Fin (k + 1)) (i : Fin k) :
    (p.succAbove i : ℕ) = if (i : ℕ) < p then (i : ℕ) else (i : ℕ) + 1 := by
  rcases lt_or_ge (i : ℕ) p with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h), if_pos h]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h), if_neg h.not_gt]
    rfl

open scoped Classical in
variable (A) in
/-- The sign of a tuple `σ : Fin (d + 1) → n` relative to a fixed enumeration
`E : Fin (d + 1) ≃ n` of the coordinates: the determinant of the matrix with entries
`[σ a = E b]`. It is the sign of the permutation `E⁻¹ ∘ σ` if `σ` is bijective, and zero
otherwise. -/
def tupleSign {d : ℕ} (E : Fin (d + 1) ≃ n) (σ : Fin (d + 1) → n) : A :=
  (Matrix.of fun a b ↦ if σ a = E b then (1 : A) else 0).det

omit [Fintype n] in
lemma tupleSign_eq_zero {d : ℕ} (E : Fin (d + 1) ≃ n) {σ : Fin (d + 1) → n}
    (h : ¬ Function.Injective σ) : tupleSign A E σ = 0 := by
  classical
  simp only [Function.Injective, not_forall] at h
  obtain ⟨a, b, hab, hne⟩ := h
  exact Matrix.det_zero_of_row_eq hne (funext fun j ↦ by simp [hab])

omit [Fintype n] in
lemma tupleSign_self {d : ℕ} (E : Fin (d + 1) ≃ n) : tupleSign A E E = 1 := by
  classical
  have : (Matrix.of fun a b ↦ if E a = E b then (1 : A) else 0) = 1 := by
    ext a b
    simp [Matrix.one_apply, E.injective.eq_iff]
  rw [tupleSign, this, Matrix.det_one]

/-- **The sign is a cocycle**: for `τ : Fin (d + 2) → n`, the alternating sum of the signs of
the faces of `τ` is the Laplace expansion, along its first column, of a matrix with two equal
rows. -/
lemma sum_tupleSign_comp_succAbove {d : ℕ} (hn : Fintype.card n = d + 1)
    (E : Fin (d + 1) ≃ n) (τ : Fin (d + 2) → n) :
    ∑ i : Fin (d + 2), (-1 : A) ^ (i : ℕ) * tupleSign A E (τ ∘ i.succAbove) = 0 := by
  classical
  let B : Matrix (Fin (d + 2)) (Fin (d + 2)) A :=
    Matrix.of fun i j ↦ Fin.cases 1 (fun b ↦ if τ i = E b then 1 else 0) j
  have h := Matrix.det_succ_column_zero B
  obtain ⟨i, j, hij, hτ⟩ := Fintype.exists_ne_map_eq_of_card_lt τ (by simp [hn])
  rw [Matrix.det_zero_of_row_eq hij (funext fun l ↦ by cases l using Fin.cases <;> simp [B, hτ])]
    at h
  refine (Finset.sum_congr rfl fun l _ ↦ ?_).trans h.symm
  simp only [B, Matrix.of_apply, Fin.cases_zero, mul_one]
  rfl

/-- The degeneracy `Fin (d + 2) → Fin (d + 1)` with values
`(0, …, a - 1, a + 1, a, a + 1, a + 2, …, d)`: it hits `a + 1` twice, at `a` and `a + 2`. -/
def swapDegeneracy {d : ℕ} (a : Fin d) (j : Fin (d + 2)) : Fin (d + 1) :=
  ⟨if (j : ℕ) < a then j else if (j : ℕ) = a then a + 1 else if (j : ℕ) = a + 1 then a
    else if (j : ℕ) = a + 2 then a + 1 else j - 1, by
    have := j.2
    have := a.2
    split_ifs <;> omega⟩

lemma swapDegeneracy_comp_succAbove {d : ℕ} (a : Fin d) :
    swapDegeneracy a ∘ (⟨a, by omega⟩ : Fin (d + 2)).succAbove = id := by
  funext k
  ext
  simp only [swapDegeneracy, Function.comp_apply, val_succAbove_eq_ite, id_eq]
  split_ifs <;> omega

lemma swapDegeneracy_comp_succAbove_add_two {d : ℕ} (a : Fin d) :
    swapDegeneracy a ∘ (⟨a + 2, by omega⟩ : Fin (d + 2)).succAbove =
      Equiv.swap a.castSucc a.succ := by
  funext k
  ext
  simp only [swapDegeneracy, Function.comp_apply, val_succAbove_eq_ite]
  rw [Equiv.swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

lemma swapDegeneracy_eq_iff {d : ℕ} (a : Fin d) {j x : Fin (d + 2)} (hj : (j : ℕ) ≠ a)
    (hj' : (j : ℕ) ≠ a + 2) (h : swapDegeneracy a x = swapDegeneracy a j) : x = j := by
  simp only [swapDegeneracy, Fin.mk.injEq] at h
  ext
  split_ifs at h <;> omega

variable (n A m) in
/-- The strictly negative exponent vectors of sum `m`, the exponents of the Laurent monomials
`xᵉ` that are sections of `𝒪(m)` on `U₀ ∩ ⋯ ∩ U_d` only. -/
def negativeExponents : Set (n → ℤ) :=
  {e | ∑ i, e i = m ∧ ∀ i, e i < 0}

/-- **Top-degree cocycles are alternating**: on the summand of a strictly negative exponent
vector, swapping two adjacent entries of a tuple changes the sign of the coefficient of a
cocycle of degree `d`. This is the cocycle condition at the tuple
`σ ∘ swapDegeneracy a`, all of whose faces but two miss a coordinate. -/
lemma monomialCech_cocycle_top_swap {d : ℕ} (hn : Fintype.card n = d + 1)
    {c : MonomialCechCochain n A m d} (hc : (monomialCechComplex n A m).d d (d + 1) c = 0)
    {e : n → ℤ} (he : ∀ i, e i < 0) (σ : Fin (d + 1) → n) (a : Fin d) :
    c.coeff (σ ∘ Equiv.swap a.castSucc a.succ) e = -c.coeff σ e := by
  by_cases hσ : Function.Injective σ
  · have h := congrArg (fun c' ↦ MonomialCechCochain.coeff (m := m) c'
      (σ ∘ swapDegeneracy a) e) hc
    simp only at h
    rw [monomialCechComplex_d_apply] at h
    have hsum := Fintype.sum_eq_add (f := fun j : Fin (d + 2) ↦ (-1 : ℤ) ^ (j : ℕ) •
        c.coeff ((σ ∘ swapDegeneracy a) ∘ j.succAbove) e)
      (⟨a, by omega⟩ : Fin (d + 2)) ⟨a + 2, by omega⟩ (by simp [Fin.ext_iff]) (by
        rintro j ⟨hj₁, hj₂⟩
        have hj₁' : (j : ℕ) ≠ a := fun h ↦ hj₁ (Fin.ext h)
        have hj₂' : (j : ℕ) ≠ a + 2 := fun h ↦ hj₂ (Fin.ext h)
        rw [c.coeff_eq_zero_of_neg _ (i := σ (swapDegeneracy a j)) ?_ (he _), smul_zero]
        rintro ⟨k, hk⟩
        exact Fin.succAbove_ne j k (swapDegeneracy_eq_iff a hj₁' hj₂' (hσ hk)))
    have h' := hsum.symm.trans (h.trans (rfl : _ = (0 : A)))
    simp only [Function.comp_assoc, swapDegeneracy_comp_succAbove,
      swapDegeneracy_comp_succAbove_add_two, Function.comp_id, pow_add, neg_one_sq,
      mul_one] at h'
    rw [← smul_add] at h'
    rcases neg_one_pow_eq_or ℤ (a : ℕ) with h1 | h1 <;> rw [h1] at h' <;>
      simp only [one_smul, neg_smul, neg_eq_zero] at h' <;>
      exact eq_neg_of_add_eq_zero_right h'
  · have hσ' : ¬ Function.Surjective σ := fun h ↦ hσ (Finite.injective_iff_surjective_of_equiv
      (Fintype.equivOfCardEq (by simp [hn])) |>.2 h)
    simp only [Function.Surjective, not_forall] at hσ'
    obtain ⟨i, hi⟩ := hσ'
    rw [c.coeff_eq_zero_of_neg σ (i := i) (fun ⟨k, hk⟩ ↦ hi ⟨k, hk⟩) (he i),
      c.coeff_eq_zero_of_neg _ (i := i) (fun ⟨k, hk⟩ ↦ hi ⟨_, hk⟩) (he i), neg_zero]

/-- A non-injective tuple `Fin (d + 1) → n` misses some coordinate. -/
private lemma exists_notMem_range_of_not_injective {d : ℕ} (hn : Fintype.card n = d + 1)
    {σ : Fin (d + 1) → n} (hσ : ¬ Function.Injective σ) : ∃ i, i ∉ Set.range σ := by
  by_contra! h
  exact hσ ((Fintype.bijective_iff_surjective_and_card σ).2 ⟨fun i ↦ h i, by simp [hn]⟩).1

/-- **Top-degree cocycles are determined by one component**: on the summand of a strictly
negative exponent vector, a cocycle of degree `d` whose coefficient vanishes on one bijective
tuple `E` vanishes, since the adjacent transpositions generate the symmetric group. -/
lemma monomialCech_cocycle_top_eq_zero {d : ℕ} (hn : Fintype.card n = d + 1)
    {c : MonomialCechCochain n A m d} (hc : (monomialCechComplex n A m).d d (d + 1) c = 0)
    {e : n → ℤ} (he : ∀ i, e i < 0) (E : Fin (d + 1) ≃ n) (h₀ : c.coeff E e = 0)
    (σ : Fin (d + 1) → n) : c.coeff σ e = 0 := by
  have key (π : Equiv.Perm (Fin (d + 1))) :
      ∀ τ : Fin (d + 1) → n, c.coeff τ e = 0 → c.coeff (τ ∘ π) e = 0 := by
    have hπ : π ∈ Submonoid.closure
        (Set.range fun i : Fin d ↦ Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction hπ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      intro τ hτ
      rw [monomialCech_cocycle_top_swap hn hc he τ a, hτ, neg_zero]
    | one =>
      intro τ hτ
      simpa using hτ
    | mul x y _ _ hx hy =>
      intro τ hτ
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc]
      exact hy _ (hx _ hτ)
  by_cases hσ : Function.Injective σ
  · have hb : Function.Bijective σ :=
      (Fintype.bijective_iff_injective_and_card σ).2 ⟨hσ, by simp [hn]⟩
    have hσE : σ = E ∘ ((Equiv.ofBijective σ hb).trans E.symm) := funext fun x ↦ by simp
    rw [hσE]
    exact key _ E h₀
  · obtain ⟨i, hi⟩ := exists_notMem_range_of_not_injective hn hσ
    exact c.coeff_eq_zero_of_neg σ hi (he i)

variable (n A m) in
/-- The coefficients of a top-degree cochain on the bijective tuple `E`, at the strictly
negative exponent vectors. -/
def monomialCechTopCoeff {d : ℕ} (E : Fin (d + 1) ≃ n) :
    MonomialCechCochain n A m d →ₗ[A] (negativeExponents n m →₀ A) :=
  Finsupp.lcomapDomain Subtype.val Subtype.val_injective ∘ₗ
    (Submodule.subtype _ ∘ₗ LinearMap.proj (R := A) (φ := fun σ : Fin (d + 1) → n ↦
      Finsupp.supported A A (monomialCechSupport n m σ)) (E : Fin (d + 1) → n))

lemma monomialCechTopCoeff_apply {d : ℕ} (E : Fin (d + 1) ≃ n) (c : MonomialCechCochain n A m d)
    (e : negativeExponents n m) : monomialCechTopCoeff n A m E c e = c.coeff E e :=
  rfl

lemma tupleSign_smul_mem_supported {d : ℕ} (hn : Fintype.card n = d + 1) (E : Fin (d + 1) ≃ n)
    (σ : Fin (d + 1) → n) (a : negativeExponents n m →₀ A) :
    tupleSign A E σ • Finsupp.mapDomain Subtype.val a ∈
      Finsupp.supported A A (monomialCechSupport n m σ) := by
  intro e he
  by_cases hs : tupleSign A E σ = 0
  · simp [hs] at he
  have hσ : Function.Injective σ := by
    by_contra h
    exact hs (tupleSign_eq_zero E h)
  have hσ' := ((Fintype.bijective_iff_injective_and_card σ).2 ⟨hσ, by simp [hn]⟩).2
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1
    (Finsupp.mapDomain_support (Finsupp.support_smul he))
  exact ⟨x.2.1, fun i hi ↦ absurd (hσ' i) hi⟩

variable (n A m) in
/-- The top-degree cocycle with coefficients `a` on the strictly negative exponent vectors,
alternating in the tuple: its component on `σ` is `tupleSign E σ • a`. -/
def monomialCechTopCocycle {d : ℕ} (hn : Fintype.card n = d + 1) (E : Fin (d + 1) ≃ n) :
    (negativeExponents n m →₀ A) →ₗ[A] MonomialCechCochain n A m d where
  toFun a σ := ⟨_, tupleSign_smul_mem_supported hn E σ a⟩
  map_add' a b := funext fun σ ↦ Subtype.ext (by
    change tupleSign A E σ • Finsupp.mapDomain Subtype.val (a + b) =
      tupleSign A E σ • Finsupp.mapDomain Subtype.val a +
        tupleSign A E σ • Finsupp.mapDomain Subtype.val b
    rw [Finsupp.mapDomain_add, smul_add])
  map_smul' r a := MonomialCechCochain.ext_coeff fun σ e ↦ by
    simp [MonomialCechCochain.coeff, Finsupp.mapDomain_smul, mul_left_comm]

lemma monomialCechTopCocycle_coeff {d : ℕ} (hn : Fintype.card n = d + 1) (E : Fin (d + 1) ≃ n)
    (a : negativeExponents n m →₀ A) (σ : Fin (d + 1) → n) (e : n → ℤ) :
    (monomialCechTopCocycle n A m hn E a).coeff σ e =
      tupleSign A E σ * Finsupp.mapDomain Subtype.val a e :=
  rfl

lemma monomialCechComplex_d_monomialCechTopCocycle {d : ℕ} (hn : Fintype.card n = d + 1)
    (E : Fin (d + 1) ≃ n) (a : negativeExponents n m →₀ A) :
    (monomialCechComplex n A m).d d (d + 1) (monomialCechTopCocycle n A m hn E a) = 0 := by
  refine MonomialCechCochain.ext_coeff (p := d + 1) fun τ e ↦ ?_
  rw [monomialCechComplex_d_apply]
  change _ = (0 : A)
  simp only [monomialCechTopCocycle_coeff, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    ← mul_assoc, ← Finset.sum_mul, sum_tupleSign_comp_succAbove hn, zero_mul]

lemma monomialCechTopCoeff_monomialCechTopCocycle {d : ℕ} (hn : Fintype.card n = d + 1)
    (E : Fin (d + 1) ≃ n) (a : negativeExponents n m →₀ A) :
    monomialCechTopCoeff n A m E (monomialCechTopCocycle n A m hn E a) = a := by
  ext e
  rw [monomialCechTopCoeff_apply, monomialCechTopCocycle_coeff, tupleSign_self, one_mul,
    Finsupp.mapDomain_apply Subtype.val_injective]

variable (n A m) in
/-- The coefficients of the top-degree cocycles on the bijective tuple `E`. -/
def monomialCechCocycleTopCoeff {d : ℕ} (E : Fin (d + 1) ≃ n) :
    LinearMap.ker ((monomialCechComplex n A m).d d (d + 1)).hom →ₗ[A]
      (negativeExponents n m →₀ A) :=
  monomialCechTopCoeff n A m E ∘ₗ Submodule.subtype _

lemma monomialCechCocycleTopCoeff_surjective {d : ℕ} (hn : Fintype.card n = d + 1)
    (E : Fin (d + 1) ≃ n) : Function.Surjective (monomialCechCocycleTopCoeff n A m E) :=
  fun a ↦ ⟨⟨_, monomialCechComplex_d_monomialCechTopCocycle hn E a⟩,
    monomialCechTopCoeff_monomialCechTopCocycle hn E a⟩

/-- A top-degree cocycle whose coefficients on `E` at the strictly negative exponent vectors
vanish has no strictly negative exponent vectors at all. -/
lemma monomialCech_cocycle_top_coeff_eq_zero {d : ℕ} (hn : Fintype.card n = d + 1)
    (E : Fin (d + 1) ≃ n) {c : LinearMap.ker ((monomialCechComplex n A m).d d (d + 1)).hom}
    (hc : monomialCechCocycleTopCoeff n A m E c = 0) (σ : Fin (d + 1) → n) {e : n → ℤ}
    (he : ∀ i, e i < 0) : c.1.coeff σ e = 0 := by
  by_cases hs : ∑ i, e i = m
  · exact monomialCech_cocycle_top_eq_zero hn c.2 he E
      ((DFunLike.congr_fun hc ⟨e, hs, he⟩).trans rfl) σ
  · exact c.1.coeff_eq_zero_of_sum_ne σ hs

/-- With a single coordinate and `m < 0`, every exponent vector of sum `m` is strictly
negative. -/
private lemma forall_neg_of_card_eq_one (hn : Fintype.card n = 0 + 1) (hm : m < 0) {e : n → ℤ}
    (he : ∑ i, e i = m) (i : n) : e i < 0 := by
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.1 hn
  rw [Fintype.sum_eq_single i fun j hj ↦ absurd ((hx j).trans (hx i).symm) hj] at he
  omega

/-- The boundaries in the top degree have no strictly negative exponent vectors on a
bijective tuple. -/
lemma monomialCechTopCoeff_d_eq_zero {p : ℕ} (E : Fin (p + 2) ≃ n)
    (b : MonomialCechCochain n A m p) :
    monomialCechTopCoeff n A m E ((monomialCechComplex n A m).d p (p + 1) b) = 0 := by
  ext ⟨e, -, he⟩
  rw [monomialCechTopCoeff_apply, monomialCechComplex_d_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [b.coeff_eq_zero_of_neg _ (i := E i) ?_ (he _), smul_zero]
  rintro ⟨k, hk⟩
  exact Fin.succAbove_ne i k (E.injective hk)

variable (n A m) in
/-- The top cohomology of the monomial Čech complex with a single coordinate, for `m < 0`:
`monomialCechComplexHomologyTopLinearEquiv` for `d = 0`. -/
def monomialCechComplexHomologyTopLinearEquivZero (hn : Fintype.card n = 0 + 1)
    (E : Fin (0 + 1) ≃ n) (hm : m < 0) :
    (monomialCechComplex n A m).homology 0 ≃ₗ[A] (negativeExponents n m →₀ A) :=
  (monomialCechComplex n A m).homologyZeroLinearEquiv ≪≫ₗ
    LinearEquiv.ofBijective (monomialCechCocycleTopCoeff n A m E)
      ⟨(injective_iff_map_eq_zero _).2 fun c hc ↦ by
        refine Subtype.ext (MonomialCechCochain.ext_coeff fun σ e ↦ ?_)
        by_cases hs : ∑ i, e i = m
        · exact monomialCech_cocycle_top_coeff_eq_zero hn E hc σ
            (forall_neg_of_card_eq_one hn hm hs)
        · exact c.1.coeff_eq_zero_of_sum_ne σ hs,
        monomialCechCocycleTopCoeff_surjective hn E⟩

/-- The top-degree boundaries are the top-degree cocycles without strictly negative exponent
vectors on `E`. -/
lemma range_moduleCatToCycles_eq_ker_monomialCechCocycleTopCoeff {p : ℕ}
    (hn : Fintype.card n = p + 1 + 1) (E : Fin (p + 1 + 1) ≃ n) :
    LinearMap.range ((monomialCechComplex n A m).sc' p (p + 1) (p + 2)).moduleCatToCycles =
      LinearMap.ker (monomialCechCocycleTopCoeff n A m E) := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact monomialCechTopCoeff_d_eq_zero E b
  · intro hx
    refine ⟨monomialCechHomotopy p x.1, Subtype.ext ?_⟩
    refine MonomialCechCochain.ext_coeff fun σ e ↦ ?_
    change MonomialCechCochain.coeff (m := m)
      ((monomialCechComplex n A m).d p (p + 1) (monomialCechHomotopy p x.1)) σ e = x.1.coeff σ e
    by_cases he : ∃ i, 0 ≤ e i
    · have hx' : (monomialCechComplex n A m).d (p + 1) (p + 2) x.1 = 0 := x.2
      rw [← monomialCechComplex_d_homotopy_add p x.1 σ he, hx', map_zero]
      exact (add_zero _).symm
    · push Not at he
      rw [monomialCech_cocycle_top_coeff_eq_zero hn E hx σ he, monomialCechComplex_d_apply]
      simp [monomialCechHomotopy_coeff_of_forall _ _ he]

variable (n A m) in
/-- The top cohomology of the monomial Čech complex with at least two coordinates:
`monomialCechComplexHomologyTopLinearEquiv` for `d = p + 1`. -/
def monomialCechComplexHomologyTopLinearEquivSucc {p : ℕ}
    (hn : Fintype.card n = p + 1 + 1) (E : Fin (p + 1 + 1) ≃ n) :
    (monomialCechComplex n A m).homology (p + 1) ≃ₗ[A] (negativeExponents n m →₀ A) :=
  (monomialCechComplex n A m).homologyLinearEquivQuotient p (p + 1) (p + 2) (by simp)
      (by simp) ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (range_moduleCatToCycles_eq_ker_monomialCechCocycleTopCoeff hn E)
      ≪≫ₗ
    (monomialCechCocycleTopCoeff n A m E).quotKerEquivOfSurjective
      (monomialCechCocycleTopCoeff_surjective hn E)

variable (n A m) in
/-- **The top cohomology of the monomial Čech complex**: with `d + 1` coordinates, `Hᵈ` is the
free module on the strictly negative exponent vectors of sum `m` (for `d = 0` this requires
`m < 0`; the case `m ≥ 0` is `H⁰`). The isomorphism takes the coefficients of a cocycle on a
fixed bijective tuple `E : Fin (d + 1) ≃ n`: on the summands of the exponent vectors with a
nonnegative coordinate every cocycle is a coboundary, and on the other summands the
cocycles are the alternating functions of the tuple. -/
def monomialCechComplexHomologyTopLinearEquiv :
    ∀ {d : ℕ} (_ : Fintype.card n = d + 1) (_ : Fin (d + 1) ≃ n) (_ : d ≠ 0 ∨ m < 0),
      (monomialCechComplex n A m).homology d ≃ₗ[A] (negativeExponents n m →₀ A)
  | 0, hn, E, hm => monomialCechComplexHomologyTopLinearEquivZero n A m hn E
      (hm.resolve_left (by simp))
  | _ + 1, hn, E, _ => monomialCechComplexHomologyTopLinearEquivSucc n A m hn E

/-- Strictly negative exponent vectors have sum at most `-(d + 1)`, so there are none of sum
`m ≥ -d`. -/
lemma isEmpty_negativeExponents {d : ℕ} (hn : Fintype.card n = d + 1) (hm : -(d : ℤ) ≤ m) :
    IsEmpty (negativeExponents n m) := by
  refine ⟨fun ⟨e, hs, he⟩ ↦ ?_⟩
  have h : ∑ i, e i ≤ ∑ _i : n, (-1 : ℤ) := Finset.sum_le_sum fun i _ ↦ by
    have := he i
    omega
  simp only [Finset.sum_const, Finset.card_univ, hn, nsmul_eq_mul] at h
  push_cast at h
  omega

/-- **Vanishing of the top cohomology of the monomial Čech complex**: with `d + 1 ≥ 2`
coordinates, `Hᵈ = 0` for `m ≥ -d`. -/
theorem subsingleton_monomialCechComplex_homology_top {d : ℕ} (hn : Fintype.card n = d + 1)
    (hd : d ≠ 0) (hm : -(d : ℤ) ≤ m) :
    Subsingleton ((monomialCechComplex n A m).homology d) := by
  have := isEmpty_negativeExponents hn hm
  exact (monomialCechComplexHomologyTopLinearEquiv n A m hn
    (Fintype.equivFinOfCardEq hn).symm (.inl hd)).toEquiv.subsingleton

variable (n m) in
/-- The strictly negative exponent vectors `e` of sum `m` are, through `e ↦ -e - 1`, the
exponent vectors of the monomials of degree `-m - d - 1`. -/
def negativeExponentsEquiv {d : ℕ} (hn : Fintype.card n = d + 1) (hm : m ≤ -(d : ℤ) - 1) :
    negativeExponents n m ≃ {s : n →₀ ℕ | s.degree = (-m - d - 1).toNat} where
  toFun e := ⟨Finsupp.equivFunOnFinite.symm fun i ↦ (-e.1 i - 1).toNat, by
    obtain ⟨hs, he⟩ := e.2
    change Finsupp.degree _ = _
    rw [Finsupp.degree_eq_sum]
    apply Nat.cast_injective (R := ℤ)
    rw [Nat.cast_sum, Int.toNat_of_nonneg (by omega)]
    have h : ∑ i, ((-e.1 i - 1).toNat : ℤ) = ∑ i, (-e.1 i - 1) :=
      Finset.sum_congr rfl fun i _ ↦ Int.toNat_of_nonneg (by have := he i; omega)
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    rw [h, Finset.sum_sub_distrib, Finset.sum_neg_distrib, hs]
    simp [hn]
    ring⟩
  invFun s := ⟨fun i ↦ -(s.1 i : ℤ) - 1, by
    refine ⟨?_, fun i ↦ show -(s.1 i : ℤ) - 1 < 0 by omega⟩
    have h : Finsupp.degree s.1 = (-m - d - 1).toNat := s.2
    rw [Finsupp.degree_eq_sum] at h
    have h' : ∑ i, ((s.1 i : ℕ) : ℤ) = -m - d - 1 := by
      rw [← Nat.cast_sum, h, Int.toNat_of_nonneg (by omega)]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, h']
    simp [hn]
    ring⟩
  left_inv e := Subtype.ext (funext fun i ↦ by
    have := e.2.2 i
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    omega)
  right_inv s := by
    rcases s with ⟨s, hs⟩
    refine Subtype.ext ?_
    ext i
    simp

/-- There are finitely many strictly negative exponent vectors of a given sum. -/
lemma finite_negativeExponents (m : ℤ) : Finite (negativeExponents n m) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, Fintype.card n = d + 1 ∨ IsEmpty n := by
    rcases isEmpty_or_nonempty n with h | h
    · exact ⟨0, .inr h⟩
    · exact ⟨Fintype.card n - 1, .inl (by have := Fintype.card_pos (α := n); omega)⟩
  rcases hd with hd | hd
  · by_cases hm : m ≤ -(d : ℤ) - 1
    · haveI : Finite {s : n →₀ ℕ | s.degree = (-m - d - 1).toNat} :=
        (Finsupp.finite_of_degree_eq _).to_subtype
      exact Finite.of_equiv _ (negativeExponentsEquiv n m hd hm).symm
    · haveI := isEmpty_negativeExponents (n := n) hd (m := m) (by omega)
      infer_instance
  · exact Finite.of_injective (fun e : negativeExponents n m ↦ (e : n → ℤ))
      Subtype.val_injective

/-- **The homology of the monomial Čech complex is finite**, in the degrees `q ≤ d` where it can
compute cohomology: `H⁰` is a module of homogeneous polynomials (or zero), the middle degrees
vanish and the top degree is free on the finitely many strictly negative exponent vectors. -/
lemma finite_monomialCechComplex_homology (A : Type (max u v)) [CommRing A] {d : ℕ}
    (hn : Fintype.card n = d + 1) (m : ℤ) {q : ℕ} (hq : q ≤ d) :
    Module.Finite A ((monomialCechComplex n A m).homology q) := by
  haveI := finite_negativeExponents (n := n) m
  letI : Fintype (negativeExponents n m) := Fintype.ofFinite _
  letI : Module.Finite A (negativeExponents n m →₀ A) :=
    Module.Finite.of_basis (Finsupp.basisSingleOne (R := A) (ι := negativeExponents n m))
  haveI hnonempty : Nonempty n := Fintype.card_pos_iff.1 (by omega)
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · rcases le_or_gt 0 m with hm | hm
    · obtain ⟨D, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      haveI : Finite {s : n →₀ ℕ | s.degree = D} := (Finsupp.finite_of_degree_eq _).to_subtype
      haveI := Module.Finite.of_basis (homogeneousSubmoduleBasis n A D)
      exact Module.Finite.equiv (monomialCechComplexHomologyZeroLinearEquiv n A D).symm
    · rcases Nat.eq_zero_or_pos d with rfl | hd
      · exact Module.Finite.equiv (monomialCechComplexHomologyTopLinearEquiv n A m hn
          (Fintype.equivFinOfCardEq hn).symm (.inr hm)).symm
      · haveI : Nontrivial n := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
        haveI := subsingleton_monomialCechComplex_homology_zero n A hm
        infer_instance
  · rcases hq.lt_or_eq with hlt | rfl
    · obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0.ne'
      haveI := ModuleCat.isZero_iff_subsingleton.1
        (exactAt_monomialCechComplex n A m hn q hlt).isZero_homology
      infer_instance
    · exact Module.Finite.equiv (monomialCechComplexHomologyTopLinearEquiv n A m hn
        (Fintype.equivFinOfCardEq hn).symm (.inl hq0.ne')).symm

section PolynomialDual

variable (coordinates : Type v) [Fintype coordinates]
  (coefficientRing : Type (max u v)) [CommRing coefficientRing] (twistDegree : ℤ)

/-- Top monomial Čech homology is the coefficient dual of homogeneous polynomials. -/
def monomialCechComplexHomologyTopLinearEquivDual {dimension : ℕ} (coordinateCount : Fintype.card coordinates = dimension + 1)
    (twistBound : twistDegree ≤ -(dimension : ℤ) - 1) :
    (monomialCechComplex coordinates coefficientRing twistDegree).homology dimension ≃ₗ[coefficientRing]
      Module.Dual coefficientRing (MvPolynomial.homogeneousSubmodule coordinates coefficientRing (-twistDegree - dimension - 1).toNat) :=
  haveI : Finite {naturalExponents : coordinates →₀ ℕ | naturalExponents.degree = (-twistDegree - dimension - 1).toNat} :=
    (Finsupp.finite_of_degree_eq _).to_subtype
  monomialCechComplexHomologyTopLinearEquiv coordinates coefficientRing twistDegree coordinateCount (Fintype.equivFinOfCardEq coordinateCount).symm
      (.inr (by omega)) ≪≫ₗ
    Finsupp.domLCongr (negativeExponentsEquiv coordinates twistDegree coordinateCount twistBound) ≪≫ₗ
    Finsupp.linearEquivFunOnFinite coefficientRing coefficientRing _ ≪≫ₗ
    (homogeneousSubmoduleBasis coordinates coefficientRing _).constr coefficientRing

end PolynomialDual

end AlgebraicGeometry.ProjectiveSpace
