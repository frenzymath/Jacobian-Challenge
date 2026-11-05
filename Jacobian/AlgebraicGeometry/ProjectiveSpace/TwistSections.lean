import Jacobian.AlgebraicGeometry.Modules.Sections
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Basic
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.StructureMap
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.FreeGenerator
import Jacobian.RingTheory.MvPolynomial.Laurent

/-!
# Laurent monomial sections of twisting sheaves

On a nonempty standard affine intersection of polynomial projective space,
the sections of `𝒪(m)` have a basis of Laurent monomials of total degree `m`.
The construction works directly over the coefficient ring. Restricting to a
smaller standard intersection preserves each monomial.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist HomogeneousLocalization MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : Type v} [Fintype n] {R : Type (max u v)} [CommRing R] {s : Set n} {m : ℤ}

local instance moduleTwistSections (openSubset : (projectiveSpaceOverAffine n R).Opens) :
    Module Γ(projectiveSpaceOverAffine n R, openSubset)
      Γ(twist (homogeneousSubmodule n R) m, openSubset) :=
  modulePresheafInAbObj (homogeneousSubmodule n R) m (.op openSubset)

/-- A point lies in `D₊(∏_{i ∈ s} Xᵢ)` if and only if it lies in every `D₊(Xᵢ)`, `i ∈ s`. -/
lemma mem_basicOpen_monomialToNat_indicator {x : Proj (homogeneousSubmodule n R)} :
    x ∈ Proj.basicOpen _ (monomialToNat R (s.indicator 1)) ↔
      ∀ i ∈ s, x ∈ Proj.basicOpen (homogeneousSubmodule n R) (X i) := by
  simp only [Proj.mem_basicOpen]
  change monomialToNat R (s.indicator 1) ∉ x.asHomogeneousIdeal.toIdeal ↔
    ∀ i ∈ s, X i ∉ x.asHomogeneousIdeal.toIdeal
  rw [monomialToNat_mem_iff]
  constructor
  · intro h i hi hX
    exact h ⟨i, by simp [Set.indicator_of_mem hi], hX⟩
  · rintro h ⟨i, hi, hX⟩
    by_cases his : i ∈ s
    · exact h i his hX
    · simp [Set.indicator_of_notMem his] at hi

lemma basicOpen_monomialToNat_indicator_mono {s t : Set n} (h : t ⊆ s) :
    Proj.basicOpen (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1)) ≤
      Proj.basicOpen _ (monomialToNat R (t.indicator 1)) := fun _ hx ↦
  mem_basicOpen_monomialToNat_indicator.2 fun i hi ↦
    mem_basicOpen_monomialToNat_indicator.1 hx i (h hi)



variable (R m) in
/-- **The section `xᵃ / xᵇ` of `𝒪(m)`** over an open `U` of `Proj R[Xᵢ]` on which `xᵇ` does not
vanish, for nonnegative exponent vectors `a`, `b` with `∑ aᵢ = ∑ bᵢ + m`. -/
noncomputable def twistMonomialFraction {a b : n → ℤ} (h : ∑ i, a i = ∑ i, b i + m) (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (U : (Proj (homogeneousSubmodule n R)).Opens)
    (hU : ∀ x ∈ U, monomialToNat R b ∉ x.asHomogeneousIdeal) :
    Γ(twist (homogeneousSubmodule n R) m, U) :=
  ⟨fun x ↦ degreePart.mk ⟨monomialToNat R a, monomialToNat_mem a⟩
    ⟨monomialToNat R b, monomialToNat_mem b⟩ (hU x.1 x.2) (by
      rw [cast_sum_toNat ha, cast_sum_toNat hb, h]),
    isLocallyFraction_mk (by rw [cast_sum_toNat ha, cast_sum_toNat hb, h]) _ _
      fun x ↦ hU x.1 x.2⟩

lemma coe_twistMonomialFraction_apply {a b : n → ℤ} (h : ∑ i, a i = ∑ i, b i + m) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (U : (Proj (homogeneousSubmodule n R)).Opens)
    (hU : ∀ x ∈ U, monomialToNat R b ∉ x.asHomogeneousIdeal) (x : U) :
    ((twistMonomialFraction (R := R) (m := m) h ha hb U hU).1 x :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      Localization.mk (monomialToNat R a) ⟨monomialToNat R b, hU x.1 x.2⟩ :=
  rfl

lemma monomialToNat_nsmul_indicator_notMem {x : Proj (homogeneousSubmodule n R)}
    (hx : x ∈ Proj.basicOpen _ (monomialToNat R (s.indicator 1))) (N : ℕ) :
    monomialToNat R (N • s.indicator (1 : n → ℤ)) ∉ x.asHomogeneousIdeal := by
  rw [← monomialToNat_pow (indicator_one_nonneg s)]
  exact fun h ↦ hx (x.isPrime.mem_of_pow_mem N h)

lemma sum_add_nsmul_indicator_eq {e : n → ℤ} (he : ∑ i, e i = m) (N : ℕ) :
    ∑ i, (e + N • s.indicator (1 : n → ℤ)) i = ∑ i, (N • s.indicator (1 : n → ℤ)) i + m := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, he]
  ring

variable (R s) in
/-- **The Laurent monomial `xᵉ` as a section of `𝒪(m)`** over `D₊(∏_{i ∈ s} Xᵢ)`, for an
exponent vector `e` with `∑ eᵢ = m` and `eᵢ ≥ 0` for `i ∉ s`. -/
noncomputable def twistMonomial (e : laurentExponents s m) :
    Γ(twist (homogeneousSubmodule n R) m,
      Proj.basicOpen _ (monomialToNat R (s.indicator 1))) :=
  twistMonomialFraction (R := R) (m := m) (sum_add_nsmul_indicator_eq e.2.1 (negExponentSum e.1))
    (add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1))
    (nsmul_nonneg (indicator_one_nonneg s) _) _
    fun _ hx ↦ monomialToNat_nsmul_indicator_notMem hx _

lemma coe_twistMonomial_apply (e : laurentExponents s m)
    (x : Proj.basicOpen (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1))) :
    ((twistMonomial R s e).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      Localization.mk (monomialToNat R (e.1 + negExponentSum e.1 • s.indicator 1))
        ⟨monomialToNat R (negExponentSum e.1 • s.indicator 1),
          monomialToNat_nsmul_indicator_notMem x.2 _⟩ :=
  rfl

/-- The Laurent monomial `xᵉ` on `D₊(∏_{i ∈ t} Xᵢ)` restricts to the Laurent monomial `xᵉ` on
the smaller open `D₊(∏_{i ∈ s} Xᵢ)`, for `t ⊆ s`. -/
lemma twist_presheaf_map_twistMonomial {t : Set n} (hts : t ⊆ s) (e : laurentExponents t m) :
    (twist (homogeneousSubmodule n R) m).presheaf.map
        (homOfLE (basicOpen_monomialToNat_indicator_mono (R := R) hts)).op
        (twistMonomial R t e) =
      twistMonomial R s ⟨e.1, e.2.1, fun i hi ↦ e.2.2 i fun h ↦ hi (hts h)⟩ := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  rw [twist_presheaf_map_apply, coe_twistMonomial_apply, coe_twistMonomial_apply]
  have h0 := indicator_one_nonneg s
  have h0' := indicator_one_nonneg t
  refine mk_monomialToNat_eq_mk (add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1))
    (nsmul_nonneg h0' _) (add_nsmul_indicator_nonneg (fun i hi ↦ e.2.2 i fun h ↦ hi (hts h))
      (neg_le_negExponentSum e.1)) (nsmul_nonneg h0 _) ?_ _ _
  abel



variable (s m) in
open Classical in
/-- The exponent vector `m eᵢ` of the monomial `Xᵢ ^ m`, for `i ∈ s`. -/
noncomputable def singleExponent {i : n} (hi : i ∈ s) : laurentExponents s m :=
  ⟨Pi.single i m, by simp, fun j hj ↦ by
    rw [Pi.single_apply, if_neg fun h : j = i ↦ hj (h ▸ hi)]⟩

/-- `xᵢ ^ m` is a free generator of `𝒪(m)` on `D₊(∏_{j ∈ s} Xⱼ)`, for `i ∈ s`. -/
lemma isFreeGenerator_twistMonomial_singleExponent {i : n} (hi : i ∈ s) :
    Scheme.Modules.IsFreeGenerator (twistMonomial R s (singleExponent (s := s) (m := m) hi)) := by
  refine isFreeGenerator_twist_of_mul_eq_one _
    (twistMonomial R s (singleExponent (s := s) (m := -m) hi))
    fun x ↦ ?_
  rw [coe_twistMonomial_apply, coe_twistMonomial_apply, Localization.mk_mul,
    ← Localization.mk_one]
  have h0 := indicator_one_nonneg s
  have ha := add_nsmul_indicator_nonneg (singleExponent (s := s) (m := m) hi).2.2
    (neg_le_negExponentSum (singleExponent (s := s) (m := m) hi).1)
  have ha' := add_nsmul_indicator_nonneg (singleExponent (s := s) (m := -m) hi).2.2
    (neg_le_negExponentSum (singleExponent (s := s) (m := -m) hi).1)
  have hN := nsmul_nonneg h0 (negExponentSum (singleExponent (s := s) (m := m) hi).1)
  have hN' := nsmul_nonneg h0 (negExponentSum (singleExponent (s := s) (m := -m) hi).1)
  refine mk_eq_mk_of_monomialToNat (add_nonneg ha ha') (add_nonneg hN hN') le_rfl le_rfl
    (monomialToNat_mul ha ha') ?_ monomialToNat_zero.symm monomialToNat_zero.symm ?_
  · exact monomialToNat_mul hN hN'
  · ext j
    simp only [singleExponent, Pi.add_apply, Pi.zero_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> ring

/-- The value at a point of the function `xᵉ` on `D₊(∏_{i ∈ s} Xᵢ)`. -/
lemma val_awayToSection_awayMonomial_apply (e : laurentExponents s 0)
    (x : Proj.basicOpen (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1))) :
    ((Proj.awayToSection _ _ (awayMonomial R s e)).1 x).val =
      Localization.mk (monomialToNat R (e.1 + negExponentSum e.1 • s.indicator 1))
        ⟨monomialToNat R (negExponentSum e.1 • s.indicator 1),
          monomialToNat_nsmul_indicator_notMem x.2 _⟩ := by
  have := ProjectiveSpectrum.Proj.awayToSection_apply (homogeneousSubmodule n R)
    (monomialToNat R (s.indicator 1)) (awayMonomial R s e) x
  erw [this]
  rw [awayMonomial, Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    RingHom.id_apply, ← Localization.mk_eq_mk']
  have h0 := indicator_one_nonneg s
  have ha := add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1)
  exact mk_eq_mk_of_monomialToNat ha (nsmul_nonneg h0 _) ha (nsmul_nonneg h0 _) rfl
    (monomialToNat_pow h0 _) rfl rfl rfl

open Classical in
variable (m) in
/-- The exponent vector `e - m eᵢ` of `xᵉ / xᵢ ^ m`, for `i ∈ s`. -/
noncomputable def shiftExponent {i : n} (hi : i ∈ s) (e : laurentExponents s m) :
    laurentExponents s 0 :=
  ⟨e.1 - Pi.single i m, by simp [Finset.sum_sub_distrib, e.2.1], fun j hj ↦ by
    rw [Pi.sub_apply, Pi.single_apply, if_neg fun h : j = i ↦ hj (h ▸ hi), sub_zero]
    exact e.2.2 j hj⟩

/-- **`xᵉ = (xᵉ / xᵢ ^ m) xᵢ ^ m`** in `𝒪(m)` over `D₊(∏_{j ∈ s} Xⱼ)`, for `i ∈ s`. -/
lemma twistMonomial_eq_smul {i : n} (hi : i ∈ s) (e : laurentExponents s m) :
    twistMonomial R s e = @SMul.smul _ _
      (moduleTwistSections (n := n) (R := R) (m := m)
        (basicOpen (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1)))).toSMul
      (Proj.awayToSection _ _ (awayMonomial R s (shiftExponent m hi e)))
      (twistMonomial R s (singleExponent (s := s) (m := m) hi)) := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change ((twistMonomial R s e).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
    ((Proj.awayToSection _ _ (awayMonomial R s (shiftExponent m hi e))).1 x).val *
      ((twistMonomial R s (singleExponent (s := s) (m := m) hi)).1 x :
        Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)
  rw [coe_twistMonomial_apply, coe_twistMonomial_apply,
    val_awayToSection_awayMonomial_apply, Localization.mk_mul]
  have h0 := indicator_one_nonneg s
  have ha := add_nsmul_indicator_nonneg e.2.2 (neg_le_negExponentSum e.1)
  have hb := add_nsmul_indicator_nonneg (shiftExponent m hi e).2.2
    (neg_le_negExponentSum (shiftExponent m hi e).1)
  have hc := add_nsmul_indicator_nonneg (singleExponent (s := s) (m := m) hi).2.2
    (neg_le_negExponentSum (singleExponent (s := s) (m := m) hi).1)
  have hN := nsmul_nonneg h0 (negExponentSum (shiftExponent m hi e).1)
  have hN' := nsmul_nonneg h0 (negExponentSum (singleExponent (s := s) (m := m) hi).1)
  refine mk_eq_mk_of_monomialToNat ha (nsmul_nonneg h0 _) (add_nonneg hb hc)
    (add_nonneg hN hN') rfl rfl (monomialToNat_mul hb hc) (monomialToNat_mul hN hN') ?_
  ext j
  simp only [shiftExponent, singleExponent, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.single_apply]
  split_ifs <;> ring


/-- The degree of a nonempty product of distinct variables is positive. -/
lemma indicatorDegree_pos {s : Set n} (hs : s.Nonempty) : 0 < indicatorDegree s := by
  obtain ⟨i, hi⟩ := hs
  have : 0 < (s.indicator (1 : n → ℤ) i).toNat := by simp [Set.indicator_of_mem hi]
  exact this.trans_le (Finset.single_le_sum (f := fun j ↦ (s.indicator (1 : n → ℤ) j).toNat)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i))

/-- The standard open on which a coordinate is invertible. -/
def standardOpen (n : Type v) (R : Type (max u v)) [CommRing R] (index : n) :
    (projectiveSpaceOverAffine n R).Opens :=
  basicOpen (homogeneousSubmodule n R) (X index)

/-- The standard intersection on which all coordinates in `s` are invertible. -/
abbrev monomialOpen (R : Type (max u v)) [CommRing R] (s : Set n) :
    (projectiveSpaceOverAffine n R).Opens :=
  basicOpen (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1))

/-- The inclusion of coefficients agrees with the structure morphism on a standard chart. -/
lemma projectiveSpaceOverAffineToSpec_appTop_res (R : Type (max u v)) [CommRing R]
    {s : Set n} (hs : s.Nonempty) :
    (Scheme.ΓSpecIso (.of R)).inv ≫ (projectiveSpaceOverAffineToSpec n R).appTop ≫
        (projectiveSpaceOverAffine n R).presheaf.map
          (homOfLE (le_top : monomialOpen R s ≤ ⊤)).op =
      CommRingCat.ofHom (algebraMap R
        (Away (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1)))) ≫
          awayToSection _ _ := by
  rw [projectiveSpaceOverAffineToSpec, Scheme.Hom.comp_appTop]
  simp only [Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc,
    toSpecZero_appTop_res _ _ (monomialToNat_indicator_mem R s) (indicatorDegree_pos hs)]
  rfl

set_option maxHeartbeats 400000 in
/-- Laurent monomials form a basis of the functions on a nonempty standard intersection. -/
theorem bijective_sum_awayMonomial (R : Type (max u v)) [CommRing R]
    {s : Set n} (hs : s.Nonempty) :
    Function.Bijective fun coefficients : laurentExponents s 0 →₀ R ↦
      coefficients.sum fun exponent scalar ↦
        ((Scheme.ΓSpecIso (.of R)).inv ≫ (projectiveSpaceOverAffineToSpec n R).appTop ≫
          (projectiveSpaceOverAffine n R).presheaf.map
            (homOfLE (le_top : monomialOpen R s ≤ ⊤)).op) scalar *
          awayToSection _ _ (awayMonomial R s exponent) := by
  haveI : IsIso (awayToSection (homogeneousSubmodule n R)
      (monomialToNat R (s.indicator 1))) := by
    change IsIso (basicOpenIsoAway _ _ (monomialToNat_indicator_mem R s)
      (indicatorDegree_pos hs)).hom
    infer_instance
  let sectionMap : Away (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1)) →+*
      Γ(projectiveSpaceOverAffine n R, monomialOpen R s) :=
    (awayToSection (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1))).hom
  rw [projectiveSpaceOverAffineToSpec_appTop_res R hs]
  change Function.Bijective fun coefficients : laurentExponents s 0 →₀ R ↦
    coefficients.sum fun exponent scalar ↦
      sectionMap (algebraMap R _ scalar) * sectionMap (awayMonomial R s exponent)
  have formula : (fun coefficients : laurentExponents s 0 →₀ R ↦
      coefficients.sum fun exponent scalar ↦
        sectionMap (algebraMap R _ scalar) * sectionMap (awayMonomial R s exponent)) =
      sectionMap ∘ (awayMonomialBasis R s).repr.symm := by
    funext coefficients
    rw [Function.comp_apply, Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply,
      map_finsuppSum]
    refine Finsupp.sum_congr fun exponent _ ↦ ?_
    rw [awayMonomialBasis_apply, Algebra.smul_def, map_mul]
  rw [formula]
  exact (ConcreteCategory.bijective_of_isIso
    (awayToSection (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1)))).comp
      (awayMonomialBasis R s).repr.symm.bijective

open Classical in
variable (m) in
/-- Shifting exponent vectors by `m eᵢ`, for `i ∈ s`, identifies the Laurent monomials of
degree `m` regular on `⋂_{j ∈ s} D₊(xⱼ)` with those of degree `0`. -/
noncomputable def shiftExponentEquiv {s : Set n} {i : n} (hi : i ∈ s) :
    laurentExponents s m ≃ laurentExponents s 0 where
  toFun := Proj.shiftExponent m hi
  invFun e := ⟨e.1 + Pi.single i m, by simp [Finset.sum_add_distrib, e.2.1], fun j hj ↦ by
    rw [Pi.add_apply, Pi.single_apply, if_neg fun h : j = i ↦ hj (h ▸ hi), add_zero]
    exact e.2.2 j hj⟩
  left_inv e := Subtype.ext (by simp [Proj.shiftExponent])
  right_inv e := Subtype.ext (by simp [Proj.shiftExponent])


private noncomputable def twistSectionSum
    {gradedRing gradedSubobjects : Type u} [CommRing gradedRing]
    [SetLike gradedSubobjects gradedRing] [AddSubgroupClass gradedSubobjects gradedRing]
    (grading : ℕ → gradedSubobjects) [GradedRing grading] (degree : ℤ)
    (openSubset : TopologicalSpace.Opens (ProjectiveSpectrum.top (A := gradedRing) grading))
    {coefficientRing : Type*} {exponents : Type*} [Semiring coefficientRing]
    (coefficientMap : coefficientRing → Γ(Proj (A := gradedRing) grading, openSubset))
    (monomials : exponents → Γ(twist (A := gradedRing) grading degree, openSubset)) :
    (exponents →₀ coefficientRing) → Γ(twist (A := gradedRing) grading degree, openSubset) :=
  fun coefficients ↦ coefficients.sum fun exponent scalar ↦
    @SMul.smul _ _
      (modulePresheafInAbObj (A := gradedRing) grading degree (.op openSubset)).toSMul
      (coefficientMap scalar) (monomials exponent)

private noncomputable def projectiveScalarSection (R : Type (max u v)) [CommRing R]
    (s : Set n) : R →+* Γ(projectiveSpaceOverAffine n R, monomialOpen R s) :=
  (((Scheme.ΓSpecIso (.of R)).inv ≫ (projectiveSpaceOverAffineToSpec n R).appTop ≫
    (projectiveSpaceOverAffine n R).presheaf.map
      (homOfLE (le_top : monomialOpen R s ≤ ⊤)).op)).hom

/-- The section `∑ cₑ xᵉ` of `𝒪(m)` on a standard intersection, with coefficients in `R`. -/
noncomputable def twistMonomialSum (R : Type (max u v)) [CommRing R] (s : Set n) (m : ℤ) :
    (laurentExponents s m →₀ R) →
      Γ(twist (homogeneousSubmodule n R) m, monomialOpen R s) :=
  twistSectionSum (gradedRing := MvPolynomial n R)
    (gradedSubobjects := Submodule R (MvPolynomial n R))
    (homogeneousSubmodule n R) m (monomialOpen R s)
    (projectiveScalarSection (n := n) R s) (twistMonomial R s)

private lemma bijective_sum_smul_of_generator
    {coefficientRing : Type*} {scalarRing : Type*} {moduleType : Type*}
    {sourceExponents : Type*} {targetExponents : Type*}
    [Semiring coefficientRing] [Semiring scalarRing] [AddCommMonoid moduleType]
    [Module scalarRing moduleType]
    (coefficientMap : coefficientRing → scalarRing)
    (monomials : sourceExponents → moduleType)
    (degreeZeroMonomials : targetExponents → scalarRing) (generator : moduleType)
    (shift : sourceExponents ≃ targetExponents)
    (monomialFactorization : ∀ exponent,
      monomials exponent = degreeZeroMonomials (shift exponent) • generator)
    (generatorBijective : Function.Bijective fun scalar : scalarRing ↦ scalar • generator)
    (degreeZeroBijective : Function.Bijective fun coefficients : targetExponents →₀ coefficientRing ↦
      coefficients.sum fun exponent scalar ↦ coefficientMap scalar * degreeZeroMonomials exponent) :
    Function.Bijective fun coefficients : sourceExponents →₀ coefficientRing ↦
      coefficients.sum fun exponent scalar ↦ coefficientMap scalar • monomials exponent := by
  have factorization :
      (fun coefficients : sourceExponents →₀ coefficientRing ↦
        coefficients.sum fun exponent scalar ↦ coefficientMap scalar • monomials exponent) =
      (fun scalar : scalarRing ↦ scalar • generator) ∘
      (fun coefficients : targetExponents →₀ coefficientRing ↦
        coefficients.sum fun exponent scalar ↦
          coefficientMap scalar * degreeZeroMonomials exponent) ∘
      Finsupp.equivMapDomain shift := by
    funext coefficients
    simp only [Function.comp_apply, Finsupp.sum_equivMapDomain]
    rw [Finsupp.sum, Finsupp.sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun exponent _ ↦ ?_
    rw [monomialFactorization exponent, smul_smul]
  rw [factorization]
  exact generatorBijective.comp (degreeZeroBijective.comp
    (Finsupp.domCongr (M := coefficientRing) shift).bijective)

private lemma bijective_sum_twist_of_generator
    {gradedRing gradedSubobjects : Type u} [CommRing gradedRing]
    [SetLike gradedSubobjects gradedRing] [AddSubgroupClass gradedSubobjects gradedRing]
    (grading : ℕ → gradedSubobjects) [GradedRing grading] (degree : ℤ)
    (openSubset : TopologicalSpace.Opens (ProjectiveSpectrum.top (A := gradedRing) grading))
    {coefficientRing : Type*} {sourceExponents : Type*} {targetExponents : Type*}
    [Semiring coefficientRing]
    (coefficientMap : coefficientRing → Γ(Proj (A := gradedRing) grading, openSubset))
    (monomials : sourceExponents → Γ(twist (A := gradedRing) grading degree, openSubset))
    (degreeZeroMonomials : targetExponents → Γ(Proj (A := gradedRing) grading, openSubset))
    (generator : Γ(twist (A := gradedRing) grading degree, openSubset))
    (shift : sourceExponents ≃ targetExponents)
    (monomialFactorization : ∀ exponent, monomials exponent = @SMul.smul _ _
      (modulePresheafInAbObj (A := gradedRing) grading degree (.op openSubset)).toSMul
      (degreeZeroMonomials (shift exponent)) generator)
    (generatorFree : Scheme.Modules.IsFreeGenerator
      (M := twist (A := gradedRing) grading degree) generator)
    (degreeZeroBijective : Function.Bijective fun coefficients : targetExponents →₀ coefficientRing ↦
      coefficients.sum fun exponent scalar ↦ coefficientMap scalar * degreeZeroMonomials exponent) :
    Function.Bijective
      (twistSectionSum (gradedRing := gradedRing) (gradedSubobjects := gradedSubobjects)
        grading degree openSubset coefficientMap monomials) := by
  change Function.Bijective fun coefficients : sourceExponents →₀ coefficientRing ↦
    coefficients.sum fun exponent scalar ↦ @SMul.smul _ _
      (modulePresheafInAbObj (A := gradedRing) grading degree (.op openSubset)).toSMul
      (coefficientMap scalar) (monomials exponent)
  have generatorBijective :
      Function.Bijective fun scalar : Γ(Proj (A := gradedRing) grading, openSubset) ↦
      @SMul.smul _ _ (modulePresheafInAbObj (A := gradedRing) grading degree (.op openSubset)).toSMul
        scalar generator := generatorFree.bijective
  exact @bijective_sum_smul_of_generator coefficientRing
    Γ(Proj (A := gradedRing) grading, openSubset)
    Γ(twist (A := gradedRing) grading degree, openSubset)
    sourceExponents targetExponents inferInstance inferInstance inferInstance
    (modulePresheafInAbObj (A := gradedRing) grading degree (.op openSubset))
    coefficientMap monomials degreeZeroMonomials generator shift
    monomialFactorization generatorBijective degreeZeroBijective

/-- Laurent monomials of total degree `m` form a basis of the sections of `𝒪(m)`
on a nonempty standard intersection. -/
theorem bijective_sum_twistMonomial (R : Type (max u v)) [CommRing R]
    {s : Set n} (hs : s.Nonempty) (m : ℤ) :
    @Function.Bijective (laurentExponents s m →₀ R)
      Γ(twist (homogeneousSubmodule n R) m, monomialOpen R s)
      (twistMonomialSum (n := n) R s m) := by
  obtain ⟨index, membership⟩ := hs
  have monomialFactorization (exponent : laurentExponents s m) :=
    twistMonomial_eq_smul (n := n) (R := R) (s := s) (m := m) membership exponent
  have generatorFree := isFreeGenerator_twistMonomial_singleExponent
    (n := n) (R := R) (s := s) (m := m) membership
  have degreeZeroBijective := bijective_sum_awayMonomial (n := n) R (s := s) ⟨index, membership⟩
  have scalarMap_eq (scalar : R) :
      projectiveScalarSection R s scalar =
        ((Scheme.ΓSpecIso (.of R)).inv ≫ (projectiveSpaceOverAffineToSpec n R).appTop ≫
          (projectiveSpaceOverAffine n R).presheaf.map
            (homOfLE (le_top : monomialOpen R s ≤ ⊤)).op) scalar := by
    unfold projectiveScalarSection
    rfl
  simp_rw [← scalarMap_eq] at degreeZeroBijective
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      have nativeSpecialization := bijective_sum_twist_of_generator
        (gradedRing := MvPolynomial n R) (coefficientRing := R)
        (sourceExponents := laurentExponents s m) (targetExponents := laurentExponents s 0)
        (homogeneousSubmodule n R) m
        (basicOpen (homogeneousSubmodule n R) (monomialToNat R (s.indicator 1)))
        (projectiveScalarSection (n := n) R s) (twistMonomial R s)
        (fun exponent ↦ awayToSection (homogeneousSubmodule n R)
          (monomialToNat R (s.indicator 1)) (awayMonomial R s exponent))
        (twistMonomial R s (singleExponent (s := s) (m := m) membership))
        (shiftExponentEquiv m membership) monomialFactorization generatorFree
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      have nativeBijective := nativeSpecialization degreeZeroBijective
  exact nativeBijective

/-- A finite standard intersection is the basic open of the product of its coordinates. -/
lemma monomialOpen_range {p : ℕ} (R : Type (max u v)) [CommRing R]
    (indices : Fin (p + 1) → n) :
    monomialOpen R (Set.range indices) = ⨅ index, standardOpen n R (indices index) := by
  refine le_antisymm (le_iInf fun index _ membership ↦
    mem_basicOpen_monomialToNat_indicator.1 membership _ (Set.mem_range_self index))
    fun point membership ↦ ?_
  refine mem_basicOpen_monomialToNat_indicator.2 ?_
  rintro _ ⟨index, rfl⟩
  exact (iInf_le (fun index ↦ standardOpen n R (indices index)) index) membership

end AlgebraicGeometry.Proj
