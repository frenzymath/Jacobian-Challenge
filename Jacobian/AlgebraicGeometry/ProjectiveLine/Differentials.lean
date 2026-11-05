import Mathlib.Algebra.Polynomial.Derivation
import Jacobian.AlgebraicGeometry.Modules.DifferentialsSections
import Jacobian.AlgebraicGeometry.Modules.LocalDerivation
import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Hom
import Jacobian.AlgebraicGeometry.ProjectiveLine.BasicOpens
import Jacobian.AlgebraicGeometry.ProjectiveSpace.LaurentMonomial

/-!
# Differentials of the projective line

The relative cotangent sheaf of the polynomial projective line over a field is
`𝒪(-2)`. On the two standard affine charts the comparison sends `dt` to the
standard generator and `ds` to its negative. The identity `s = t⁻¹` gives the
transition law, so these derivations and their inverse maps glue.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.ProjectiveLine

open Scheme.Modules ProjectiveSpectrum.Twist
open Proj (twist)

attribute [local instance] MvPolynomial.gradedAlgebra

variable (baseField : Type u) [Field baseField]

private abbrev polynomialLine : Scheme.{u} :=
  Proj (homogeneousSubmodule (Fin 2) baseField)

private abbrev polynomialLineToSpec : polynomialLine baseField ⟶ Spec (.of baseField) :=
  Proj.toSpecZero (homogeneousSubmodule (Fin 2) baseField) ≫
    Spec.map (CommRingCat.ofHom (algebraMap baseField (homogeneousSubmodule (Fin 2) baseField 0)))

/-- The intersection of the standard coordinate opens indexed by a set. -/
private abbrev monomialChart (s : Set (Fin 2)) : (polynomialLine baseField).Opens :=
  Proj.monomialOpen baseField s

private lemma monomialChart_mono {s t : Set (Fin 2)} (hts : t ⊆ s) :
    monomialChart baseField s ≤ monomialChart baseField t :=
  Proj.basicOpen_monomialToNat_indicator_mono hts

/-- Degree-zero fractions as functions on a standard affine intersection. -/
private def chartFun (s : Set (Fin 2)) :
    Away (homogeneousSubmodule (Fin 2) baseField)
      (monomialToNat baseField (s.indicator 1)) →+*
      Γ(polynomialLine baseField, monomialChart baseField s) :=
  (Proj.awayToSection _ _).hom

/-- The constant functions on an open of `ℙ¹_k`. -/
private def chartConst (V : (polynomialLine baseField).Opens) :
    baseField →+* Γ(polynomialLine baseField, V) :=
  ((Scheme.ΓSpecIso (.of baseField)).inv ≫ (polynomialLineToSpec baseField).appTop ≫
    (polynomialLine baseField).presheaf.map (homOfLE le_top).op).hom

private lemma presheaf_map_chartConst {V W : (polynomialLine baseField).Opens} (h : W ≤ V) (c : baseField) :
    (polynomialLine baseField).presheaf.map (homOfLE h).op (chartConst baseField V c) =
      chartConst baseField W c := by
  simp only [chartConst, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [Scheme.presheaf_map_map_apply]
  rfl

private lemma presheaf_map_chartFun_awayMonomial {s t : Set (Fin 2)} (hts : t ⊆ s)
    (e : laurentExponents t 0) :
    (polynomialLine baseField).presheaf.map (homOfLE (monomialChart_mono baseField hts)).op
        (chartFun baseField t (awayMonomial _ t e)) =
      chartFun baseField s (awayMonomial _ s ⟨e.1, e.2.1, fun i hi ↦ e.2.2 i fun h ↦ hi (hts h)⟩) :=
  Proj.presheaf_map_awayToSection_awayMonomial hts e

section Coordinates

variable {i j : Fin 2} (hij : i ≠ j)

include hij in
private lemma eq_or_eq_of_ne (l : Fin 2) : l = i ∨ l = j := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  obtain ⟨l, hl⟩ := l
  simp only [ne_eq, Fin.mk.injEq] at hij ⊢
  omega

include hij in
private lemma sum_eq_add_of_ne {M : Type*} [AddCommMonoid M] (f : Fin 2 → M) :
    ∑ l, f l = f i + f j :=
  Fintype.sum_eq_add i j hij fun l hl ↦ ((eq_or_eq_of_ne hij l).elim hl.1 hl.2).elim

/-- The exponent vector of the affine coordinate `xⱼ / xᵢ` on `D₊(xᵢ)`. -/
private def coordExp : laurentExponents ({i} : Set (Fin 2)) 0 :=
  ⟨Pi.single j 1 - Pi.single i 1, by simp [Finset.sum_sub_distrib], fun l hl ↦ by
    rw [Set.mem_singleton_iff] at hl
    simp only [Pi.sub_apply, Pi.single_apply, if_neg hl, sub_zero]
    split_ifs <;> norm_num⟩

/-- The affine coordinate `xⱼ / xᵢ` on `D₊(xᵢ)`. -/
private def coord : Γ(polynomialLine baseField, monomialChart baseField {i}) :=
  chartFun baseField {i} (awayMonomial _ {i} (coordExp (i := i) (j := j)))

/-- Every Laurent monomial regular on `D₊(xᵢ)` is a power of `xⱼ / xᵢ`. -/
private def coordExpEquiv : ℕ ≃ laurentExponents ({i} : Set (Fin 2)) 0 where
  toFun m := ⟨m • (coordExp (i := i) (j := j)).1, by
    simp only [Pi.smul_apply, nsmul_eq_mul, ← Finset.mul_sum, (coordExp (i := i) (j := j)).2.1,
      mul_zero],
    fun l hl ↦ nsmul_nonneg ((coordExp (i := i) (j := j)).2.2 l hl) m⟩
  invFun e := (e.1 j).toNat
  left_inv m := by simp [coordExp, hij.symm]
  right_inv e := by
    have hj := e.2.2 j (by simpa using hij.symm)
    have hs := e.2.1
    rw [sum_eq_add_of_ne hij] at hs
    refine Subtype.ext (funext fun l ↦ ?_)
    rcases eq_or_eq_of_ne hij l with rfl | rfl
    · simp [coordExp, hij]
      omega
    · simp [coordExp, hij.symm]
      omega

private lemma chartFun_coordExpEquiv (m : ℕ) :
    chartFun baseField {i} (awayMonomial _ _ (coordExpEquiv hij m)) = coord baseField (i := i) (j := j) ^ m := by
  rw [coord, ← map_pow, ← Proj.awayMonomial_pow _ m (coordExpEquiv hij m) rfl]

/-- The ring homomorphism `baseField[X] → Γ(D₊(xᵢ))`, `X ↦ xⱼ / xᵢ`. -/
private def polyToChart : Polynomial baseField →+* Γ(polynomialLine baseField, monomialChart baseField {i}) :=
  Polynomial.eval₂RingHom (chartConst baseField (monomialChart baseField {i})) (coord baseField (i := i) (j := j))

include hij in
/-- **The functions on the standard monomialChart `D₊(xᵢ)` of `ℙ¹_k` are the polynomials in
`xⱼ / xᵢ`.** -/
private lemma bijective_polyToChart : Function.Bijective (polyToChart baseField (i := i) (j := j)) := by
  have hB := Proj.bijective_sum_awayMonomial (n := Fin 2) baseField (Set.singleton_nonempty i)
  change Function.Bijective (fun coefficients : laurentExponents ({i} : Set (Fin 2)) 0 →₀ baseField ↦
    coefficients.sum fun exponent scalar ↦
      chartConst baseField (monomialChart baseField {i}) scalar *
        chartFun baseField {i} (awayMonomial baseField {i} exponent)) at hB
  let g : Polynomial baseField ≃ (laurentExponents ({i} : Set (Fin 2)) 0 →₀ baseField) :=
    (Polynomial.toFinsuppIso baseField).toEquiv.trans
      ((AddMonoidAlgebra.coeffEquiv (R := baseField) (M := ℕ)).trans
        (Finsupp.equivCongrLeft (coordExpEquiv hij)))
  have formula : (polyToChart baseField (i := i) (j := j) :
      Polynomial baseField → Γ(polynomialLine baseField, monomialChart baseField {i})) =
      (fun coefficients : laurentExponents ({i} : Set (Fin 2)) 0 →₀ baseField ↦
        coefficients.sum fun exponent scalar ↦
          chartConst baseField (monomialChart baseField {i}) scalar *
            chartFun baseField {i} (awayMonomial baseField {i} exponent)) ∘ g := by
    funext polynomial
    rw [Function.comp_apply]
    simp only [g, Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
      Polynomial.toFinsuppIso_apply, AddMonoidAlgebra.coeffEquiv_apply,
      Finsupp.equivCongrLeft_apply, Finsupp.sum_equivMapDomain]
    rw [polyToChart, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
      Finsupp.sum, Polynomial.support_toFinsupp]
    refine Finset.sum_congr rfl fun degree _ ↦ ?_
    rw [Polynomial.toFinsupp_apply, ← chartFun_coordExpEquiv baseField hij]
  rw [formula]
  exact hB.comp g.bijective

/-- The ring isomorphism `baseField[X] ≅ Γ(D₊(xᵢ))`, `X ↦ xⱼ / xᵢ`. -/
private def laurentPolyEquivChart : Polynomial baseField ≃+* Γ(polynomialLine baseField, monomialChart baseField {i}) :=
  RingEquiv.ofBijective _ (bijective_polyToChart baseField hij)

private lemma laurentPolyEquivChart_apply (p : Polynomial baseField) :
    laurentPolyEquivChart baseField hij p = polyToChart baseField (i := i) (j := j) p :=
  rfl

private lemma laurentPolyEquivChart_symm_coord :
    (laurentPolyEquivChart baseField hij).symm (coord baseField (i := i) (j := j)) = Polynomial.X :=
  (laurentPolyEquivChart baseField hij).symm_apply_eq.2 (by simp [laurentPolyEquivChart_apply, polyToChart])

private lemma laurentPolyEquivChart_symm_chartConst (c : baseField) :
    (laurentPolyEquivChart baseField hij).symm (chartConst baseField _ c) = Polynomial.C c :=
  (laurentPolyEquivChart baseField hij).symm_apply_eq.2 (by simp [laurentPolyEquivChart_apply, polyToChart])

end Coordinates

section Charts

private lemma isAffineOpen_monomialChart {s : Set (Fin 2)} (hs : s.Nonempty) :
    IsAffineOpen (monomialChart baseField s) :=
  Proj.isAffineOpen_basicOpen _ _ (monomialToNat_indicator_mem baseField s)
    (Proj.indicatorDegree_pos hs)

/-- The generator `xᵢ⁻²` of `𝒪(-2)` over `D₊(xᵢ)`. -/
private def twistGen (i : Fin 2) :
    Γ(twist (homogeneousSubmodule (Fin 2) baseField) (-2), monomialChart baseField {i}) :=
  Proj.twistMonomial baseField {i}
    (Proj.singleExponent (s := {i}) (m := -2) (Set.mem_singleton i))

private lemma isFreeGenerator_twistGen (i : Fin 2) : IsFreeGenerator (twistGen baseField i) :=
  Proj.isFreeGenerator_twistMonomial_singleExponent (Set.mem_singleton _)

variable {i j : Fin 2} (hij : i ≠ j) (σ : ℤ)

/-- The derivation `σ d / d(xⱼ / xᵢ)` of `Γ(D₊(xᵢ)) = baseField[xⱼ / xᵢ]`, with values in `𝒪(-2)`
through its generator `xᵢ⁻²`. -/
private def chartDerivation :
    Γ(polynomialLine baseField, monomialChart baseField {i}) →+
      Γ(twist (homogeneousSubmodule (Fin 2) baseField) (-2), monomialChart baseField {i}) where
  toFun f := σ • ((laurentPolyEquivChart baseField hij
    (Polynomial.derivative ((laurentPolyEquivChart baseField hij).symm f))) • twistGen baseField i)
  map_zero' := by simp
  map_add' f g := by simp [add_smul]

private lemma chartDerivation_apply (f : Γ(polynomialLine baseField, monomialChart baseField {i})) :
    chartDerivation baseField hij σ f = σ • ((laurentPolyEquivChart baseField hij
      (Polynomial.derivative ((laurentPolyEquivChart baseField hij).symm f))) • twistGen baseField i) :=
  rfl

private lemma chartDerivation_mul (f g : Γ(polynomialLine baseField, monomialChart baseField {i})) :
    chartDerivation baseField hij σ (f * g) =
      f • chartDerivation baseField hij σ g + g • chartDerivation baseField hij σ f := by
  simp only [chartDerivation_apply, map_mul, Polynomial.derivative_mul, map_add,
    RingEquiv.apply_symm_apply, add_smul, mul_smul, smul_add]
  module

private lemma chartDerivation_coord :
    chartDerivation baseField hij σ (coord baseField (i := i) (j := j)) = σ • twistGen baseField i := by
  simp [chartDerivation_apply, laurentPolyEquivChart_symm_coord]

private lemma chartDerivation_chartConst (c : baseField) : chartDerivation baseField hij σ (chartConst baseField _ c) = 0 := by
  simp [chartDerivation_apply, laurentPolyEquivChart_symm_chartConst]

/-- The local derivation over `D₊(xᵢ)` extending `chartDerivation`. -/
private def chartLocalDerivation : LocalDerivation (twist (homogeneousSubmodule (Fin 2) baseField) (-2))
    (monomialChart baseField {i}) :=
  LocalDerivation.ofIsAffineOpen (isAffineOpen_monomialChart baseField (Set.singleton_nonempty i))
    (chartDerivation baseField hij σ) (chartDerivation_mul baseField hij σ)

end Charts

section Overlap

/-- The intersection `D₊(x₀) ∩ D₊(x₁)`. -/
private abbrev overlap : (polynomialLine baseField).Opens := monomialChart baseField Set.univ

private lemma overlap_le_chart (i : Fin 2) : overlap baseField ≤ monomialChart baseField {i} :=
  monomialChart_mono baseField (Set.subset_univ _)

private lemma mem_chart_iff {s : Set (Fin 2)} {x : polynomialLine baseField} :
    x ∈ monomialChart baseField s ↔
      ∀ i ∈ s, x ∈ Proj.basicOpen (homogeneousSubmodule (Fin 2) baseField) (X i) :=
  Proj.mem_basicOpen_monomialToNat_indicator

private lemma chart_singleton (i : Fin 2) : monomialChart baseField {i} =
    Proj.basicOpen (homogeneousSubmodule (Fin 2) baseField) (X i) :=
  Opens.ext (Set.ext fun _ ↦ (mem_chart_iff baseField).trans (by simp))

private lemma le_overlap {i j : Fin 2} (hij : i ≠ j) {W : (polynomialLine baseField).Opens}
    (hi : W ≤ monomialChart baseField {i}) (hj : W ≤ monomialChart baseField {j}) : W ≤ overlap baseField := fun _ hx ↦
  (mem_chart_iff baseField).2 fun l _ ↦ (eq_or_eq_of_ne hij l).elim
    (fun h ↦ h ▸ chart_singleton baseField i ▸ hi hx) fun h ↦ h ▸ chart_singleton baseField j ▸ hj hx

private lemma iSup_chart : ⨆ i, monomialChart baseField {i} = ⊤ := by
  simp only [chart_singleton]
  apply Proj.iSup_basicOpen_eq_top
  rw [MvPolynomial.toIdeal_irrelevant_homogeneousSubmodule]

variable {i j : Fin 2}

/-- The Laurent monomial `xⱼ / xᵢ` on the overlap. -/
private def overlapCoordExp (i j : Fin 2) :
    laurentExponents (Set.univ : Set (Fin 2)) 0 :=
  ⟨(coordExp (i := i) (j := j)).1, (coordExp (i := i) (j := j)).2.1, fun _ hl ↦ (hl trivial).elim⟩

private lemma coord_restrict :
    (polynomialLine baseField).presheaf.map (homOfLE (overlap_le_chart baseField i)).op
        (coord baseField (i := i) (j := j)) =
      chartFun baseField Set.univ (awayMonomial _ _ (overlapCoordExp i j)) :=
  presheaf_map_chartFun_awayMonomial baseField (Set.subset_univ _) _

private lemma coord_mul_coord :
    (polynomialLine baseField).presheaf.map (homOfLE (overlap_le_chart baseField i)).op
        (coord baseField (i := i) (j := j)) *
      (polynomialLine baseField).presheaf.map (homOfLE (overlap_le_chart baseField j)).op
        (coord baseField (i := j) (j := i)) = 1 := by
  rw [coord_restrict, coord_restrict, ← map_mul,
    Proj.awayMonomial_mul _ _ ⟨0, by simp, fun _ _ ↦ le_rfl⟩ (by
      funext l
      simp only [overlapCoordExp, coordExp, Pi.zero_apply, Pi.add_apply, Pi.sub_apply]
      ring),
    Proj.awayMonomial_zero _ rfl, map_one]

private lemma twistGen_restrict :
    (twist (homogeneousSubmodule (Fin 2) baseField) (-2)).presheaf.map
        (homOfLE (overlap_le_chart baseField i)).op (twistGen baseField i) =
      ((polynomialLine baseField).presheaf.map (homOfLE (overlap_le_chart baseField i)).op
        (coord baseField (i := i) (j := j))) ^ 2 •
      (twist (homogeneousSubmodule (Fin 2) baseField) (-2)).presheaf.map
        (homOfLE (overlap_le_chart baseField j)).op (twistGen baseField j) := by
  have hi := Proj.twist_presheaf_map_twistMonomial (R := baseField) (m := -2)
    (Set.subset_univ {i}) (Proj.singleExponent (s := {i}) (m := -2) (Set.mem_singleton i))
  have hj := Proj.twist_presheaf_map_twistMonomial (R := baseField) (m := -2)
    (Set.subset_univ {j}) (Proj.singleExponent (s := {j}) (m := -2) (Set.mem_singleton j))
  rw [twistGen, twistGen, hi, hj, Proj.twistMonomial_eq_smul (Set.mem_univ j), coord_restrict,
    ← map_pow, ← Proj.awayMonomial_pow _ 2 _ ?_]
  · rfl
  · funext l
    simp only [Proj.shiftExponent, Proj.singleExponent, overlapCoordExp, coordExp, Pi.sub_apply,
      Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp_all

private lemma closure_overlap (hij : i ≠ j) :
    Subring.closure (Set.range (chartConst baseField (overlap baseField)) ∪
      {(polynomialLine baseField).presheaf.map (homOfLE (overlap_le_chart baseField i)).op
        (coord baseField (i := i) (j := j)),
       (polynomialLine baseField).presheaf.map (homOfLE (overlap_le_chart baseField j)).op
        (coord baseField (i := j) (j := i))}) = ⊤ := by
  set T := Subring.closure (Set.range (chartConst baseField (overlap baseField)) ∪
      {(polynomialLine baseField).presheaf.map (homOfLE (overlap_le_chart baseField i)).op
        (coord baseField (i := i) (j := j)),
       (polynomialLine baseField).presheaf.map (homOfLE (overlap_le_chart baseField j)).op
        (coord baseField (i := j) (j := i))})
  have hmono (e : laurentExponents (Set.univ : Set (Fin 2)) 0) :
      chartFun baseField Set.univ (awayMonomial _ _ e) ∈ T := by
    have hs := e.2.1
    rw [sum_eq_add_of_ne hij] at hs
    rcases le_total 0 (e.1 j) with h | h
    · rw [Proj.awayMonomial_pow (overlapCoordExp i j) (e.1 j).toNat e ?_,
        RingHom.map_pow (chartFun baseField Set.univ) _ (e.1 j).toNat,
        ← coord_restrict]
      · exact T.pow_mem (Subring.subset_closure (by simp)) _
      · funext l
        rcases eq_or_eq_of_ne hij l with rfl | rfl
        · simp [overlapCoordExp, coordExp, hij]
          omega
        · simp [overlapCoordExp, coordExp, hij.symm]
          omega
    · rw [Proj.awayMonomial_pow (overlapCoordExp j i) (e.1 i).toNat e ?_,
        RingHom.map_pow (chartFun baseField Set.univ) _ (e.1 i).toNat,
        ← coord_restrict]
      · exact T.pow_mem (Subring.subset_closure (by simp)) _
      · funext l
        rcases eq_or_eq_of_ne hij l with rfl | rfl
        · simp [overlapCoordExp, coordExp, hij]
          omega
        · simp [overlapCoordExp, coordExp, hij.symm]
          omega
  refine eq_top_iff.2 fun f _ ↦ ?_
  obtain ⟨c, rfl⟩ := (Proj.bijective_sum_awayMonomial (n := Fin 2) baseField
    (Set.univ_nonempty (α := Fin 2))).2 f
  refine Subring.sum_mem _ fun e _ ↦ Subring.mul_mem _
    (Subring.subset_closure (Or.inl ⟨c e, rfl⟩)) (hmono e)

end Overlap

section Glue

variable {i j : Fin 2}

omit [Field baseField] in
private lemma neg_sq_smul_neg_zsmul_sq_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {x y : R} (h : x * y = 1) (τ : ℤ) (g : M) : -(y ^ 2) • -τ • x ^ 2 • g = τ • g := by
  rw [neg_smul, neg_smul, smul_neg, neg_neg, smul_comm (y ^ 2) τ, smul_smul, ← mul_pow,
    mul_comm y x, h, one_pow, one_smul]

private lemma chartLocalDerivation_app_self (hij : i ≠ j) (σ : ℤ)
    (f : Γ(polynomialLine baseField, monomialChart baseField {i})) :
    (chartLocalDerivation baseField hij σ).app (monomialChart baseField {i}) le_rfl f = chartDerivation baseField hij σ f :=
  LocalDerivation.ofIsAffineOpen_app_self _ _ _ f

private lemma chartLocalDerivation_app_restrict (hij : i ≠ j) (σ : ℤ)
    {W : (polynomialLine baseField).Opens}
    (hW : W ≤ monomialChart baseField {i}) (f : Γ(polynomialLine baseField, monomialChart baseField {i})) :
    (chartLocalDerivation baseField hij σ).app W hW
        ((polynomialLine baseField).presheaf.map (homOfLE hW).op f) =
      (twist (homogeneousSubmodule (Fin 2) baseField) (-2)).presheaf.map (homOfLE hW).op
        (chartDerivation baseField hij σ f) := by
  rw [← chartLocalDerivation_app_self baseField hij σ f]
  exact (chartLocalDerivation baseField hij σ).naturality _ _ le_rfl hW f

/-- **The chain rule on `D₊(x₀) ∩ D₊(x₁)`.** The derivations `σ d/d(xⱼ/xᵢ)` on `D₊(xᵢ)` and
`τ d/d(xᵢ/xⱼ)` on `D₊(xⱼ)`, with values in `𝒪(-2)` through `xᵢ⁻²` and `xⱼ⁻²`, agree on the
overlap if `σ = -τ`. -/
private lemma chartLocalDerivation_agree (hij : i ≠ j) (σ τ : ℤ) (hστ : σ = -τ)
    (W : (polynomialLine baseField).Opens) (hi : W ≤ monomialChart baseField {i}) (hj : W ≤ monomialChart baseField {j})
    (a : Γ(polynomialLine baseField, W)) :
    (chartLocalDerivation baseField hij σ).app W hi a = (chartLocalDerivation baseField hij.symm τ).app W hj a := by
  set D₁ := (chartLocalDerivation baseField hij σ).restrict (overlap_le_chart baseField i)
  set D₂ := (chartLocalDerivation baseField hij.symm τ).restrict (overlap_le_chart baseField j)
  have hD₁ : ∀ f, D₁.app (overlap baseField) le_rfl
      ((polynomialLine baseField).presheaf.map (homOfLE (overlap_le_chart baseField i)).op f) =
      (twist (homogeneousSubmodule (Fin 2) baseField) (-2)).presheaf.map
        (homOfLE (overlap_le_chart baseField i)).op (chartDerivation baseField hij σ f) :=
    chartLocalDerivation_app_restrict baseField hij σ _
  have hD₂ : ∀ f, D₂.app (overlap baseField) le_rfl
      ((polynomialLine baseField).presheaf.map (homOfLE (overlap_le_chart baseField j)).op f) =
      (twist (homogeneousSubmodule (Fin 2) baseField) (-2)).presheaf.map
        (homOfLE (overlap_le_chart baseField j)).op (chartDerivation baseField hij.symm τ f) :=
    chartLocalDerivation_app_restrict baseField hij.symm τ _
  have hc := coord_mul_coord baseField (i := i) (j := j)
  have hc' := coord_mul_coord baseField (i := j) (j := i)
  have hg := twistGen_restrict baseField (i := i) (j := j)
  have key : ∀ a, D₁.app (overlap baseField) le_rfl a = D₂.app (overlap baseField) le_rfl a := by
    refine LocalDerivation.app_eq_of_closure D₁ D₂ le_rfl _ (closure_overlap baseField hij) ?_
    rintro a (⟨c, rfl⟩ | rfl | rfl)
    · conv_lhs => rw [← presheaf_map_chartConst baseField (overlap_le_chart baseField i) c]
      conv_rhs => rw [← presheaf_map_chartConst baseField (overlap_le_chart baseField j) c]
      rw [hD₁, hD₂, chartDerivation_chartConst, chartDerivation_chartConst, map_zero, map_zero]
    · rw [hD₁, D₂.app_eq_neg_sq_smul_of_mul_eq_one le_rfl hc, hD₂, chartDerivation_coord,
        chartDerivation_coord, map_zsmul, map_zsmul, hg, hστ]
      module
    · rw [hD₂, D₁.app_eq_neg_sq_smul_of_mul_eq_one le_rfl hc', hD₁, chartDerivation_coord,
        chartDerivation_coord, map_zsmul, map_zsmul, hg, hστ]
      exact neg_sq_smul_neg_zsmul_sq_smul hc _ _
  exact LocalDerivation.ext_of_isAffineOpen (isAffineOpen_monomialChart baseField (Set.univ_nonempty)) D₁ D₂ key W
    (le_overlap baseField hij hi hj) a

/-- The other homogeneous coordinate. -/
private def other (i : Fin 2) : Fin 2 :=
  i.rev

private lemma ne_other (i : Fin 2) : i ≠ other i := by
  obtain ⟨i, hi⟩ := i
  simp only [other, ne_eq, Fin.ext_iff, Fin.val_rev]
  omega

private lemma other_eq (hij : i ≠ j) : other i = j :=
  ((eq_or_eq_of_ne (ne_other i) j).resolve_left hij.symm).symm

/-- The sign `1` on `D₊(x₀)` and `-1` on `D₊(x₁)`. -/
private def sign (i : Fin 2) : ℤ :=
  if i = 0 then 1 else -1

private lemma sign_eq_neg (hij : i ≠ j) : sign i = -sign j := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  simp only [ne_eq, Fin.mk.injEq] at hij
  simp only [sign, Fin.ext_iff]
  split_ifs <;> omega

/-- The derivation `sign i • d / d(x_{other i} / xᵢ)` over `D₊(xᵢ)`. -/
private def localD (i : Fin 2) :
    LocalDerivation (twist (homogeneousSubmodule (Fin 2) baseField) (-2)) (monomialChart baseField {i}) :=
  chartLocalDerivation baseField (ne_other i) (sign i)

private lemma chartLocalDerivation_congr {j' : Fin 2} (hij : i ≠ j) (hij' : i ≠ j')
    (h : j = j') (σ : ℤ) : chartLocalDerivation baseField hij σ = chartLocalDerivation baseField hij' σ := by
  subst h
  rfl

private lemma localD_agree (i j : Fin 2) (W : (polynomialLine baseField).Opens)
    (hi : W ≤ monomialChart baseField {i}) (hj : W ≤ monomialChart baseField {j}) (a : Γ(polynomialLine baseField, W)) :
    (localD baseField i).app W hi a = (localD baseField j).app W hj a := by
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [localD, localD, chartLocalDerivation_congr baseField (ne_other i) hij (other_eq hij),
      chartLocalDerivation_congr baseField (ne_other j) (Ne.symm hij) (other_eq (Ne.symm hij))]
    exact chartLocalDerivation_agree baseField hij _ _ (sign_eq_neg hij) W hi hj a

/-- **The derivation `𝒪 → 𝒪(-2)`** on `ℙ¹_k`, given by `d/dt` on `D₊(x₀)` and `-d/ds` on
`D₊(x₁)`. -/
private def twistDerivation : LocalDerivation (twist (homogeneousSubmodule (Fin 2) baseField) (-2)) ⊤ :=
  LocalDerivation.glueCover (fun i ↦ monomialChart baseField {i}) (iSup_chart baseField) (localD baseField) (localD_agree baseField)

private lemma twistDerivation_app (i : Fin 2) (W : (polynomialLine baseField).Opens)
    (hW : W ≤ monomialChart baseField {i}) (a : Γ(polynomialLine baseField, W)) :
    (twistDerivation baseField).app W le_top a = (localD baseField i).app W hW a :=
  LocalDerivation.glueCover_app _ _ _ _ i W hW a

private lemma appLE_top_eq_chartConst (W : (polynomialLine baseField).Opens)
    (e : W ≤ (polynomialLineToSpec baseField) ⁻¹ᵁ ⊤) (c : Γ(Spec (.of baseField), ⊤)) :
    (polynomialLineToSpec baseField).appLE ⊤ W e c =
      chartConst baseField W ((Scheme.ΓSpecIso (.of baseField)).hom c) := by
  simp only [chartConst, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply]
  rfl

private lemma twistDerivation_appLE (U : (Spec (.of baseField)).Opens) (V : (polynomialLine baseField).Opens)
    (e : V ≤ (polynomialLineToSpec baseField) ⁻¹ᵁ U) (c : Γ(Spec (.of baseField), U)) :
    (twistDerivation baseField).app V le_top
      ((polynomialLineToSpec baseField).appLE U V e c) = 0 := by
  by_cases hV : V = ⊥
  · subst hV
    have := subsingleton_sections_bot (twist (homogeneousSubmodule (Fin 2) baseField) (-2))
    exact Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty V).1 hV
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ ↦ Subsingleton.elim
    ((polynomialLineToSpec baseField).base x) y ▸ e hx
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, (twist (homogeneousSubmodule (Fin 2) baseField) (-2)).isSheaf⟩
    (fun i ↦ V ⊓ monomialChart baseField {i}) V (fun _ ↦ homOfLE inf_le_left) (fun y hy ↦ ?_) _ 0 fun i ↦ ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp ((iSup_chart baseField).ge (Set.mem_univ y))
    exact Opens.mem_iSup.mpr ⟨i, hy, hi⟩
  · rw [map_zero, ← (twistDerivation baseField).naturality V _ le_top inf_le_left]
    have h1 : (polynomialLine baseField).presheaf.map
        (homOfLE (inf_le_left : V ⊓ monomialChart baseField {i} ≤ V)).op
          ((polynomialLineToSpec baseField).appLE ⊤ V e c) =
        (polynomialLine baseField).presheaf.map
          (homOfLE (inf_le_right : V ⊓ monomialChart baseField {i} ≤ monomialChart baseField {i})).op
          (chartConst baseField (monomialChart baseField {i}) ((Scheme.ΓSpecIso (.of baseField)).hom c)) := by
      rw [presheaf_map_chartConst, ← appLE_top_eq_chartConst baseField _ (inf_le_left.trans e)]
      exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_map _ e _) c
    rw [h1, twistDerivation_app baseField i _ inf_le_right, localD, chartLocalDerivation_app_restrict,
      chartDerivation_chartConst, map_zero]

end Glue

section Differentials

/-- The universal derivation `d : 𝒪 → Ω¹_{ℙ¹/baseField}`, as a local derivation. -/
private def dΩ : LocalDerivation (polynomialLineToSpec baseField).relativeDifferentials ⊤ :=
  LocalDerivation.ofDerivation'
    (polynomialLineToSpec baseField).relativeDifferentialsDerivation

/-- **The morphism `Ω¹_{ℙ¹/baseField} ⟶ 𝒪(-2)`** induced by the derivation `twistDerivation`. -/
private def toTwist : (polynomialLineToSpec baseField).relativeDifferentials ⟶
    twist (homogeneousSubmodule (Fin 2) baseField) (-2) :=
  ((polynomialLineToSpec baseField).relativeDifferentialsHomEquiv _).symm
    (LocalDerivation.toDerivation' _ (twistDerivation baseField) (twistDerivation_appLE baseField))

private lemma toTwist_app_dΩ (V : (polynomialLine baseField).Opens)
    (a : Γ(polynomialLine baseField, V)) :
    (toTwist baseField).app V ((dΩ baseField).app V le_top a) = (twistDerivation baseField).app V le_top a := by
  have := ((polynomialLineToSpec baseField).relativeDifferentialsHomEquiv
    _).apply_symm_apply (LocalDerivation.toDerivation' _ (twistDerivation baseField)
      (twistDerivation_appLE baseField))
  exact congrArg (fun d ↦ d.d (X := Opposite.op V) a) this

/-- The local generator `± d(x_{other i} / xᵢ)` of `Ω¹_{ℙ¹/baseField}` over `D₊(xᵢ)`. -/
private def omegaGen (i : Fin 2) :
    Γ((polynomialLineToSpec baseField).relativeDifferentials, monomialChart baseField {i}) :=
  sign i • (dΩ baseField).app _ le_top (coord baseField (i := i) (j := other i))

private lemma omegaGen_compat (i j : Fin 2) (W : (polynomialLine baseField).Opens)
    (hi : W ≤ monomialChart baseField {i}) (hj : W ≤ monomialChart baseField {j}) (a b : Γ(polynomialLine baseField, W))
    (h : a • (twist (homogeneousSubmodule (Fin 2) baseField) (-2)).presheaf.map (homOfLE hi).op
        (twistGen baseField i) =
      b • (twist (homogeneousSubmodule (Fin 2) baseField) (-2)).presheaf.map (homOfLE hj).op
        (twistGen baseField j)) :
    a • (polynomialLineToSpec baseField).relativeDifferentials.presheaf.map
        (homOfLE hi).op (omegaGen baseField i) =
      b • (polynomialLineToSpec baseField).relativeDifferentials.presheaf.map
        (homOfLE hj).op (omegaGen baseField j) := by
  by_cases hij : i = j
  · subst hij
    rw [((isFreeGenerator_twistGen baseField i).map hi).smul_left_injective h]
  have hW := le_overlap baseField hij hi hj
  set c := (polynomialLine baseField).presheaf.map (homOfLE hi).op (coord baseField (i := i) (j := j))
  set c' := (polynomialLine baseField).presheaf.map (homOfLE hj).op
    (coord baseField (i := j) (j := i))
  have hres {l : Fin 2} (hl : W ≤ monomialChart baseField {l})
      (x : Γ(polynomialLine baseField, monomialChart baseField {l})) :
      (polynomialLine baseField).presheaf.map (homOfLE hW).op
        ((polynomialLine baseField).presheaf.map (homOfLE (overlap_le_chart baseField l)).op x) =
      (polynomialLine baseField).presheaf.map (homOfLE hl).op x := by
    rw [Scheme.presheaf_map_map_apply]
    rfl
  have hcc : c * c' = 1 := by
    have := congrArg ((polynomialLine baseField).presheaf.map (homOfLE hW).op)
      (coord_mul_coord baseField (i := i) (j := j))
    rwa [map_mul, map_one, hres hi, hres hj] at this
  have hg : (twist (homogeneousSubmodule (Fin 2) baseField) (-2)).presheaf.map (homOfLE hi).op
      (twistGen baseField i) = c ^ 2 • (twist (homogeneousSubmodule (Fin 2) baseField) (-2)).presheaf.map
        (homOfLE hj).op (twistGen baseField j) := by
    have := congrArg ((twist (homogeneousSubmodule (Fin 2) baseField) (-2)).presheaf.map
      (homOfLE hW).op) (twistGen_restrict baseField (i := i) (j := j))
    rwa [map_smul, map_pow, hres hi, presheaf_map_homOfLE_map_homOfLE,
      presheaf_map_homOfLE_map_homOfLE] at this
  rw [hg, smul_smul] at h
  have hb : b = a * c ^ 2 := (((isFreeGenerator_twistGen baseField j).map hj).smul_left_injective h).symm
  have hd {l : Fin 2} (hl : W ≤ monomialChart baseField {l})
      (x : Γ(polynomialLine baseField, monomialChart baseField {l})) :
      (polynomialLineToSpec baseField).relativeDifferentials.presheaf.map
        (homOfLE hl).op ((dΩ baseField).app _ le_top x) =
      (dΩ baseField).app W le_top ((polynomialLine baseField).presheaf.map (homOfLE hl).op x) :=
    ((dΩ baseField).naturality _ _ le_top hl x).symm
  rw [omegaGen, omegaGen, other_eq hij, other_eq (Ne.symm hij), map_zsmul, map_zsmul, hd hi,
    hd hj, (dΩ baseField).app_eq_neg_sq_smul_of_mul_eq_one le_top hcc, sign_eq_neg hij, hb]
  module

/-- **The morphism `𝒪(-2) ⟶ Ω¹_{ℙ¹/baseField}`** sending the generator `xᵢ⁻²` over `D₊(xᵢ)` to
`± d(x_{other i} / xᵢ)`. -/
private def fromTwist : twist (homogeneousSubmodule (Fin 2) baseField) (-2) ⟶
    (polynomialLineToSpec baseField).relativeDifferentials :=
  glueHom (iSup_chart baseField) (isFreeGenerator_twistGen baseField) (omegaGen_compat baseField)

private lemma fromTwist_twistGen (i : Fin 2) :
    (fromTwist baseField).app (monomialChart baseField {i}) (twistGen baseField i) = omegaGen baseField i :=
  glueHom_app_self _ _ _ i

private lemma sign_mul_self (i : Fin 2) : sign i * sign i = 1 := by
  unfold sign
  split_ifs <;> norm_num

private lemma fromTwist_comp_toTwist : fromTwist baseField ≫ toTwist baseField = 𝟙 _ := by
  refine hom_ext_of_isFreeGenerator (iSup_chart baseField) (isFreeGenerator_twistGen baseField) fun i ↦ ?_
  change (toTwist baseField).app _ ((fromTwist baseField).app _ (twistGen baseField i)) = twistGen baseField i
  rw [fromTwist_twistGen, omegaGen, map_zsmul, toTwist_app_dΩ, twistDerivation_app baseField i _ le_rfl,
    localD, chartLocalDerivation_app_self, chartDerivation_coord, smul_smul, sign_mul_self,
    one_smul]

private lemma dΩ_chartConst (W : (polynomialLine baseField).Opens) (c : baseField) :
    (dΩ baseField).app W le_top (chartConst baseField W c) = 0 := by
  have e : W ≤ (polynomialLineToSpec baseField) ⁻¹ᵁ ⊤ := le_top
  have h := appLE_top_eq_chartConst baseField W e ((Scheme.ΓSpecIso (.of baseField)).inv c)
  have hc : (Scheme.ΓSpecIso (.of baseField)).hom ((Scheme.ΓSpecIso (.of baseField)).inv c) = c := by simp
  rw [hc] at h
  rw [← h, Scheme.Hom.appLE_eq_pullbackPresheafToPresheaf_app, CommRingCat.comp_apply,
    CommRingCat.comp_apply]
  exact (polynomialLineToSpec baseField).relativeDifferentialsDerivation.d_app _

private lemma closure_chart {i j : Fin 2} (hij : i ≠ j) :
    Subring.closure (Set.range (chartConst baseField (monomialChart baseField {i})) ∪ {coord baseField (i := i) (j := j)}) = ⊤ := by
  refine eq_top_iff.2 ?_
  rintro f -
  obtain ⟨p, rfl⟩ := (bijective_polyToChart baseField hij).2 f
  induction p using Polynomial.induction_on with
  | C a => exact Subring.subset_closure (Or.inl ⟨a, by simp [polyToChart]⟩)
  | add p q hp hq => rw [map_add]; exact Subring.add_mem _ hp hq
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul]
    exact Subring.mul_mem _ h (Subring.subset_closure (Or.inr (by simp [polyToChart])))

private lemma fromTwist_twistDerivation (W : (polynomialLine baseField).Opens)
    (a : Γ(polynomialLine baseField, W)) :
    (fromTwist baseField).app W ((twistDerivation baseField).app W le_top a) = (dΩ baseField).app W le_top a := by
  refine LocalDerivation.ext_of_cover (fun i ↦ monomialChart baseField {i}) (iSup_chart baseField)
    ((twistDerivation baseField).postcomp (fromTwist baseField)) (dΩ baseField) (fun i W hW a ↦ ?_) W a
  refine LocalDerivation.ext_of_isAffineOpen (isAffineOpen_monomialChart baseField (Set.singleton_nonempty i))
    (((twistDerivation baseField).postcomp (fromTwist baseField)).restrict le_top) ((dΩ baseField).restrict le_top)
    (fun a ↦ ?_) W hW a
  refine LocalDerivation.app_eq_of_closure _ _ le_rfl _ (closure_chart baseField (ne_other i)) ?_ a
  rintro a (⟨c, rfl⟩ | rfl)
  · simp only [LocalDerivation.restrict_app, LocalDerivation.postcomp_app]
    rw [twistDerivation_app baseField i _ le_rfl, localD, chartLocalDerivation_app_self,
      chartDerivation_chartConst, map_zero, dΩ_chartConst]
  · simp only [LocalDerivation.restrict_app, LocalDerivation.postcomp_app]
    rw [twistDerivation_app baseField i _ le_rfl, localD, chartLocalDerivation_app_self,
      chartDerivation_coord, map_zsmul, fromTwist_twistGen, omegaGen, smul_smul, sign_mul_self,
      one_smul]

private lemma toTwist_comp_fromTwist : toTwist baseField ≫ fromTwist baseField = 𝟙 _ := by
  apply ((polynomialLineToSpec baseField).relativeDifferentialsHomEquiv _).injective
  rw [Scheme.Hom.relativeDifferentialsHomEquiv_apply,
    Scheme.Hom.relativeDifferentialsHomEquiv_apply]
  ext V a
  change (fromTwist baseField).app V.unop ((toTwist baseField).app V.unop ((dΩ baseField).app V.unop le_top a)) =
    (dΩ baseField).app V.unop le_top a
  rw [toTwist_app_dΩ, fromTwist_twistDerivation]

/-- **The canonical sheaf of `ℙ¹_k`**: `Ω¹_{ℙ¹/baseField} ≅ 𝒪(-2)`. -/
noncomputable def relativeDifferentialsIsoTwist :
    (projectiveLineToSpec baseField).relativeDifferentials ≅
      twist (homogeneousSubmodule (Fin 2) baseField) (-2) := by
  change (polynomialLineToSpec baseField).relativeDifferentials ≅
    twist (homogeneousSubmodule (Fin 2) baseField) (-2)
  exact
    { hom := toTwist baseField
      inv := fromTwist baseField
      hom_inv_id := toTwist_comp_fromTwist baseField
      inv_hom_id := fromTwist_comp_toTwist baseField }

end Differentials

section ChartGenerators

private lemma polyEquivChart_X_val (coordinate : Fin 2)
    (point : chart baseField coordinate) :
    ((polyEquivChart baseField coordinate Polynomial.X).1 point).val =
      Localization.mk (X coordinate.rev) ⟨X coordinate, point.2⟩ := by
  letI : Unique {index : Fin 2 // index ≠ coordinate} :=
    { default := ⟨coordinate.rev, by
        change other coordinate ≠ coordinate
        exact (ne_other coordinate).symm⟩
      uniq index := by
        apply Subtype.ext
        exact (other_eq index.property.symm).symm }
  have defaultCoordinate :
      (default : {index : Fin 2 // index ≠ coordinate}).1 = coordinate.rev := rfl
  have polynomialVariable :
      (MvPolynomial.uniqueAlgEquiv baseField {index : Fin 2 // index ≠ coordinate}).symm
          Polynomial.X = X (default : {index : Fin 2 // index ≠ coordinate}) := by
    change Polynomial.eval₂ MvPolynomial.C (X _) Polynomial.X = _
    rw [Polynomial.eval₂_X]
  change ((Proj.awayToSection (homogeneousSubmodule (Fin 2) baseField) (X coordinate)
    ((MvPolynomial.homogeneousLocalizationAwayXEquiv baseField coordinate).symm
      ((MvPolynomial.uniqueAlgEquiv baseField {index : Fin 2 // index ≠ coordinate}).symm
        Polynomial.X))).1 point).val = _
  rw [polynomialVariable, MvPolynomial.homogeneousLocalizationAwayXEquiv_symm_X]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  simp only [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.map_mk', RingHom.id_apply, pow_one, defaultCoordinate]

private lemma coord_restrict_chart (coordinate : Fin 2) :
    (polynomialLine baseField).presheaf.map
        (homOfLE (chart_singleton baseField coordinate).ge).op
        (coord baseField (i := coordinate) (j := other coordinate)) =
      polyEquivChart baseField coordinate Polynomial.X := by
  apply Subtype.ext
  funext point
  apply HomogeneousLocalization.val_injective
  rw [polyEquivChart_X_val]
  change ((Proj.awayToSection (homogeneousSubmodule (Fin 2) baseField)
    (monomialToNat baseField (({coordinate} : Set (Fin 2)).indicator 1))
      (awayMonomial baseField {coordinate}
        (coordExp (i := coordinate) (j := other coordinate)))).1
          ⟨point.1, (chart_singleton baseField coordinate).ge point.2⟩).val = _
  rw [Proj.val_awayToSection_awayMonomial_apply]
  have negativeSum : negExponentSum (coordExp (i := coordinate) (j := other coordinate)).1 = 1 := by
    fin_cases coordinate <;> simp [negExponentSum, coordExp, other, Fin.sum_univ_two]
  have numerator : monomialToNat baseField
      ((coordExp (i := coordinate) (j := other coordinate)).1 +
        ({coordinate} : Set (Fin 2)).indicator 1) = X coordinate.rev := by
    fin_cases coordinate <;> simp [monomialToNat_eq_prod, coordExp, other, Fin.prod_univ_two]
  have denominator : monomialToNat baseField
      (({coordinate} : Set (Fin 2)).indicator 1) = X coordinate := by
    fin_cases coordinate <;> simp [monomialToNat_eq_prod, Fin.prod_univ_two]
  simp only [negativeSum, one_smul]
  apply congrArg₂ Localization.mk
  · exact numerator
  · exact Subtype.ext denominator

private lemma isFreeGenerator_omegaGen (coordinate : Fin 2) :
    IsFreeGenerator (omegaGen baseField coordinate) := by
  let differentialIso : twist (homogeneousSubmodule (Fin 2) baseField) (-2) ≅
      (polynomialLineToSpec baseField).relativeDifferentials :=
    (relativeDifferentialsIsoTwist baseField).symm
  have generator := (isFreeGenerator_twistGen baseField coordinate).app_hom differentialIso
  change IsFreeGenerator ((fromTwist baseField).app _ (twistGen baseField coordinate)) at generator
  rwa [fromTwist_twistGen] at generator

private lemma isFreeGenerator_sectionsD_coord (coordinate : Fin 2) :
    IsFreeGenerator ((polynomialLineToSpec baseField).sectionsD
      (monomialChart baseField {coordinate})
      (coord baseField (i := coordinate) (j := other coordinate))) := by
  have signSquare : (sign coordinate : Γ(polynomialLine baseField,
      monomialChart baseField {coordinate})) * (sign coordinate : _) = 1 := by
    rw [← Int.cast_mul, sign_mul_self, Int.cast_one]
  have generatorEquation : ((⟨_, _, signSquare, signSquare⟩ :
      Γ(polynomialLine baseField, monomialChart baseField {coordinate})ˣ) :
      Γ(polynomialLine baseField, monomialChart baseField {coordinate})) •
        omegaGen baseField coordinate =
      (polynomialLineToSpec baseField).sectionsD (monomialChart baseField {coordinate})
        (coord baseField (i := coordinate) (j := other coordinate)) := by
    rw [omegaGen, Int.cast_smul_eq_zsmul, smul_smul, sign_mul_self, one_smul]
    rfl
  rw [← generatorEquation]
  exact (isFreeGenerator_omegaGen baseField coordinate).units_smul _

/-- The differential of the polynomial coordinate freely generates the relative
cotangent sheaf on a standard affine chart of the projective line. -/
theorem isFreeGenerator_sectionsD_polyEquivChart_X (coordinate : Fin 2) :
    IsFreeGenerator ((projectiveLineToSpec baseField).sectionsD (chart baseField coordinate)
      (polyEquivChart baseField coordinate Polynomial.X)) := by
  change IsFreeGenerator ((polynomialLineToSpec baseField).sectionsD
    (Proj.basicOpen (homogeneousSubmodule (Fin 2) baseField) (X coordinate))
    (polyEquivChart baseField coordinate Polynomial.X))
  have generator := (isFreeGenerator_sectionsD_coord baseField coordinate).map
    (chart_singleton baseField coordinate).ge
  rw [← Scheme.Hom.sectionsD_map, coord_restrict_chart] at generator
  exact generator

/-- The differential of the polynomial coordinate remains a free generator on
any polynomial basic open of a standard projective-line chart. -/
theorem isFreeGenerator_sectionsD_polyToChartBasicOpen_X (coordinate : Fin 2)
    (polynomial : Polynomial baseField) :
    IsFreeGenerator ((projectiveLineToSpec baseField).sectionsD
      (chartBasicOpen baseField coordinate polynomial)
      (polyToChartBasicOpen baseField coordinate polynomial Polynomial.X)) := by
  rw [polyToChartBasicOpen, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, Scheme.Hom.sectionsD_map]
  exact (isFreeGenerator_sectionsD_polyEquivChart_X baseField coordinate).map
    (chartBasicOpen_le baseField coordinate polynomial)

end ChartGenerators

end AlgebraicGeometry.ProjectiveLine
