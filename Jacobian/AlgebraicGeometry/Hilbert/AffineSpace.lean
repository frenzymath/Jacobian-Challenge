import Jacobian.AlgebraicGeometry.Hilbert.Affine
import Jacobian.AlgebraicGeometry.Hilbert.BasisLocus
import Jacobian.AlgebraicGeometry.AffineSpace.GlobalSections

/-!
# Affine basis charts of the Hilbert functor

Finite flat subschemes of affine space over affine test schemes are described
by polynomial quotient algebras. The universal quotient-basis rings give actual
Hilbert families. Their images are open basis loci and cover every affine test
scheme locally.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Hilbert

section Algebra

variable {A B B' : Type*} [CommRing A] [CommRing B] [CommRing B']

/-- A ring map is finite, flat, of finite presentation and of rank `d` at every prime. -/
def IsFiniteFlatQuotient (d : ℕ) (f : A →+* B) : Prop :=
  f.Finite ∧ f.Flat ∧ f.FinitePresentation ∧ ∀ p, f.finrank p = d

/-- `IsFiniteFlatQuotient` is preserved by composing with a ring isomorphism. -/
lemma IsFiniteFlatQuotient.ringEquiv_comp {d : ℕ} {f : A →+* B} (h : IsFiniteFlatQuotient d f) (e : B ≃+* B') :
    IsFiniteFlatQuotient d (e.toRingHom.comp f) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨(RingHom.Finite.of_surjective _ e.surjective).comp h₁,
    h₂.comp (RingHom.Flat.of_bijective e.bijective),
    (RingHom.FinitePresentation.of_surjective _ e.surjective ?_).comp h₃, fun p ↦ ?_⟩
  · rw [(RingHom.injective_iff_ker_eq_bot e.toRingHom).1 e.injective]
    exact Submodule.fg_bot
  · rw [RingHom.finrank_comp_left_of_bijective _ _ e.bijective h₁ h₂, h₄]

/-- `IsFiniteFlatQuotient` is invariant under composing with a ring isomorphism. -/
lemma isFiniteFlatQuotient_ringEquiv_comp_iff {d : ℕ} (f : A →+* B) (e : B ≃+* B') :
    IsFiniteFlatQuotient d (e.toRingHom.comp f) ↔ IsFiniteFlatQuotient d f := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.ringEquiv_comp e⟩
  convert h.ringEquiv_comp e.symm
  ext
  simp

/-- `IsFiniteFlatQuotient` of an algebra map, in terms of the module and algebra structure. -/
lemma isFiniteFlatQuotient_algebraMap_iff {d : ℕ} [Algebra A B] :
    IsFiniteFlatQuotient d (algebraMap A B) ↔ Module.Finite A B ∧ Module.Flat A B ∧
      Algebra.FinitePresentation A B ∧ ∀ p, Module.rankAtStalk (R := A) B p = d := by
  rw [IsFiniteFlatQuotient, RingHom.finite_algebraMap, RingHom.flat_algebraMap_iff,
    RingHom.finitePresentation_algebraMap, RingHom.finrank_algebraMap]

/-- A quotient of `A[n]` with a basis of `d` elements is finite, flat, finitely presented of
rank `d`. -/
lemma isFiniteFlatQuotient_of_isQuotientBasis {R : Type u} [CommRing R] {n : Type u} {d : ℕ}
    {w : Fin d → MvPolynomial n R} [Algebra R A] {I : Ideal (MvPolynomial n A)}
    (hI : MvPolynomial.IsQuotientBasis w I) :
    IsFiniteFlatQuotient d (algebraMap A (MvPolynomial n A ⧸ I)) := by
  let b := Module.Basis.mk hI.1 hI.2.ge
  have : Module.Free A (MvPolynomial n A ⧸ I) := .of_basis b
  have : Module.Finite A (MvPolynomial n A ⧸ I) := .of_basis b
  have : Module.FinitePresentation A (MvPolynomial n A ⧸ I) :=
    Module.finitePresentation_of_projective _ _
  rw [isFiniteFlatQuotient_algebraMap_iff]
  refine ⟨inferInstance, inferInstance, .of_finitePresentation _ _, fun p ↦ ?_⟩
  have : Nontrivial A := p.nontrivial
  rw [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Module.finrank_eq_card_basis b,
    Fintype.card_fin, Nat.cast_id]

/-- Transport of the Hilbert condition along `A[n] ≃ B`. -/
lemma isFiniteFlatQuotient_quotient_iff {n : Type*} {d : ℕ} (E : MvPolynomial n A ≃+* B)
    (σ : A →+* B) (hσ : E.toRingHom.comp MvPolynomial.C = σ) (K : Ideal B) :
    IsFiniteFlatQuotient d ((Ideal.Quotient.mk K).comp σ) ↔
      IsFiniteFlatQuotient d (algebraMap A (MvPolynomial n A ⧸ K.comap E)) := by
  let e := Ideal.quotientEquiv (K.comap E) K E (Ideal.map_comap_of_surjective _ E.surjective K).symm
  rw [← isFiniteFlatQuotient_ringEquiv_comp_iff _ e]
  congr! 1
  ext a
  simp [e, ← hσ]

end Algebra

section Dictionary

variable {n : Type u} {S : Scheme.{u}} {d : ℕ}

/-- The ideal of `Γ(T)[n]` of a point of the Hilbert functor of `𝔸(n; S)` over an affine `T`. -/
noncomputable def polynomialIdeal {T : Over S} [IsAffine T.left]
    (x : (hilbertPresheaf (𝔸(n; S) ↘ S) d).obj (op T)) : Ideal (MvPolynomial n Γ(T.left, ⊤)) :=
  (x.1.ideal ⟨⊤, isAffineOpen_top _⟩).comap (AffineSpace.toΓPullback n T.hom)

/-- `toΓPullback` as a ring isomorphism. -/
noncomputable def pullbackPolynomialEquiv (T : Over S) [IsAffine T.left] :
    MvPolynomial n Γ(T.left, ⊤) ≃+* Γ(pullback (𝔸(n; S) ↘ S) T.hom, ⊤) :=
  RingEquiv.ofBijective _ (AffineSpace.toΓPullback_bijective (n := n) T.hom)

/-- `toΓPullback` restricted to the constants is the pullback of `𝔸(n; S) ×[S] T ⟶ T`. -/
lemma pullbackPolynomialEquiv_comp_C (T : Over S) [IsAffine T.left] :
    (pullbackPolynomialEquiv (n := n) T).toRingHom.comp MvPolynomial.C =
      (pullback.snd (𝔸(n; S) ↘ S) T.hom).appTop.hom := by
  ext a
  simp [pullbackPolynomialEquiv, AffineSpace.toΓPullback]

/-- Over an affine base, a point of the Hilbert functor is determined by its ideal. -/
lemma polynomialIdeal_injective {T : Over S} [IsAffine T.left] :
    Function.Injective (polynomialIdeal (n := n) (d := d) (T := T)) := by
  intro x y h
  refine Subtype.ext (Scheme.IdealSheafData.ext_of_isAffine ?_)
  exact Ideal.comap_injective_of_surjective _
    (AffineSpace.toΓPullback_bijective (n := n) T.hom).2 h

/-- The quotient by the ideal of a point is finite flat finitely presented of rank `d`. -/
lemma isFiniteFlatQuotient_polynomialIdeal {T : Over S} [IsAffine T.left]
    (x : (hilbertPresheaf (𝔸(n; S) ↘ S) d).obj (op T)) :
    IsFiniteFlatQuotient d (algebraMap Γ(T.left, ⊤) (MvPolynomial n Γ(T.left, ⊤) ⧸ polynomialIdeal x)) := by
  have h := (isHilbertSubscheme_iff_of_isAffine _ d T x.1).1 x.2
  exact (isFiniteFlatQuotient_quotient_iff (pullbackPolynomialEquiv T) _ (pullbackPolynomialEquiv_comp_C T) _).1 h

/-- The point of the Hilbert functor with a given ideal of `Γ(T)[n]`. -/
noncomputable def ofPolynomialIdeal {T : Over S} [IsAffine T.left]
    (K : Ideal (MvPolynomial n Γ(T.left, ⊤)))
    (hK : IsFiniteFlatQuotient d (algebraMap Γ(T.left, ⊤) (MvPolynomial n Γ(T.left, ⊤) ⧸ K))) :
    (hilbertPresheaf (𝔸(n; S) ↘ S) d).obj (op T) :=
  ⟨.ofIdealTop (K.map (pullbackPolynomialEquiv T)), by
    rw [isHilbertSubscheme_iff_of_isAffine, Scheme.IdealSheafData.ideal_top_ofIdealTop]
    refine (isFiniteFlatQuotient_quotient_iff (pullbackPolynomialEquiv T) _ (pullbackPolynomialEquiv_comp_C T) _).2 ?_
    rwa [Ideal.comap_map_of_bijective _ (pullbackPolynomialEquiv T).bijective]⟩

/-- The ideal of `ofPolynomialIdeal K` is `K`. -/
lemma polynomialIdeal_ofPolynomialIdeal {T : Over S} [IsAffine T.left]
    (K : Ideal (MvPolynomial n Γ(T.left, ⊤)))
    (hK : IsFiniteFlatQuotient d (algebraMap Γ(T.left, ⊤) (MvPolynomial n Γ(T.left, ⊤) ⧸ K))) :
    polynomialIdeal (ofPolynomialIdeal K hK) = K := by
  rw [polynomialIdeal, ofPolynomialIdeal, Scheme.IdealSheafData.ideal_top_ofIdealTop]
  exact Ideal.comap_map_of_bijective _ (pullbackPolynomialEquiv T).bijective

/-- Naturality of `polynomialIdeal`: pulling back a point extends its ideal. -/
lemma polynomialIdeal_map {T W : Over S} [IsAffine T.left] [IsAffine W.left] (a : W ⟶ T)
    (x : (hilbertPresheaf (𝔸(n; S) ↘ S) d).obj (op T)) :
    polynomialIdeal ((hilbertPresheaf (𝔸(n; S) ↘ S) d).map a.op x) =
      (polynomialIdeal x).map (MvPolynomial.map a.left.appTop.hom) := by
  have hT : x.1.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (polynomialIdeal x).map (AffineSpace.toΓPullback n T.hom) :=
    (Ideal.map_comap_of_surjective _ (AffineSpace.toΓPullback_bijective n T.hom).2 _).symm
  generalize polynomialIdeal x = K at hT
  rw [polynomialIdeal]
  refine Eq.trans ?_
    (Ideal.comap_map_of_bijective _ (AffineSpace.toΓPullback_bijective n W.hom))
  congr 1
  refine (Scheme.IdealSheafData.ideal_top_comap_of_isAffine _ _).trans ?_
  rw [hT, Ideal.map_map, Ideal.map_map]
  congr 1
  refine RingHom.ext fun p ↦ ?_
  exact AffineSpace.appTop_pullbackMap_toΓPullback (n := n) T.hom W.hom a.left (Over.w a) p

end Dictionary


section Universal



variable {n : Type u} {S : Scheme.{u}} [IsAffine S] {d : ℕ}



/-- Extensions of the universal ideal along algebra maps are `w`-adapted. -/
lemma isQuotientBasis_map_quotientBasisIdeal {R : Type u} [CommRing R]
    {w : Fin d → MvPolynomial n R} {A : Type*} [CommRing A] [Algebra R A]
    (φ : MvPolynomial.QuotientBasisRing w →+* A)
    (hφ : φ.comp (algebraMap R (MvPolynomial.QuotientBasisRing w)) = algebraMap R A) :
    MvPolynomial.IsQuotientBasis w
      ((MvPolynomial.quotientBasisIdeal w).map (MvPolynomial.map φ)) :=
  (MvPolynomial.quotientBasisEquiv w A ⟨φ, fun r ↦ RingHom.congr_fun hφ r⟩).2

/-- An algebra map is determined by the extension of the universal ideal along it. -/
lemma eq_of_map_quotientBasisIdeal_eq {R : Type u} [CommRing R]
    {w : Fin d → MvPolynomial n R} {A : Type*} [CommRing A] [Algebra R A]
    {φ ψ : MvPolynomial.QuotientBasisRing w →+* A}
    (hφ : φ.comp (algebraMap R (MvPolynomial.QuotientBasisRing w)) = algebraMap R A)
    (hψ : ψ.comp (algebraMap R (MvPolynomial.QuotientBasisRing w)) = algebraMap R A)
    (h : (MvPolynomial.quotientBasisIdeal w).map (MvPolynomial.map φ) =
      (MvPolynomial.quotientBasisIdeal w).map (MvPolynomial.map ψ)) : φ = ψ := by
  have := (MvPolynomial.quotientBasisEquiv w A).injective
    (a₁ := ⟨φ, fun r ↦ RingHom.congr_fun hφ r⟩) (a₂ := ⟨ψ, fun r ↦ RingHom.congr_fun hψ r⟩)
    (Subtype.ext h)
  exact congrArg AlgHom.toRingHom this

/-- Every `w`-adapted ideal is an extension of the universal ideal. -/
lemma exists_map_quotientBasisIdeal_eq {R : Type u} [CommRing R]
    {w : Fin d → MvPolynomial n R} {A : Type*} [CommRing A] [Algebra R A]
    {I : Ideal (MvPolynomial n A)} (hI : MvPolynomial.IsQuotientBasis w I) :
    ∃ φ : MvPolynomial.QuotientBasisRing w →+* A,
      φ.comp (algebraMap R (MvPolynomial.QuotientBasisRing w)) = algebraMap R A ∧
        I = (MvPolynomial.quotientBasisIdeal w).map (MvPolynomial.map φ) := by
  obtain ⟨φ, hφ⟩ := (MvPolynomial.quotientBasisEquiv w A).surjective ⟨I, hI⟩
  exact ⟨φ.toRingHom, RingHom.ext φ.commutes, (congrArg Subtype.val hφ).symm⟩

/-- The universal point of the Hilbert functor over `basisChart w`. -/
noncomputable def basisChartPoint (w : Fin d → MvPolynomial n Γ(S, ⊤)) :
    (hilbertPresheaf (𝔸(n; S) ↘ S) d).obj (op (basisChart w)) :=
  ofPolynomialIdeal ((MvPolynomial.quotientBasisIdeal w).map (MvPolynomial.map (basisChartRingHom (𝟙 _)))) <|
    letI := (basisChart w).hom.appTop.hom.toAlgebra
    isFiniteFlatQuotient_of_isQuotientBasis (isQuotientBasis_map_quotientBasisIdeal _
      (basisChartRingHom_comp_algebraMap _))

/-- The ideal of the pullback of the universal point along `b`. -/
lemma polynomialIdeal_map_basisChartPoint {w : Fin d → MvPolynomial n Γ(S, ⊤)} {W : Over S}
    [IsAffine W.left] (b : W ⟶ basisChart w) :
    polynomialIdeal ((hilbertPresheaf (𝔸(n; S) ↘ S) d).map b.op (basisChartPoint w)) =
      (MvPolynomial.quotientBasisIdeal w).map (MvPolynomial.map (basisChartRingHom b)) := by
  rw [polynomialIdeal_map, basisChartPoint, polynomialIdeal_ofPolynomialIdeal, Ideal.map_map]
  congr 1
  refine RingHom.ext fun p ↦ ?_
  rw [RingHom.comp_apply, MvPolynomial.map_map, ← basisChartRingHom_comp, Category.comp_id]

/-- The annihilator of the cokernel of the images of the `w l` in the quotient of `Γ(T)[n]`
of a point `x`: the locus of `T` where these images span, hence form a basis. -/
noncomputable def basisAnnihilator {T : Over S} [IsAffine T.left]
    (x : (hilbertPresheaf (𝔸(n; S) ↘ S) d).obj (op T)) (w : Fin d → MvPolynomial n Γ(S, ⊤)) :
    Ideal Γ(T.left, ⊤) :=
  Module.annihilator Γ(T.left, ⊤) ((MvPolynomial n Γ(T.left, ⊤) ⧸ polynomialIdeal x) ⧸
    Submodule.span Γ(T.left, ⊤) (Set.range fun l ↦
      Ideal.Quotient.mk (polynomialIdeal x) (MvPolynomial.map T.hom.appTop.hom (w l))))

/-- A pullback of `x` comes from the universal point if and only if `basisAnnihilator x w` generates
the unit ideal. -/
lemma exists_eq_basisChartPoint_iff {T W : Over S} [IsAffine T.left] [IsAffine W.left]
    (x : (hilbertPresheaf (𝔸(n; S) ↘ S) d).obj (op T)) (w : Fin d → MvPolynomial n Γ(S, ⊤))
    (a : W ⟶ T) :
    (∃ b : W ⟶ basisChart w, (hilbertPresheaf (𝔸(n; S) ↘ S) d).map a.op x =
      (hilbertPresheaf (𝔸(n; S) ↘ S) d).map b.op (basisChartPoint w)) ↔
      (basisAnnihilator x w).map a.left.appTop.hom = ⊤ := by
  let := W.hom.appTop.hom.toAlgebra
  obtain ⟨hfin, -, -, -⟩ := (isFiniteFlatQuotient_algebraMap_iff (d := d)).1 (isFiniteFlatQuotient_polynomialIdeal x)
  have hW := isFiniteFlatQuotient_polynomialIdeal ((hilbertPresheaf (𝔸(n; S) ↘ S) d).map a.op x)
  rw [polynomialIdeal_map] at hW
  obtain ⟨hfinW, hflat, hfp, hrank⟩ := (isFiniteFlatQuotient_algebraMap_iff (d := d)).1 hW
  have hfp' : Module.FinitePresentation Γ(W.left, ⊤)
      (MvPolynomial n Γ(W.left, ⊤) ⧸ (polynomialIdeal x).map (MvPolynomial.map a.left.appTop.hom)) :=
    .of_finite_of_finitePresentation _ _
  have hw (l : Fin d) : MvPolynomial.map (algebraMap Γ(S, ⊤) Γ(W.left, ⊤)) (w l) =
      MvPolynomial.map a.left.appTop.hom (MvPolynomial.map T.hom.appTop.hom (w l)) := by
    rw [MvPolynomial.map_map, RingHom.algebraMap_toAlgebra, ← Over.w a, Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp]
  rw [basisAnnihilator, ← MvPolynomial.span_range_mk_map_eq_top_iff]
  simp_rw [← hw]
  trans MvPolynomial.IsQuotientBasis w ((polynomialIdeal x).map (MvPolynomial.map a.left.appTop.hom))
  · rw [← polynomialIdeal_map]
    constructor
    · rintro ⟨b, hb⟩
      rw [hb, polynomialIdeal_map_basisChartPoint]
      exact isQuotientBasis_map_quotientBasisIdeal _ (basisChartRingHom_comp_algebraMap b)
    · intro h
      obtain ⟨φ, hφ, hI⟩ := exists_map_quotientBasisIdeal_eq h
      obtain ⟨b, rfl⟩ := exists_basisChartRingHom_eq φ hφ
      exact ⟨b, polynomialIdeal_injective (hI.trans (polynomialIdeal_map_basisChartPoint b).symm)⟩
  · exact ⟨fun h ↦ h.2, fun h ↦ ⟨linearIndependent_of_span_eq_top_of_rankAtStalk _ h hrank, h⟩⟩

end Universal

/-- An affine test morphism factors through the complement of a zero locus exactly

when the defining ideal becomes the unit ideal. -/
lemma range_subset_compl_zeroLocus_iff {T W : Scheme.{u}} [IsAffine W] (a : W ⟶ T)
    (J : Ideal Γ(T, ⊤)) :
    Set.range a ⊆ (T.zeroLocus (U := ⊤) (J : Set Γ(T, ⊤)))ᶜ ↔ J.map a.appTop.hom = ⊤ := by
  rw [Set.range_subset_iff, ← PrimeSpectrum.zeroLocus_empty_iff_eq_top, Ideal.map,
    PrimeSpectrum.zeroLocus_span, ← W.toSpecΓ_image_zeroLocus, Set.image_eq_empty,
    Set.eq_empty_iff_forall_notMem]
  refine forall_congr' fun y ↦ ?_
  simp only [Set.mem_compl_iff, Scheme.mem_zeroLocus_iff, Set.forall_mem_image,
    ← Scheme.preimage_basicOpen_top]
  rfl


/-- The universal Hilbert family defines the morphism from a basis chart to the Hilbert functor. -/
noncomputable def basisChartι {indeterminates : Type u} {base : Scheme.{u}} [IsAffine base]
    {rank : ℕ} (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)) :
    yoneda.obj (basisChart family) ⟶ hilbertPresheaf (𝔸(indeterminates; base) ↘ base) rank :=
  yonedaEquiv.symm (basisChartPoint family)

/-- A basis-chart morphism over an affine test scheme is determined by its Hilbert family. -/
lemma basisChartPoint_injective {indeterminates : Type u} {base : Scheme.{u}} [IsAffine base]
    {rank : ℕ} (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
    (test : Over base) [IsAffine test.left] :
    Function.Injective (fun chartMap : test ⟶ basisChart family ↦
      (hilbertPresheaf (𝔸(indeterminates; base) ↘ base) rank).map chartMap.op (basisChartPoint family)) := by
  intro firstMap secondMap equality
  letI := test.hom.appTop.hom.toAlgebra
  have idealEquality := congrArg polynomialIdeal equality
  rw [polynomialIdeal_map_basisChartPoint, polynomialIdeal_map_basisChartPoint] at idealEquality
  exact basisChartRingHom_injective (eq_of_map_quotientBasisIdeal_eq
    (basisChartRingHom_comp_algebraMap firstMap)
    (basisChartRingHom_comp_algebraMap secondMap) idealEquality)

/-- The inverse image of a basis chart is the complement of the zero locus of the basis annihilator. -/
lemma exists_opens_basisChartPoint {indeterminates : Type u} {base : Scheme.{u}} [IsAffine base]
    {rank : ℕ} (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
    (test : Over base) [IsAffine test.left]
    (point : (hilbertPresheaf (𝔸(indeterminates; base) ↘ base) rank).obj (op test)) :
    ∃ openSubset : test.left.Opens, ∀ (smallerTest : Over base) [IsAffine smallerTest.left]
      (restriction : smallerTest ⟶ test),
      (∃ chartMap : smallerTest ⟶ basisChart family,
        (hilbertPresheaf (𝔸(indeterminates; base) ↘ base) rank).map restriction.op point =
          (hilbertPresheaf (𝔸(indeterminates; base) ↘ base) rank).map chartMap.op
            (basisChartPoint family)) ↔ Set.range restriction.left ⊆ openSubset := by
  refine ⟨⟨(test.left.zeroLocus (U := ⊤)
    (basisAnnihilator point family : Set Γ(test.left, ⊤)))ᶜ,
      (Scheme.zeroLocus_isClosed _ _).isOpen_compl⟩, fun smallerTest _ restriction ↦ ?_⟩
  rw [exists_eq_basisChartPoint_iff, ← range_subset_compl_zeroLocus_iff]
  rfl

/-- Every Hilbert point over an affine scheme is locally induced by a basis chart. -/
lemma exists_basisChartPoint {indeterminates : Type u} {base : Scheme.{u}} [IsAffine base]
    {rank : ℕ} (test : Over base) [IsAffine test.left]
    (point : (hilbertPresheaf (𝔸(indeterminates; base) ↘ base) rank).obj (op test))
    (testPoint : test.left) :
    ∃ (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
      (smallerTest : Over base) (restriction : smallerTest ⟶ test)
      (chartMap : smallerTest ⟶ basisChart family),
      testPoint ∈ Set.range restriction.left ∧
        (hilbertPresheaf (𝔸(indeterminates; base) ↘ base) rank).map restriction.op point =
          (hilbertPresheaf (𝔸(indeterminates; base) ↘ base) rank).map chartMap.op
            (basisChartPoint family) := by
  obtain ⟨finite, flat, finitePresentation, constantRank⟩ :=
    (isFiniteFlatQuotient_algebraMap_iff (d := rank)).mp (isFiniteFlatQuotient_polynomialIdeal point)
  have : Module.FinitePresentation Γ(test.left, ⊤)
      (MvPolynomial indeterminates Γ(test.left, ⊤) ⧸ polynomialIdeal point) :=
    .of_finite_of_finitePresentation _ _
  obtain ⟨monomials, annihilatorNotContained⟩ :=
    MvPolynomial.exists_monomials_annihilator_not_le (polynomialIdeal point)
      (test.left.toSpecΓ testPoint) (constantRank _)
  obtain ⟨denominator, inAnnihilator, notInPrime⟩ := Set.not_subset.mp annihilatorNotContained
  let family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤) :=
    fun index ↦ MvPolynomial.monomial (monomials index) 1
  have familyEquality : (fun index ↦ Ideal.Quotient.mk (polynomialIdeal point)
      (MvPolynomial.map test.hom.appTop.hom (family index))) =
      fun index ↦ Ideal.Quotient.mk (polynomialIdeal point)
        (MvPolynomial.monomial (monomials index) 1) := by
    simp [family, MvPolynomial.map_monomial]
  have denominatorInAnnihilator : denominator ∈ basisAnnihilator point family := by
    rwa [basisAnnihilator, familyEquality]
  let smallerTest : Over base := Over.mk ((test.left.basicOpen denominator).ι ≫ test.hom)
  have : IsAffine smallerTest.left := (isAffineOpen_top test.left).basicOpen denominator
  let restriction : smallerTest ⟶ test := Over.homMk (test.left.basicOpen denominator).ι
  have restrictionRange : Set.range restriction.left = test.left.basicOpen denominator :=
    Scheme.Opens.range_ι _
  obtain ⟨chartMap, familyEquality⟩ :=
    (exists_eq_basisChartPoint_iff (W := smallerTest) point family restriction).mpr (by
      rw [← range_subset_compl_zeroLocus_iff, restrictionRange]
      exact fun element membership vanishing ↦
        (Scheme.mem_zeroLocus_iff _ _ _).mp vanishing denominator denominatorInAnnihilator membership)
  refine ⟨family, smallerTest, restriction, chartMap, ?_, familyEquality⟩
  rw [restrictionRange, ← Scheme.toSpecΓ_preimage_basicOpen]
  exact notInPrime

end AlgebraicGeometry.Hilbert
