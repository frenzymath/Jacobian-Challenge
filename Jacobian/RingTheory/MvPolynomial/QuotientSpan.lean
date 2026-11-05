import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Basis loci in finite locally free polynomial quotients

The spanning locus of a polynomial family is the complement of the zero locus
of its cokernel annihilator. For finite locally free quotients, spanning
families of the right size are bases, and monomial basis loci cover the base.
-/

section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open TensorProduct

/-- **A spanning family of the right size is a basis.** If `M` is a finitely presented flat
`A`-module of rank `d` at every prime, then a family of `d` elements spanning `M` is linearly
independent. -/
theorem linearIndependent_of_span_eq_top_of_rankAtStalk {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] [Module.Flat A M] {d : ℕ}
    (v : Fin d → M) (hv : Submodule.span A (Set.range v) = ⊤)
    (hM : ∀ p, Module.rankAtStalk (R := A) M p = d) : LinearIndependent A v := by
  refine (Module.bijective_of_surjective_of_rankAtStalk_eq (M := Fin d →₀ A) (N := M)
    (φ := Finsupp.linearCombination A v) ?_ fun m hm ↦ ?_).1
  · rwa [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  · have := Ideal.Quotient.nontrivial_iff.mpr hm.ne_top
    have := (Ideal.Quotient.mk_surjective (I := m)).nontrivial
    simp [hM]

/-- If the base change of a finite `A`-module `C` to an `A`-algebra `B` vanishes, then the
annihilator of `C` generates the unit ideal of `B`. -/
theorem Module.annihilator_map_eq_top_of_subsingleton_tensorProduct {A B C : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [AddCommGroup C] [Module A C] [Module.Finite A C]
    [Subsingleton (B ⊗[A] C)] :
    (Module.annihilator A C).map (algebraMap A B) = ⊤ := by
  by_contra h
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ h
  let p : PrimeSpectrum A := ⟨q.comap (algebraMap A B), inferInstance⟩
  have hp : p ∈ Module.support A C := by
    rw [Module.mem_support_iff_of_finite]
    exact Ideal.map_le_iff_le_comap.mp hle
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  let := (Ideal.ResidueField.mapₐ p.asIdeal q (Algebra.ofId A B) rfl).toAlgebra
  have : IsScalarTower A p.asIdeal.ResidueField q.ResidueField := IsScalarTower.of_algHom _
  have : Module.FaithfullyFlat p.asIdeal.ResidueField q.ResidueField := inferInstance
  have : Nontrivial (q.ResidueField ⊗[A] C) :=
    (AlgebraTensorModule.cancelBaseChange A p.asIdeal.ResidueField q.ResidueField
      q.ResidueField C).symm.toEquiv.nontrivial
  exact not_subsingleton _ (AlgebraTensorModule.cancelBaseChange A B q.ResidueField
      q.ResidueField C).symm.toEquiv.subsingleton

namespace MvPolynomial

variable {n A B : Type*} [CommRing A] [CommRing B]

/-- The images of the monomials span `A[n] ⧸ I` as an `A`-module. -/
theorem span_range_mk_monomial_eq_top (I : Ideal (MvPolynomial n A)) :
    Submodule.span A (Set.range fun m : n →₀ ℕ ↦ Ideal.Quotient.mk I (monomial m 1)) = ⊤ := by
  have := congrArg (Submodule.map (Ideal.Quotient.mkₐ A I).toLinearMap)
    (basisMonomials n A).span_eq
  rwa [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr
    (Ideal.Quotient.mkₐ_surjective A I), ← Set.range_comp, coe_basisMonomials] at this

/-- Spanning after base change. Let
`I ⊆ A[n]` be an ideal with `A[n] ⧸ I` finite over `A`, let `φ : A →+* B` and let `v` be a family
of polynomials. The images of `v` span `B[n] ⧸ I B[n]` over `B` if and only if the annihilator
of the cokernel of `v` on `A[n] ⧸ I` generates the unit ideal of `B`. -/
theorem span_range_mk_map_eq_top_iff (φ : A →+* B) (I : Ideal (MvPolynomial n A))
    [Module.Finite A (MvPolynomial n A ⧸ I)] {ι : Type*} (v : ι → MvPolynomial n A) :
    Submodule.span B (Set.range fun i ↦ Ideal.Quotient.mk (I.map (map φ)) (map φ (v i))) = ⊤ ↔
      (Module.annihilator A ((MvPolynomial n A ⧸ I) ⧸
        Submodule.span A (Set.range fun i ↦ Ideal.Quotient.mk I (v i)))).map φ = ⊤ := by
  classical
  let _ := φ.toAlgebra
  set N := Submodule.span A (Set.range fun i ↦ Ideal.Quotient.mk I (v i))
  set S := Submodule.span B (Set.range fun i ↦ Ideal.Quotient.mk (I.map (map φ)) (map φ (v i)))
  constructor
  · intro hS
    let Θ₀ : MvPolynomial n B →ₐ[B] B ⊗[A] (MvPolynomial n A ⧸ I) :=
      aeval (R := B) fun i ↦ (1 : B) ⊗ₜ[A] Ideal.Quotient.mk I (X i)
    have hΘ₀ (f : MvPolynomial n A) :
        Θ₀ (map φ f) = (1 : B) ⊗ₜ[A] Ideal.Quotient.mk I f := by
      have : (Θ₀ : MvPolynomial n B →+* _).comp (map φ) =
          (Algebra.TensorProduct.includeRight : (MvPolynomial n A ⧸ I) →ₐ[A]
            B ⊗[A] _).toRingHom.comp (Ideal.Quotient.mk I) := by
        refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
        · simp only [Θ₀, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_C,
            algHom_C, AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.includeRight_apply]
          rw [← RingHom.algebraMap_toAlgebra φ, ← IsScalarTower.algebraMap_apply A B,
            Algebra.TensorProduct.algebraMap_apply']
          rfl
        · simp [Θ₀]
      exact congr($this f)
    let Θ := Ideal.Quotient.liftₐ (I.map (map φ)) Θ₀ fun x hx ↦
      (Ideal.map_le_iff_le_comap.mpr (fun f hf ↦ by
        rw [Ideal.mem_comap, RingHom.mem_ker, hΘ₀, Ideal.Quotient.eq_zero_iff_mem.mpr hf,
          tmul_zero]) : I.map (map φ) ≤ RingHom.ker Θ₀) hx
    have hΘ : Function.Surjective Θ := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul b q =>
        obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
        refine ⟨b • Ideal.Quotient.mk _ (map φ f), ?_⟩
        rw [map_smul]
        simp [Θ, hΘ₀, smul_tmul']
      | add y z hy hz =>
        obtain ⟨y, rfl⟩ := hy
        obtain ⟨z, rfl⟩ := hz
        exact ⟨y + z, map_add _ _ _⟩
    have hT := congrArg (Submodule.map Θ.toLinearMap) hS
    rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr hΘ,
      ← Set.range_comp] at hT
    let π := LinearMap.baseChange B N.mkQ
    have hπ : Function.Surjective π := LinearMap.lTensor_surjective _ N.mkQ_surjective
    have hker : (⊤ : Submodule B (B ⊗[A] (MvPolynomial n A ⧸ I))) ≤ LinearMap.ker π := by
      rw [← hT, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply, SetLike.mem_coe,
        LinearMap.mem_ker, π, Θ, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
      rw [AlgHom.coe_toRingHom, hΘ₀, LinearMap.baseChange_tmul, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨i, rfl⟩), tmul_zero]
    have : Subsingleton (B ⊗[A] ((MvPolynomial n A ⧸ I) ⧸ N)) := by
      refine subsingleton_of_forall_eq 0 fun y ↦ ?_
      obtain ⟨y, rfl⟩ := hπ y
      exact hker trivial
    exact Module.annihilator_map_eq_top_of_subsingleton_tensorProduct (B := B)
  · intro hJ
    let ψ := Ideal.quotientMap (I.map (map φ)) (map φ) Ideal.le_comap_map
    have hψmk (f : MvPolynomial n A) :
        ψ (Ideal.Quotient.mk I f) = Ideal.Quotient.mk _ (map φ f) :=
      Ideal.quotientMap_mk
    have hψ (a : A) (x : MvPolynomial n A ⧸ I) : ψ (a • x) = φ a • ψ x := by
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      calc
        ψ (a • Ideal.Quotient.mk I f) = ψ (Ideal.Quotient.mk I (C a * f)) := by
          apply congrArg ψ
          rw [C_mul', ← Ideal.Quotient.mkₐ_eq_mk A]
          exact (map_smul (Ideal.Quotient.mkₐ A I) a f).symm
        _ = Ideal.Quotient.mk (I.map (map φ)) (C (φ a) * map φ f) := by
          rw [hψmk, map_mul, map_C]
        _ = φ a • Ideal.Quotient.mk (I.map (map φ)) (map φ f) := by
          rw [C_mul', ← Ideal.Quotient.mkₐ_eq_mk B]
          exact map_smul (Ideal.Quotient.mkₐ B (I.map (map φ))) (φ a) (map φ f)
        _ = φ a • ψ (Ideal.Quotient.mk I f) := by rw [hψmk]
    have hN (x : MvPolynomial n A ⧸ I) (hx : x ∈ N) : ψ x ∈ S := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact Submodule.subset_span ⟨i, by simp [ψ]⟩
      | zero => simp
      | add x y _ _ hx hy => simpa using add_mem hx hy
      | smul a x _ hx => simpa [hψ] using S.smul_mem (φ a) hx
    have key (f : MvPolynomial n A) : Ideal.Quotient.mk _ (map φ f) ∈ S := by
      have h1 : (1 : B) ∈ (Module.annihilator A ((MvPolynomial n A ⧸ I) ⧸ N)).map φ :=
        hJ ▸ Submodule.mem_top
      suffices ∀ b ∈ (Module.annihilator A ((MvPolynomial n A ⧸ I) ⧸ N)).map φ,
          ∀ f, b • Ideal.Quotient.mk (I.map (map φ)) (map φ f) ∈ S by
        simpa using this 1 h1 f
      intro b hb
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨a, ha, rfl⟩ := hb
        intro f
        rw [← hψmk, ← hψ]
        refine hN _ ?_
        have := Module.mem_annihilator.mp ha (Submodule.Quotient.mk (Ideal.Quotient.mk I f))
        rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
      | zero => simp
      | add x y _ _ hx hy => simpa [add_smul] using fun f ↦ add_mem (hx f) (hy f)
      | smul c x _ hx => simpa [mul_smul] using fun f ↦ S.smul_mem c (hx f)
    rw [eq_top_iff]
    rintro y -
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction g using MvPolynomial.induction_on' with
    | monomial m b =>
      have h := S.smul_mem b (key (monomial m 1))
      rw [map_monomial, map_one] at h
      have hsmul : b • Ideal.Quotient.mk (I.map (map φ)) (monomial m 1) =
          Ideal.Quotient.mk (I.map (map φ)) (monomial m b) := by
        calc
          b • Ideal.Quotient.mk (I.map (map φ)) (monomial m 1) =
              Ideal.Quotient.mk (I.map (map φ)) (C b * monomial m 1) := by
            rw [C_mul', ← Ideal.Quotient.mkₐ_eq_mk B]
            exact (map_smul (Ideal.Quotient.mkₐ B (I.map (map φ))) b
              (monomial m 1)).symm
          _ = Ideal.Quotient.mk (I.map (map φ)) (monomial m b) := by
            rw [C_mul_monomial, mul_one]
      rwa [hsmul] at h
    | add g h hg hh => simpa using add_mem hg hh

attribute [local instance] Module.free_of_flat_of_isLocalRing in
/-- Monomial bases exist locally.
If `A[n] ⧸ I` is a finitely presented flat `A`-module of rank `d` at the prime `p`, then there
are `d` monomials whose images span `A[n] ⧸ I` near `p`: the annihilator of the cokernel of
their images is not contained in `p`. -/
theorem exists_monomials_annihilator_not_le (I : Ideal (MvPolynomial n A))
    [Module.FinitePresentation A (MvPolynomial n A ⧸ I)] [Module.Flat A (MvPolynomial n A ⧸ I)]
    (p : PrimeSpectrum A) {d : ℕ} (hp : Module.rankAtStalk (MvPolynomial n A ⧸ I) p = d) :
    ∃ v : Fin d → (n →₀ ℕ), ¬ Module.annihilator A ((MvPolynomial n A ⧸ I) ⧸
      Submodule.span A (Set.range fun l ↦ Ideal.Quotient.mk I (monomial (v l) 1))) ≤
        p.asIdeal := by
  classical
  let f := LocalizedModule.mkLinearMap p.asIdeal.primeCompl (MvPolynomial n A ⧸ I)
  have hspan : Submodule.span (Localization.AtPrime p.asIdeal)
      (Set.range fun m : n →₀ ℕ ↦ f (Ideal.Quotient.mk I (monomial m 1))) = ⊤ := by
    rw [Set.range_comp' f, ← Submodule.localized'_span (S := Localization.AtPrime p.asIdeal)
      (p := p.asIdeal.primeCompl) (f := f), span_range_mk_monomial_eq_top,
      Submodule.localized'_top]
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _ hspan
  have : Fintype κ :=
    have := Module.Finite.finite_basis b
    Fintype.ofFinite κ
  have hκ : Fintype.card κ = d := by rw [← hp, Module.rankAtStalk, Module.finrank_eq_card_basis b]
  let e : Fin d ≃ κ := (Fintype.equivFinOfCardEq hκ).symm
  refine ⟨a ∘ e, fun hle ↦ ?_⟩
  rw [← Module.mem_support_iff_of_finite (p := p)] at hle
  refine ((Module.notMem_support_iff' (p := p)).mpr fun c ↦ ?_) hle
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  have hx : f x ∈ (Submodule.span A (Set.range fun l ↦ Ideal.Quotient.mk I
      (monomial ((a ∘ e) l) 1))).localized' (Localization.AtPrime p.asIdeal)
        p.asIdeal.primeCompl f := by
    have hr : f '' Set.range (fun l ↦ Ideal.Quotient.mk I (monomial ((a ∘ e) l) 1)) =
        Set.range b := by
      rw [← Set.range_comp', ← e.surjective.range_comp b]
      simp [Function.comp_def, hb]
    rw [Submodule.localized'_span, hr, b.span_eq]
    trivial
  obtain ⟨m, hm, s, hms⟩ := (Submodule.mem_localized' _ _ _ _ _).mp hx
  rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hms
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := p.asIdeal.primeCompl) hms
  refine ⟨c * s, (c * s).2, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mul_smul,
    ← Submonoid.smul_def, ← hc]
  exact Submodule.smul_of_tower_mem _ c hm

end MvPolynomial
