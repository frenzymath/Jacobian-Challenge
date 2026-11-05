import Jacobian.RingTheory.LocalRing.ResidueField.RegularFiber

/-!
# Flat quotients by fibrewise regular equations

A principal ideal in a flat finitely presented algebra which is generated
locally on a fibre by nonzerodivisors is regular near that fibre. Its quotient
is flat over the base on the same neighborhood.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct
open scoped nonZeroDivisors

namespace Algebra

/-- Injectivity of multiplication on all ideal quotients gives a regular
equation and a flat quotient after localization. -/
theorem isRegularPrincipal_and_flat_of_forall_mul_mem_map {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Module.Flat A B] (f g : B)
    (hP : ∀ (J : Ideal A) (x : B), f * x ∈ J.map (algebraMap A B) →
      ∃ n : ℕ, g ^ n * x ∈ J.map (algebraMap A B))
    (Bg C : Type*) [CommRing Bg] [CommRing C] [Algebra B Bg] [IsLocalization.Away g Bg]
    (r : Bg →+* C) (hr : Function.Surjective r)
    (hker : RingHom.ker r = (Ideal.span {f}).map (algebraMap B Bg)) :
    ((Ideal.span {f}).map (algebraMap B Bg)).IsRegularPrincipal ∧
      (r.comp ((algebraMap B Bg).comp (algebraMap A B))).Flat := by
  classical
  set s := algebraMap B Bg f
  have hspan : (Ideal.span {f}).map (algebraMap B Bg) = Ideal.span {s} := by
    rw [Ideal.map_span, Set.image_singleton]
  let : Algebra A Bg := ((algebraMap B Bg).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B Bg := .of_algebraMap_eq fun _ ↦ rfl
  have key : ∀ (J : Ideal A) (m : Bg), s * m ∈ J.map (algebraMap A Bg) →
      m ∈ J.map (algebraMap A Bg) := by
    intro J m hm
    have hJ : J.map (algebraMap A Bg) = (J.map (algebraMap A B)).map (algebraMap B Bg) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    rw [hJ] at hm ⊢
    exact mem_map_of_mul_mem_map_of_forall hP Bg J m hm
  have hs : s ∈ nonZeroDivisors Bg := algebraMap_mem_nonZeroDivisors_of_forall hP Bg
  refine ⟨hspan ▸ Ideal.isRegularPrincipal_span_singleton hs, ?_⟩
  have : Module.Flat B Bg := IsLocalization.flat Bg (Submonoid.powers g)
  have : Module.Flat A Bg := Module.Flat.trans A B Bg
  let φ : Bg →ₗ[A] Bg := (LinearMap.mulLeft Bg s).restrictScalars A
  have hφ : Module.Flat A (Bg ⧸ LinearMap.range φ) := by
    refine Module.Flat.quotient_range φ fun J m hm ↦ ?_
    rw [Ideal.smul_top_eq_map] at hm ⊢
    exact key J m hm
  have hrange : (Ideal.span {s} : Ideal Bg).restrictScalars A = LinearMap.range φ := by
    ext x
    rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton', LinearMap.mem_range]
    exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha, mul_comm]; rfl⟩,
      fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha, mul_comm]; rfl⟩⟩
  let D := Bg ⧸ (Ideal.span {s} : Ideal Bg)
  have hD : Module.Flat A D := Module.Flat.of_linearEquiv
    ((Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {s} : Ideal Bg)).symm.trans
      (Submodule.quotEquivOfEq _ _ hrange))
  let e : D ≃+* C := (Ideal.quotEquivOfEq (hspan ▸ hker.symm)).trans
    (RingHom.quotientKerEquivOfSurjective hr)
  let : Algebra A C := (r.comp ((algebraMap B Bg).comp (algebraMap A B))).toAlgebra
  let eA : D ≃ₐ[A] C := AlgEquiv.ofRingEquiv (f := e) fun a ↦ rfl
  exact Module.Flat.of_linearEquiv eA.toLinearEquiv.symm

end Algebra

/-- An equation which locally generates a regular principal ideal is a nonzerodivisor. -/
lemma eq_zero_of_mul_eq_zero_of_forall_isRegularPrincipal {R : Type*} [CommRing R]
    (a : R) (h : ∀ P : Ideal R, P.IsPrime → ∃ g ∉ P,
      ((Ideal.span {a}).map (algebraMap R (Localization.Away g))).IsRegularPrincipal)
    (x : R) (hx : a * x = 0) : x = 0 := by
  by_contra hne
  have hann : (Submodule.span R {x}).annihilator ≠ ⊤ := by
    intro htop
    apply hne
    have : (1 : R) ∈ (Submodule.span R {x}).annihilator := htop ▸ Submodule.mem_top
    simpa using (Submodule.mem_annihilator_span_singleton _ _).mp this
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hann
  obtain ⟨g, hg, s, hs, hspan⟩ := h P hP.isPrime
  rw [Ideal.map_span, Set.image_singleton] at hspan
  have ha := mem_nonZeroDivisors_of_span_singleton_eq hs hspan
  have hx' : algebraMap R (Localization.Away g) x = 0 :=
    (mem_nonZeroDivisors_iff.mp ha).1 _ (by rw [← map_mul, hx, map_zero])
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ x).mp hx'
  exact hg (hP.isPrime.mem_of_pow_mem n
    (hle ((Submodule.mem_annihilator_span_singleton _ _).mpr hn)))

/-- A fibrewise Cartier equation in a flat finitely presented algebra lifts to
a regular equation with flat quotient on a neighborhood of the given prime. -/
theorem Algebra.exists_notMem_isRegularPrincipal_and_flat_of_fiber {A B K : Type*}
    [CommRing A] [CommRing B] [CommRing K] [Algebra A B] [Algebra A K] [Module.Flat A B]
    [Algebra.FinitePresentation A B] (_hK : IsField K) (I : Ideal B) (hI : I.IsPrincipal)
    (q : Ideal B) [q.IsPrime] (hKq : RingHom.ker (algebraMap A K) = q.comap (algebraMap A B))
    (hfib : ∀ P : Ideal (B ⊗[A] K), P.IsPrime → ∃ g ∉ P,
      ((I.map Algebra.TensorProduct.includeLeftRingHom).map
        (algebraMap (B ⊗[A] K) (Localization.Away g))).IsRegularPrincipal) :
    ∃ g ∉ q, ∀ (Bg C : Type*) [CommRing Bg] [CommRing C] [Algebra B Bg]
      [IsLocalization.Away g Bg] (r : Bg →+* C), Function.Surjective r →
      RingHom.ker r = I.map (algebraMap B Bg) →
      (I.map (algebraMap B Bg)).IsRegularPrincipal ∧
        (r.comp ((algebraMap B Bg).comp (algebraMap A B))).Flat := by
  obtain ⟨f, rfl⟩ := hI.1
  have hnzd : ∀ x : B ⊗[A] K, f • x = 0 → x = 0 := by
    intro x hx
    rw [Algebra.TensorProduct.smul_eq_tmul_one_mul] at hx
    refine eq_zero_of_mul_eq_zero_of_forall_isRegularPrincipal _ (fun P hP ↦ ?_) x hx
    obtain ⟨g, hg, hreg⟩ := hfib P hP
    have heq : (Ideal.span {f} : Ideal B).map Algebra.TensorProduct.includeLeftRingHom =
        Ideal.span {f ⊗ₜ[A] (1 : K)} := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    rw [heq] at hreg
    exact ⟨g, hg, hreg⟩
  obtain ⟨g, hg, hP⟩ := Algebra.exists_notMem_forall_mul_mem_map q f 1
    ((Ideal.ne_top_iff_one q).mp (Ideal.IsPrime.ne_top ‹_›)) hKq
    (fun x hx ↦ by rw [one_smul]; exact hnzd x hx)
  exact ⟨g, hg, fun Bg C _ _ _ _ r hr hker ↦
    Algebra.isRegularPrincipal_and_flat_of_forall_mul_mem_map f g hP Bg C r hr hker⟩
