import Jacobian.RingTheory.LocalRing.ResidueField.RegularFiber
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# The flat locus and finitely generated flat models

Flatness at a prime is stable under base change. Over a noetherian base the
flat locus of a finite type algebra is open. Flatness on a compact set of
primes descends to a finitely generated subalgebra of the base.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

/-- Flatness of a localization is preserved by base change. -/
theorem Module.Flat.localization_of_isPushout {R R' S S' : Type*} [CommRing R] [CommRing R']
    [CommRing S] [CommRing S'] [Algebra R R'] [Algebra R S] [Algebra R' S'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R R' S S']
    (Q : Ideal S') [Q.IsPrime]
    (h : Module.Flat R (Localization.AtPrime (Q.comap (algebraMap S S')))) :
    Module.Flat R' (Localization.AtPrime Q) := by
  set Q₁ := Q.comap (algebraMap S S')
  set M := Algebra.algebraMapSubmonoid S' Q₁.primeCompl
  have hle : M ≤ Q.primeCompl := by
    rintro _ ⟨s, hs, rfl⟩
    exact hs
  let : Algebra (Localization M) (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ M Q.primeCompl hle
  have : IsScalarTower S' (Localization M) (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ M Q.primeCompl hle
  have : IsScalarTower R' (Localization M) (Localization.AtPrime Q) :=
    .of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply R' S' (Localization M), ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
  have : IsLocalization (Q.primeCompl.map (algebraMap S' (Localization M)))
      (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ M Q.primeCompl hle
  have : Module.Flat (Localization M) (Localization.AtPrime Q) :=
    IsLocalization.flat _ (Q.primeCompl.map (algebraMap S' (Localization M)))
  have : Algebra.IsPushout S (Localization.AtPrime Q₁) S' (Localization M) :=
    (Algebra.isPushout_of_isLocalization Q₁.primeCompl (Localization.AtPrime Q₁) S'
      (Localization M)).symm
  have : Algebra.IsPushout R S R' S' := Algebra.IsPushout.symm inferInstance
  have : IsScalarTower R (Localization.AtPrime Q₁) (Localization M) :=
    .of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q₁),
        ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S' (Localization M),
        IsScalarTower.algebraMap_apply R S S', ← IsScalarTower.algebraMap_apply S S']
  have : Algebra.IsPushout R (Localization.AtPrime Q₁) R' (Localization M) :=
    (Algebra.IsPushout.comp_iff R S R' S').mpr inferInstance
  have : Module.Flat R' (Localization M) :=
    Module.Flat.isBaseChange R R' (Localization.AtPrime Q₁) (Localization M)
      (Algebra.IsPushout.symm this).out
  exact Module.Flat.trans R' (Localization M) (Localization.AtPrime Q)

/-- Flatness at a prime persists when the base subalgebra is enlarged. -/
theorem Module.Flat.localization_tensorProduct_map {R₀ R R' S₀ : Type*} [CommRing R₀]
    [CommRing R] [CommRing R'] [CommRing S₀] [Algebra R₀ R] [Algebra R₀ R'] [Algebra R₀ S₀]
    (f : R →ₐ[R₀] R') (Q : Ideal (R' ⊗[R₀] S₀)) [Q.IsPrime] (P : Ideal (R ⊗[R₀] S₀)) [P.IsPrime]
    (hPQ : Q.comap (Algebra.TensorProduct.map f (AlgHom.id R₀ S₀)).toRingHom = P)
    (h : Module.Flat R (Localization.AtPrime P)) :
    Module.Flat R' (Localization.AtPrime Q) := by
  subst hPQ
  let : Algebra R R' := f.toRingHom.toAlgebra
  have : IsScalarTower R₀ R R' := .of_algebraMap_eq fun r ↦ (f.commutes r).symm
  let : Algebra (R ⊗[R₀] S₀) (R' ⊗[R₀] S₀) :=
    (Algebra.TensorProduct.map f (AlgHom.id R₀ S₀)).toRingHom.toAlgebra
  have : IsScalarTower R (R ⊗[R₀] S₀) (R' ⊗[R₀] S₀) := .of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have : Algebra.IsPushout R R' (R ⊗[R₀] S₀) (R' ⊗[R₀] S₀) :=
    Algebra.IsPushout.tensorProduct_tensorProduct R₀ S₀ R R' (by
      ext x
      simp [RingHom.algebraMap_toAlgebra])
  exact Module.Flat.localization_of_isPushout Q h

namespace PrimeSpectrum

/-- The flat locus of a finite type algebra over a noetherian ring is open. -/
theorem isOpen_setOf_flat_localization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] :
    IsOpen {q : PrimeSpectrum S | Module.Flat R (Localization.AtPrime q.asIdeal)} := by
  rw [isOpen_iff_forall_mem_open]
  intro q (hq : Module.Flat R _)
  have hP : Module.Flat R (LocalizedModule q.asIdeal.primeCompl S) := Module.Flat.of_linearEquiv
    ((IsLocalizedModule.iso q.asIdeal.primeCompl
      (Algebra.linearMap S (Localization.AtPrime q.asIdeal))).restrictScalars R)
  obtain ⟨g, hg, hopen⟩ :=
    Module.Flat.exists_notMem_forall_flat_localizedModule q.asIdeal hP
  refine ⟨basicOpen g, fun Q hQ ↦ ?_, isOpen_basicOpen, hg⟩
  have := hopen Q.asIdeal hQ
  exact Module.Flat.of_linearEquiv
    ((IsLocalizedModule.iso Q.asIdeal.primeCompl
      (Algebra.linearMap S (Localization.AtPrime Q.asIdeal))).restrictScalars R).symm

universe u

theorem flat_localization_tensorProduct_of_le {R₀ A S₀ : Type*} [CommRing R₀] [CommRing A]
    [CommRing S₀] [Algebra R₀ A] [Algebra R₀ S₀] {R R' : Subalgebra R₀ A} (h : R ≤ R')
    (q : PrimeSpectrum (A ⊗[R₀] S₀))
    (hq : Module.Flat R (Localization.AtPrime (comap (Algebra.TensorProduct.map R.val
        (AlgHom.id R₀ S₀) : R ⊗[R₀] S₀ →+* A ⊗[R₀] S₀) q).asIdeal)) :
    Module.Flat R' (Localization.AtPrime (comap (Algebra.TensorProduct.map R'.val
        (AlgHom.id R₀ S₀) : R' ⊗[R₀] S₀ →+* A ⊗[R₀] S₀) q).asIdeal) := by
  refine Module.Flat.localization_tensorProduct_map (Subalgebra.inclusion h) _ _ ?_ hq
  rw [comap_asIdeal, comap_asIdeal, Ideal.comap_comap]
  congr 1
  ext x
  · rfl
  · rfl

/-- For a finitely generated subalgebra `R` of `A` over a noetherian ring `R₀` and a finite type
`R₀`-algebra `S₀`, the primes `q` of `A ⊗[R₀] S₀` such that `R ⊗[R₀] S₀` is flat over `R` at the
prime below `q` form an open set. -/
theorem isOpen_setOf_flat_localization_tensorProduct {R₀ A S₀ : Type*} [CommRing R₀]
    [CommRing A] [CommRing S₀] [Algebra R₀ A] [Algebra R₀ S₀] [IsNoetherianRing R₀]
    [Algebra.FiniteType R₀ S₀] {R : Subalgebra R₀ A} (hR : R.FG) :
    IsOpen {q : PrimeSpectrum (A ⊗[R₀] S₀) | Module.Flat R (Localization.AtPrime
      (comap (Algebra.TensorProduct.map R.val (AlgHom.id R₀ S₀) : R ⊗[R₀] S₀ →+* A ⊗[R₀] S₀)
        q).asIdeal)} := by
  have : Algebra.FiniteType R₀ R := (Subalgebra.fg_iff_finiteType _).mp hR
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing R₀ R
  exact (isOpen_setOf_flat_localization (R := R) (S := R ⊗[R₀] S₀)).preimage
    (continuous_comap _)

/-- **Flatness along a quasi-compact set descends to a finitely generated subring** (Stacks
`00R6`). Let `R₀` be noetherian, `S₀` a finite type `R₀`-algebra and `A` an `R₀`-algebra such that
`A ⊗[R₀] S₀` is flat over `A`. For a quasi-compact set `K` of primes of `A ⊗[R₀] S₀` there is a
finitely generated subalgebra `R₁` of `A` such that `R₁ ⊗[R₀] S₀` is flat over `R₁` at every prime
lying under a prime of `K`.

Each prime has a neighbourhood on which some `R ⊗[R₀] S₀` is flat
(`Module.exists_fg_flat_localization_tensor` and openness of the flat locus), and flatness persists
when `R` grows. -/
theorem exists_fg_forall_flat_localization_tensor_of_isCompact {R₀ A S₀ : Type u} [CommRing R₀]
    [CommRing A] [CommRing S₀] [Algebra R₀ A] [Algebra R₀ S₀] [IsNoetherianRing R₀]
    [Algebra.FiniteType R₀ S₀] [Module.Flat A (A ⊗[R₀] S₀)]
    {K : Set (PrimeSpectrum (A ⊗[R₀] S₀))} (hK : IsCompact K) :
    ∃ R₁ : Subalgebra R₀ A, R₁.FG ∧ ∀ q ∈ K,
      Module.Flat R₁ (Localization.AtPrime (comap (Algebra.TensorProduct.map R₁.val
        (AlgHom.id R₀ S₀) : R₁ ⊗[R₀] S₀ →+* A ⊗[R₀] S₀) q).asIdeal) := by
  classical
  let W (R : Subalgebra R₀ A) : Set (PrimeSpectrum (A ⊗[R₀] S₀)) :=
    {q | Module.Flat R (Localization.AtPrime (comap (Algebra.TensorProduct.map R.val
        (AlgHom.id R₀ S₀) : R ⊗[R₀] S₀ →+* A ⊗[R₀] S₀) q).asIdeal)}
  have hWcov (q : PrimeSpectrum (A ⊗[R₀] S₀)) :
      ∃ R : {R : Subalgebra R₀ A // R.FG}, q ∈ W R.1 := by
    obtain ⟨R, hR, -, hflat⟩ := Module.exists_fg_flat_localization_tensor (S₀ := S₀) q.asIdeal
    exact ⟨⟨R, hR⟩, hflat⟩
  have : Nonempty {R : Subalgebra R₀ A // R.FG} := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  obtain ⟨⟨R₁, hR₁⟩, hK'⟩ := hK.elim_directed_cover (fun R ↦ W R.1)
    (fun R ↦ isOpen_setOf_flat_localization_tensorProduct R.2)
    (fun q _ ↦ Set.mem_iUnion.mpr (hWcov q))
    fun (R R' : {R : Subalgebra R₀ A // R.FG}) ↦ ⟨⟨R.1 ⊔ R'.1, R.2.sup R'.2⟩,
      flat_localization_tensorProduct_of_le le_sup_left,
      flat_localization_tensorProduct_of_le le_sup_right⟩
  exact ⟨R₁, hR₁, fun q hq ↦ hK' hq⟩

end PrimeSpectrum
