import Mathlib.RingTheory.Flat.Stability

/-!
# Semilinear transport of flatness

Flatness is invariant under compatible bijections of the coefficient rings and
underlying additive groups. The scalar actions may be induced by distinct ring
homomorphisms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- **Semilinear transport of flatness.** Let `φ : R →+* A` and `ψ : R' →+* B` be ring maps, `M`
an `A`-module and `N` a `B`-module, regarded as an `R`- resp. `R'`-module by restriction of
scalars. If `σ : R →+* R'` is bijective and `u : M →+ N` is bijective with
`u (φ r • m) = ψ (σ r) • u m`, then flatness of `M` over `R` implies flatness of `N` over `R'`. -/
theorem Module.Flat.of_bijective_compHom {R R' A B M N : Type*} [CommRing R] [CommRing R']
    [CommRing A] [CommRing B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (φ : R →+* A) (ψ : R' →+* B) (σ : R →+* R') (hσ : Function.Bijective σ) (u : M →+ N)
    (hu : Function.Bijective u) (hsmul : ∀ (r : R) (m : M), u (φ r • m) = ψ (σ r) • u m)
    (h : letI := Module.compHom M φ; Module.Flat R M) :
    letI := Module.compHom N ψ; Module.Flat R' N := by
  let := Module.compHom M φ
  let := Module.compHom N ψ
  let e : R ≃+* R' := RingEquiv.ofBijective σ hσ
  let : Module R N := Module.compHom N (ψ.comp σ)
  have : Module.Flat R N := Module.Flat.of_linearEquiv
    ({ AddEquiv.ofBijective u hu with map_smul' := hsmul } : M ≃ₗ[R] N).symm
  let : Algebra R' R := e.symm.toRingHom.toAlgebra
  have : IsScalarTower R' R N := ⟨fun r' r n ↦ (congrArg (· • n) ((congrArg ψ
    ((map_mul e _ _).trans (congrArg (· * e r) (e.apply_symm_apply r')))).trans
      (map_mul ψ _ _))).trans (mul_smul _ _ _)⟩
  have : Module.Flat R' R := Module.Flat.of_linearEquiv
    ({ e.toAddEquiv with
        map_smul' := fun r' r ↦
          (map_mul e _ _).trans (congrArg (· * e r) (e.apply_symm_apply r')) } : R ≃ₗ[R'] R')
  exact Module.Flat.trans R' R N
