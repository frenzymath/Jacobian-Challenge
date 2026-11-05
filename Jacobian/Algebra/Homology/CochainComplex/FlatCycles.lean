import Jacobian.RingTheory.Flat.Exact
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Flat cycles and tensor exactness in cochain complexes

Exactness after reduction modulo every ideal forces the high-degree cycles of
an eventually exact complex of flat modules to be flat. Flatness then propagates
downward through the exact tail, which remains exact after tensoring with any
module. These results apply without a bound on the terms of the complex.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory TensorProduct

namespace CochainComplex

variable {A : Type u} [CommRing A] (C : CochainComplex (ModuleCat.{u} A) ℤ)

/-- Exactness of a complex of modules in degree `k + 1` is exactness of the underlying linear
maps. -/
lemma exactAt_iff_exact (k : ℤ) :
    C.ExactAt (k + 1) ↔ Function.Exact (C.d k (k + 1)).hom (C.d (k + 1) (k + 1 + 1)).hom := by
  rw [HomologicalComplex.exactAt_iff' C k (k + 1) (k + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker, LinearMap.exact_iff]
  exact eq_comm

/-- The differential `Cᵏ ⟶ Zᵏ⁺¹` onto the cycles of the next degree. -/
noncomputable abbrev dToKer (k : ℤ) :
    C.X k →ₗ[A] LinearMap.ker (C.d (k + 1) (k + 1 + 1)).hom :=
  (C.d k (k + 1)).hom.codRestrict _ fun x ↦ by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, C.d_comp_d]
    rfl

lemma subtype_comp_dToKer (k : ℤ) :
    (LinearMap.ker (C.d (k + 1) (k + 1 + 1)).hom).subtype ∘ₗ C.dToKer k = (C.d k (k + 1)).hom :=
  rfl

lemma exact_subtype_dToKer (k : ℤ) :
    Function.Exact (LinearMap.ker (C.d k (k + 1)).hom).subtype (C.dToKer k) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, congrArg Subtype.val hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact Subtype.ext y.2

lemma surjective_dToKer (k : ℤ) (hk : C.ExactAt (k + 1)) : Function.Surjective (C.dToKer k) := by
  rintro ⟨z, hz⟩
  obtain ⟨x, hx⟩ := ((C.exactAt_iff_exact k).1 hk z).1 hz
  exact ⟨x, Subtype.ext hx⟩

lemma dToKer_comp_d (k : ℤ) : C.dToKer (k + 1) ∘ₗ (C.d k (k + 1)).hom = 0 := by
  ext x
  exact congrArg (fun φ : C.X k ⟶ C.X (k + 1 + 1) ↦ φ.hom x) (C.d_comp_d k (k + 1) (k + 1 + 1))

variable {C}

/-- If `C` is exact in degree `k + 1` and `Cᵏ`, `Zᵏ⁺¹` are flat, then so is `Zᵏ`. -/
lemma flat_ker_d_of_flat_ker_d_succ (k : ℤ) [Module.Flat A (C.X k)] (hk : C.ExactAt (k + 1))
    (h : Module.Flat A (LinearMap.ker (C.d (k + 1) (k + 1 + 1)).hom)) :
    Module.Flat A (LinearMap.ker (C.d k (k + 1)).hom) :=
  Module.Flat.of_exact_of_flat_of_flat_right _ _ Subtype.val_injective (C.surjective_dToKer k hk)
    (C.exact_subtype_dToKer k)

/-- **Flatness of the cycles propagates downwards.** Let `C` be a complex of flat modules, exact
in degrees `≥ m`, whose cycles `Zᵏ` are flat for `k ≥ N`. Then `Zᵏ` is flat for all
`k ≥ m - 1`. -/
theorem flat_ker_d_of_exactAt (hC : ∀ k, Module.Flat A (C.X k)) {m N : ℤ}
    (hex : ∀ k, m ≤ k → C.ExactAt k)
    (hN : ∀ k, N ≤ k → Module.Flat A (LinearMap.ker (C.d k (k + 1)).hom))
    (k : ℤ) (hk : m - 1 ≤ k) : Module.Flat A (LinearMap.ker (C.d k (k + 1)).hom) := by
  suffices h : ∀ t : ℕ, ∀ k : ℤ, m - 1 ≤ k → N ≤ k + t →
      Module.Flat A (LinearMap.ker (C.d k (k + 1)).hom) from
    h (N - k).toNat k hk (by omega)
  intro t
  induction t with
  | zero => exact fun k _ hk ↦ hN k (by simpa using hk)
  | succ t ih =>
    intro k hk hkt
    have := hC k
    exact flat_ker_d_of_flat_ker_d_succ k (hex _ (by omega)) (ih (k + 1) (by omega) (by omega))

variable (P : Type u) [AddCommGroup P] [Module A P]

/-- If `Zᵏ⁺¹` is flat and `C` is exact in degree `k + 1`, then `P ⊗ Zᵏ ⟶ P ⊗ Cᵏ` is injective. -/
lemma injective_lTensor_subtype_ker_d (k : ℤ) (hk : C.ExactAt (k + 1))
    [Module.Flat A (LinearMap.ker (C.d (k + 1) (k + 1 + 1)).hom)] :
    Function.Injective ((LinearMap.ker (C.d k (k + 1)).hom).subtype.lTensor P) :=
  LinearMap.lTensor_injective_of_exact_of_flat _ (C.surjective_dToKer k hk) _ Subtype.val_injective
    (C.exact_subtype_dToKer k) P

/-- **Cycles after base change.** If `C` is exact in degrees `k + 1` and `k + 2`, and `Cᵏ⁺¹`,
`Zᵏ⁺²` are flat, then the cycles of `P ⊗ C` in degree `k` are `P ⊗ Zᵏ`. -/
lemma range_lTensor_subtype_ker_d (k : ℤ) (hk₁ : C.ExactAt (k + 1)) (hk₂ : C.ExactAt (k + 1 + 1))
    [Module.Flat A (LinearMap.ker (C.d (k + 1 + 1) (k + 1 + 1 + 1)).hom)] :
    LinearMap.range ((LinearMap.ker (C.d k (k + 1)).hom).subtype.lTensor P) =
      LinearMap.ker ((C.d k (k + 1)).hom.lTensor P) := by
  have hinj := injective_lTensor_subtype_ker_d (C := C) P (k + 1) hk₂
  have e : (C.d k (k + 1)).hom.lTensor P =
      (LinearMap.ker (C.d (k + 1) (k + 1 + 1)).hom).subtype.lTensor P ∘ₗ
        (C.dToKer k).lTensor P := by
    rw [← LinearMap.lTensor_comp]
    rfl
  rw [e, LinearMap.ker_comp, LinearMap.ker_eq_bot.2 hinj, Submodule.comap_bot]
  exact ((lTensor_exact P (C.exact_subtype_dToKer k)
    (C.surjective_dToKer k hk₁)).linearMap_ker_eq).symm

/-- **Exactness after base change.** Let `C` be exact in degrees `≥ m`, with `Zʲ` flat for
`j ≥ m - 1`. Then `P ⊗ C` is exact in degrees `≥ m`. -/
theorem exact_lTensor_d {m : ℤ} (hex : ∀ j, m ≤ j → C.ExactAt j)
    (hZ : ∀ j, m - 1 ≤ j → Module.Flat A (LinearMap.ker (C.d j (j + 1)).hom)) (k : ℤ)
    (hk : m ≤ k + 1) :
    Function.Exact ((C.d k (k + 1)).hom.lTensor P) ((C.d (k + 1) (k + 1 + 1)).hom.lTensor P) := by
  have := hZ (k + 1 + 1 + 1) (by omega)
  rw [LinearMap.exact_iff, ← range_lTensor_subtype_ker_d P (k + 1) (hex _ (by omega))
    (hex _ (by omega)), ← C.subtype_comp_dToKer k, LinearMap.lTensor_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.2 (LinearMap.lTensor_surjective P (C.surjective_dToKer k
      (hex _ hk))), Submodule.map_top]

/-- **Flat cycles from exactness modulo ideals.** Let `C` be a complex of flat modules, exact in
degrees `≥ n`, such that `A/I ⊗ C` is exact in degrees `≥ n` for every ideal `I`. Then the
cycles `Zᵏ` are flat for `k ≥ n + 2`: the kernel of `A/I ⊗ Zᵏ⁻¹ ⟶ A/I ⊗ Cᵏ⁻¹`, which is
`Tor₁(A/I, Zᵏ)`, vanishes. -/
theorem flat_ker_d_of_exact_lTensor_quotient (hC : ∀ k, Module.Flat A (C.X k)) {n : ℤ}
    (hex : ∀ k, n ≤ k → C.ExactAt k)
    (hI : ∀ (I : Ideal A) (k : ℤ), n ≤ k + 1 → Function.Exact ((C.d k (k + 1)).hom.lTensor (A ⧸ I))
      ((C.d (k + 1) (k + 1 + 1)).hom.lTensor (A ⧸ I)))
    (k : ℤ) (hk : n + 2 ≤ k) : Module.Flat A (LinearMap.ker (C.d k (k + 1)).hom) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 + 1 + 1 := ⟨k - 3, by omega⟩
  have := hC (i + 1 + 1)
  refine Module.Flat.of_exact_of_lTensor_quotient_injective (C.exact_subtype_dToKer (i + 1 + 1))
    (C.surjective_dToKer (i + 1 + 1) (hex _ (by omega))) fun I ↦ ?_
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨c, rfl⟩ := LinearMap.lTensor_surjective (A ⧸ I) (C.surjective_dToKer (i + 1)
    (hex _ (by omega))) w
  have hc : (C.d (i + 1) (i + 1 + 1)).hom.lTensor (A ⧸ I) c = 0 := by
    rw [← C.subtype_comp_dToKer (i + 1), LinearMap.lTensor_comp, LinearMap.comp_apply, hw]
  obtain ⟨c', rfl⟩ := ((hI I i (by omega)) c).1 hc
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, C.dToKer_comp_d i, LinearMap.lTensor_zero,
    LinearMap.zero_apply]

/-- Truncating a complex of flat modules at a flat module of cycles gives flat terms. -/
lemma flat_truncLE_X (complex : CochainComplex (ModuleCat.{u} A) ℤ) (bound : ℤ)
    (flatTerms : ∀ degree, Module.Flat A (complex.X degree))
    (flatCycles : Module.Flat A (LinearMap.ker (complex.d bound (bound + 1)).hom))
    (degree : ℤ) : Module.Flat A ((complex.truncLE bound).X degree) := by
  rcases lt_trichotomy degree bound with below | rfl | above
  · have := flatTerms degree
    exact Module.Flat.of_linearEquiv (complex.truncLEXIso bound degree below).toLinearEquiv
  · have flatKernel : Module.Flat A (LinearMap.ker (complex.sc degree).g.hom) := by
      change Module.Flat A (LinearMap.ker (complex.d degree ((ComplexShape.up ℤ).next degree)).hom)
      rw [CochainComplex.next]
      exact flatCycles
    have : Module.Flat A (complex.sc degree).moduleCatLeftHomologyData.K := flatKernel
    exact Module.Flat.of_linearEquiv
      (complex.truncLEXIsoCycles degree ≪≫ (complex.sc degree).moduleCatCyclesIso).toLinearEquiv
  · have : Subsingleton ((complex.truncLE bound).X degree) :=
      ModuleCat.isZero_iff_subsingleton.mp
        ((complex.truncLE bound).isZero_of_isStrictlyLE bound degree above)
    infer_instance

end CochainComplex
