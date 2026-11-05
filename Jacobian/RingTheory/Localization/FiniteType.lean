import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Away.Lemmas

/-!
# Finite generators with a common denominator

A finite-type localization away from one element admits a finite family of
algebra generators sharing a single denominator power.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Algebra.FiniteType

variable {baseRing sourceRing : Type*} [CommRing baseRing] [CommRing sourceRing] (denominator : sourceRing)
  (localizationRing : Type*) [CommRing localizationRing] [Algebra sourceRing localizationRing] [Algebra baseRing localizationRing]
  [IsLocalization.Away denominator localizationRing] [Algebra.FiniteType baseRing localizationRing]

theorem exists_adjoin_mk'_eq_top :
    ∃ (exponent : ℕ) (numerators : Finset sourceRing),
      Algebra.adjoin baseRing
        ((fun element ↦ IsLocalization.mk' localizationRing element (⟨denominator ^ exponent, exponent, rfl⟩ : Submonoid.powers denominator)) '' numerators) = ⊤ := by
  classical
  obtain ⟨generators, hs⟩ := ‹Algebra.FiniteType baseRing localizationRing›.out

  set numerator : localizationRing → sourceRing := fun element ↦ (IsLocalization.Away.sec denominator element).1
  set denominatorExponent : localizationRing → ℕ := fun element ↦ (IsLocalization.Away.sec denominator element).2

  set exponent : ℕ := generators.sup denominatorExponent
  refine ⟨exponent, generators.image fun element ↦ numerator element * denominator ^ (exponent - denominatorExponent element), ?_⟩
  have key : ∀ element ∈ generators, IsLocalization.mk' localizationRing (numerator element * denominator ^ (exponent - denominatorExponent element))
      (⟨denominator ^ exponent, exponent, rfl⟩ : Submonoid.powers denominator) = element := by
    intro element hx
    have hxN : denominatorExponent element ≤ exponent := Finset.le_sup hx
    have hx' : element = IsLocalization.mk' localizationRing (numerator element) (⟨denominator ^ denominatorExponent element, denominatorExponent element, rfl⟩ : Submonoid.powers denominator) :=
      IsLocalization.eq_mk'_iff_mul_eq.mpr (IsLocalization.Away.sec_spec denominator element)
    have hb : denominator ^ exponent * numerator element = denominator ^ denominatorExponent element * (numerator element * denominator ^ (exponent - denominatorExponent element)) := by
      rw [mul_comm (numerator element), ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hxN]
    exact (IsLocalization.mk'_eq_of_eq hb).trans hx'.symm
  rw [← hs]
  congr 1
  rw [Finset.coe_image, Set.image_image]
  simpa using Set.image_congr key

theorem exists_surjective_aeval_mk' :
    ∃ (exponent : ℕ) (generatorIndex : Type) (_ : Finite generatorIndex) (numerators : generatorIndex → sourceRing),
      Function.Surjective
        (MvPolynomial.aeval (R := baseRing)
          (fun μ ↦ IsLocalization.mk' localizationRing (numerators μ) (⟨denominator ^ exponent, exponent, rfl⟩ : Submonoid.powers denominator))) := by
  classical
  obtain ⟨exponent, numerators, hc⟩ := exists_adjoin_mk'_eq_top (baseRing := baseRing) denominator localizationRing
  let enumeration : Fin numerators.card ≃ {element : sourceRing // element ∈ numerators} := (Fintype.equivFinOfCardEq (Fintype.card_coe numerators)).symm
  refine ⟨exponent, Fin numerators.card, inferInstance, fun generator ↦ (enumeration generator : sourceRing), ?_⟩
  rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
  convert hc using 2
  ext image
  simp only [Set.mem_range, Set.mem_image, Finset.mem_coe]
  exact ⟨fun ⟨generator, hi⟩ ↦ ⟨enumeration generator, (enumeration generator).2, hi⟩, fun ⟨element, hx, hy⟩ ↦ ⟨enumeration.symm ⟨element, hx⟩, by simpa using hy⟩⟩

end Algebra.FiniteType
