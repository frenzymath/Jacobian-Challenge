import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Unramified.Basic

/-!
# Separating elements of function fields

If the module of Kähler differentials of a field extension is one-dimensional, a
nonzero differential generates it. An intermediate ring containing an element with
nonzero differential therefore makes the extension formally unramified. When the
extension has a transcendental element, a generator can be chosen transcendental.
-/

noncomputable section

open KaehlerDifferential

/-- An intermediate ring containing a generator of the one-dimensional module of
differentials makes the field extension formally unramified. -/
theorem Algebra.FormallyUnramified.of_finrank_kaehlerDifferential_eq_one
    {baseRing intermediateRing extensionField : Type*}
    [CommRing baseRing] [CommRing intermediateRing] [Field extensionField]
    [Algebra baseRing intermediateRing] [Algebra intermediateRing extensionField]
    [Algebra baseRing extensionField] [IsScalarTower baseRing intermediateRing extensionField]
    (dimension : Module.finrank extensionField Ω[extensionField⁄baseRing] = 1)
    {element : extensionField} (nonzero : D baseRing extensionField element ≠ 0)
    (inRange : element ∈ Set.range (algebraMap intermediateRing extensionField)) :
    Algebra.FormallyUnramified intermediateRing extensionField := by
  refine ⟨subsingleton_of_forall_eq 0 fun differential ↦ ?_⟩
  obtain ⟨preimage, rfl⟩ :=
    KaehlerDifferential.map_surjective baseRing intermediateRing extensionField differential
  obtain ⟨scalar, rfl⟩ := (finrank_eq_one_iff_of_nonzero' _ nonzero).mp dimension preimage
  obtain ⟨element, rfl⟩ := inRange
  rw [LinearMap.map_smul, KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply,
    Derivation.map_algebraMap, smul_zero]

/-- A field with one-dimensional differentials and a transcendental element has a
transcendental element with nonzero differential. -/
theorem exists_transcendental_and_D_ne_zero {baseField baseRing extensionField : Type*}
    [Field baseField] [CommRing baseRing] [Field extensionField]
    [Algebra baseField extensionField] [Algebra baseRing extensionField]
    (dimension : Module.finrank extensionField Ω[extensionField⁄baseRing] = 1)
    {transcendentalElement : extensionField}
    (transcendental : Transcendental baseField transcendentalElement) :
    ∃ element : extensionField,
      Transcendental baseField element ∧ D baseRing extensionField element ≠ 0 := by
  obtain ⟨generator, generator_nonzero⟩ :
      ∃ element : extensionField, D baseRing extensionField element ≠ 0 := by
    by_contra! all_zero
    have span_zero : (⊤ : Submodule extensionField Ω[extensionField⁄baseRing]) = ⊥ := by
      rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
      rintro _ ⟨element, rfl⟩
      exact all_zero element
    have : Subsingleton Ω[extensionField⁄baseRing] :=
      subsingleton_of_forall_eq 0 fun differential ↦ by
        simpa using
          (span_zero ▸ Submodule.mem_top :
            differential ∈ (⊥ : Submodule extensionField Ω[extensionField⁄baseRing]))
    simp [Module.finrank_zero_of_subsingleton] at dimension
  by_cases differential_zero : D baseRing extensionField transcendentalElement = 0
  swap
  · exact ⟨transcendentalElement, transcendental, differential_zero⟩
  by_cases generator_transcendental : Transcendental baseField generator
  · exact ⟨generator, generator_transcendental, generator_nonzero⟩
  rw [Transcendental, not_not] at generator_transcendental
  have transcendental_ne_zero : transcendentalElement ≠ 0 :=
    fun equality ↦ transcendental (equality ▸ isAlgebraic_zero)
  have generator_ne_zero : generator ≠ 0 :=
    fun equality ↦ generator_nonzero (by rw [equality, map_zero])
  refine ⟨generator * transcendentalElement, fun algebraic ↦ transcendental ?_, ?_⟩
  · have equality :
        transcendentalElement = generator * transcendentalElement * generator⁻¹ := by
      field_simp
    rw [equality]
    exact algebraic.mul generator_transcendental.inv
  · rw [Derivation.leibniz, differential_zero, smul_zero, zero_add]
    exact smul_ne_zero transcendental_ne_zero generator_nonzero
