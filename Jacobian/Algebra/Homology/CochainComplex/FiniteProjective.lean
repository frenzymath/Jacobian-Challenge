import Jacobian.Algebra.Homology.CochainComplex.FlatCycles
import Jacobian.Algebra.Homology.MappingCone.Flat
import Jacobian.RingTheory.Localization.Projective
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite projective models of cochain complexes

The exact upper tail of a bounded-above complex of finite projective modules
has finite projective cycles. This permits truncation without losing finite
projectivity. Bounded finite projective complexes become finite free on a
single basic neighbourhood of any prime. For comparison with bounded flat
complexes, flatness of the lowest term is detected by a quasi-isomorphism.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits TensorProduct

namespace CochainComplex

variable {baseRing : Type u} [CommRing baseRing]

/-- The cycles in the exact upper tail of a bounded-above finite projective
complex are finite projective, including the first degree before that tail. -/
lemma projective_finite_ker_d_of_exactAt (complex : CochainComplex (ModuleCat.{u} baseRing) ℤ)
    (upperBound : ℤ) [complex.IsStrictlyLE upperBound]
    (finite_projective : ∀ degree,
      Module.Projective baseRing (complex.X degree) ∧ Module.Finite baseRing (complex.X degree))
    {cutoff : ℤ} (exact_tail : ∀ degree, cutoff < degree → complex.ExactAt degree)
    (degree : ℤ) (above_cutoff : cutoff ≤ degree) :
    Module.Projective baseRing (LinearMap.ker (complex.d degree (degree + 1)).hom) ∧
      Module.Finite baseRing (LinearMap.ker (complex.d degree (degree + 1)).hom) := by
  suffices descend : ∀ steps : ℕ, ∀ degree : ℤ, cutoff ≤ degree → upperBound < degree + steps →
      Module.Projective baseRing (LinearMap.ker (complex.d degree (degree + 1)).hom) ∧
        Module.Finite baseRing (LinearMap.ker (complex.d degree (degree + 1)).hom) from
    descend (upperBound + 1 - degree).toNat degree above_cutoff (by omega)
  intro steps
  induction steps with
  | zero =>
    intro degree _ above_bound
    have : Subsingleton (complex.X degree) := ModuleCat.subsingleton_of_isZero
      (complex.isZero_of_isStrictlyLE upperBound degree (by simpa using above_bound))
    exact ⟨inferInstance, inferInstance⟩
  | succ steps induction_hypothesis =>
    intro degree above_cutoff above_bound
    obtain ⟨next_projective, -⟩ := induction_hypothesis (degree + 1) (by omega) (by omega)
    obtain ⟨term_projective, term_finite⟩ := finite_projective degree
    obtain ⟨splitting, splitting_comp⟩ := (complex.dToKer degree).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2 (complex.surjective_dToKer degree (exact_tail _ (by omega))))
    let retraction : complex.X degree →ₗ[baseRing]
        LinearMap.ker (complex.d degree (degree + 1)).hom :=
      (LinearMap.id - splitting ∘ₗ complex.dToKer degree).codRestrict _ fun element ↦ by
        have cancel := congrArg Subtype.val
          (LinearMap.congr_fun splitting_comp (complex.dToKer degree element))
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at cancel
        rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.id_apply,
          LinearMap.comp_apply, ← complex.subtype_comp_dToKer degree, LinearMap.comp_apply,
          LinearMap.comp_apply, Submodule.subtype_apply, Submodule.subtype_apply, cancel, sub_self]
    have retraction_comp : retraction ∘ₗ (LinearMap.ker
        (complex.d degree (degree + 1)).hom).subtype = LinearMap.id := by
      ext ⟨element, in_kernel⟩
      have : complex.dToKer degree element = 0 := Subtype.ext in_kernel
      simp [retraction, this]
    exact ⟨Module.Projective.of_split _ _ retraction_comp,
      Module.Finite.of_surjective retraction fun cycle ↦
        ⟨cycle, LinearMap.congr_fun retraction_comp cycle⟩⟩

/-- Truncation preserves finite projectivity when the new top cycles are finite projective. -/
lemma projective_finite_truncLE_X (complex : CochainComplex (ModuleCat.{u} baseRing) ℤ)
    (cutoff : ℤ) (finite_projective : ∀ degree,
      Module.Projective baseRing (complex.X degree) ∧ Module.Finite baseRing (complex.X degree))
    (cycles_projective : Module.Projective baseRing (LinearMap.ker (complex.d cutoff (cutoff + 1)).hom) ∧
      Module.Finite baseRing (LinearMap.ker (complex.d cutoff (cutoff + 1)).hom))
    (degree : ℤ) : Module.Projective baseRing ((complex.truncLE cutoff).X degree) ∧
      Module.Finite baseRing ((complex.truncLE cutoff).X degree) := by
  rcases lt_trichotomy degree cutoff with below | rfl | above
  · obtain ⟨_, _⟩ := finite_projective degree
    let comparison := (complex.truncLEXIso cutoff degree below).toLinearEquiv
    exact ⟨Module.Projective.of_equiv comparison.symm, Module.Finite.equiv comparison.symm⟩
  · have cycles_projective' : Module.Projective baseRing
        (complex.sc degree).moduleCatLeftHomologyData.K ∧
        Module.Finite baseRing (complex.sc degree).moduleCatLeftHomologyData.K := by
      change Module.Projective baseRing (LinearMap.ker
          (complex.d degree ((ComplexShape.up ℤ).next degree)).hom) ∧
        Module.Finite baseRing (LinearMap.ker
          (complex.d degree ((ComplexShape.up ℤ).next degree)).hom)
      rw [CochainComplex.next]
      exact cycles_projective
    obtain ⟨_, _⟩ := cycles_projective'
    let comparison := (complex.truncLEXIsoCycles degree ≪≫
      (complex.sc degree).moduleCatCyclesIso).toLinearEquiv
    exact ⟨Module.Projective.of_equiv comparison.symm, Module.Finite.equiv comparison.symm⟩
  · have : Subsingleton ((complex.truncLE cutoff).X degree) := ModuleCat.subsingleton_of_isZero
      ((complex.truncLE cutoff).isZero_of_isStrictlyLE cutoff degree above)
    exact ⟨inferInstance, inferInstance⟩

/-- Opcycles of a complex of finitely presented modules are finitely presented. -/
lemma finitePresentation_opcycles (complex : CochainComplex (ModuleCat.{u} baseRing) ℤ)
    (finite_presentation : ∀ degree, Module.FinitePresentation baseRing (complex.X degree))
    (degree : ℤ) : Module.FinitePresentation baseRing (complex.opcycles degree) := by
  let shortComplex := complex.sc degree
  have : Module.FinitePresentation baseRing shortComplex.X₂ := finite_presentation degree
  have : Module.FinitePresentation baseRing shortComplex.X₁ := finite_presentation _
  have : Module.FinitePresentation baseRing (shortComplex.X₂ ⧸ LinearMap.range shortComplex.f.hom) :=
    Module.finitePresentation_of_surjective (LinearMap.range shortComplex.f.hom).mkQ
      (Submodule.mkQ_surjective _) (by
        rw [Submodule.ker_mkQ, LinearMap.range_eq_map]
        exact (Module.Finite.fg_top).map _)
  exact Module.FinitePresentation.of_equiv shortComplex.moduleCatOpcyclesIso.toLinearEquiv.symm

/-- A bounded complex quasi-isomorphic to a bounded flat complex is flat in its
lowest degree if its higher terms are flat. -/
lemma flat_X_of_quasiIso {source target : CochainComplex (ModuleCat.{u} baseRing) ℤ}
    (comparison : source ⟶ target) [QuasiIso comparison] (lowerBound upperBound : ℤ)
    [source.IsStrictlyGE lowerBound] [source.IsStrictlyLE upperBound]
    [target.IsStrictlyGE lowerBound] [target.IsStrictlyLE upperBound]
    (source_flat : ∀ degree, lowerBound < degree → Module.Flat baseRing (source.X degree))
    (target_flat : ∀ degree, Module.Flat baseRing (target.X degree)) :
    Module.Flat baseRing (source.X lowerBound) := by
  let cone := mappingCone comparison
  have cone_exact (degree : ℤ) : cone.ExactAt degree :=
    (mappingCone.quasiIso_iff_acyclic comparison).1 inferInstance degree
  let cone_terms (degree : ℤ) : cone.X degree ≅
      ModuleCat.of baseRing (source.X (degree + 1) × target.X degree) :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod comparison degree (degree + 1) rfl ≪≫
      ModuleCat.biprodIsoProd (source.X (degree + 1)) (target.X degree)
  have cone_flat (degree : ℤ) (above : lowerBound ≤ degree) :
      Module.Flat baseRing (cone.X degree) := by
    have : Module.Flat baseRing (source.X (degree + 1) × target.X degree) :=
      Module.Flat.prod_of_flat _ _ (source_flat (degree + 1) (by omega)) (target_flat degree)
    exact Module.Flat.of_linearEquiv (cone_terms degree).toLinearEquiv
  have cycles_flat : ∀ steps : ℕ, ∀ degree : ℤ, lowerBound ≤ degree → upperBound < degree + steps →
      Module.Flat baseRing (LinearMap.ker (cone.d degree (degree + 1)).hom) := by
    intro steps
    induction steps with
    | zero =>
      intro degree _ above_bound
      have : Subsingleton (cone.X degree) := ModuleCat.subsingleton_of_isZero
        ((mappingCone.isZero_X_iff comparison degree).2
          ⟨source.isZero_of_isStrictlyLE upperBound (degree + 1) (by omega),
            target.isZero_of_isStrictlyLE upperBound degree (by simpa using above_bound)⟩)
      infer_instance
    | succ steps induction_hypothesis =>
      intro degree above above_bound
      have := cone_flat degree above
      exact flat_ker_d_of_flat_ker_d_succ degree (cone_exact _)
        (induction_hypothesis (degree + 1) (by omega) (by omega))
  obtain ⟨offset, rfl⟩ : ∃ offset, lowerBound = offset + 1 + 1 := ⟨lowerBound - 2, by omega⟩
  have lowest_cycles_flat := cycles_flat (upperBound - offset).toNat
    (offset + 1 + 1) le_rfl (by omega)
  have : Subsingleton (cone.X offset) := ModuleCat.subsingleton_of_isZero
    ((mappingCone.isZero_X_iff comparison offset).2
      ⟨source.isZero_of_isStrictlyGE (offset + 1 + 1) (offset + 1) (by omega),
        target.isZero_of_isStrictlyGE (offset + 1 + 1) offset (by omega)⟩)
  have injective_cycles : Function.Injective (cone.dToKer (offset + 1)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro element in_kernel
    obtain ⟨preimage, image_eq⟩ := ((cone.exactAt_iff_exact offset).1 (cone_exact _) element).1
      (congrArg Subtype.val in_kernel)
    rw [← image_eq, Subsingleton.elim preimage 0, map_zero]
  have : Module.Flat baseRing (cone.X (offset + 1)) := Module.Flat.of_linearEquiv
    (LinearEquiv.ofBijective _ ⟨injective_cycles, cone.surjective_dToKer (offset + 1) (cone_exact _)⟩)
  have : Module.Flat baseRing (source.X (offset + 1 + 1) × target.X (offset + 1)) :=
    Module.Flat.of_linearEquiv (cone_terms (offset + 1)).toLinearEquiv.symm
  exact Module.Flat.of_retract
    (LinearMap.inl baseRing (source.X (offset + 1 + 1)) (target.X (offset + 1)))
    (LinearMap.fst baseRing _ _) (by ext; simp)

/-- A bounded finite projective complex becomes termwise finite free after
inverting a single element outside any given prime. -/
theorem exists_free_away_tensor_X (complex : CochainComplex (ModuleCat.{u} baseRing) ℤ)
    (lowerBound upperBound : ℤ) [complex.IsStrictlyGE lowerBound] [complex.IsStrictlyLE upperBound]
    (finite_projective : ∀ degree,
      Module.Projective baseRing (complex.X degree) ∧ Module.Finite baseRing (complex.X degree))
    (prime : Ideal baseRing) [prime.IsPrime] :
    ∃ denominator ∉ prime, ∀ degree,
      Module.Free (Localization.Away denominator)
        (Localization.Away denominator ⊗[baseRing] complex.X degree) ∧
      Module.Finite (Localization.Away denominator)
        (Localization.Away denominator ⊗[baseRing] complex.X degree) := by
  classical
  have locally_free (degree : ℤ) : ∃ denominator ∉ prime,
      Module.Free (Localization.Away denominator)
        (Localization.Away denominator ⊗[baseRing] complex.X degree) := by
    obtain ⟨_, _⟩ := finite_projective degree
    exact Module.exists_free_away_tensor _ prime
  choose denominator not_mem free using locally_free
  refine ⟨∏ degree ∈ Finset.Icc lowerBound upperBound, denominator degree,
    fun in_prime ↦ ?_, fun degree ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨degree, -, in_prime⟩ := Ideal.IsPrime.prod_mem_iff.1 in_prime
    exact not_mem degree in_prime
  · by_cases in_interval : degree ∈ Finset.Icc lowerBound upperBound
    · have := free degree
      exact Module.free_away_tensor_of_dvd _ (Finset.dvd_prod_of_mem denominator in_interval)
    · have term_zero : IsZero (complex.X degree) := by
        have outside : degree < lowerBound ∨ upperBound < degree := by
          simpa only [Finset.mem_Icc, not_and_or, not_le] using in_interval
        rcases outside with below | above
        · exact complex.isZero_of_isStrictlyGE lowerBound degree below
        · exact complex.isZero_of_isStrictlyLE upperBound degree above
      have : Subsingleton (complex.X degree) := ModuleCat.subsingleton_of_isZero term_zero
      infer_instance
  · have := (finite_projective degree).2
    infer_instance

end CochainComplex
