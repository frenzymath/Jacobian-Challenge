import Jacobian.Algebra.Homology.CochainComplex.FiniteProjective
import Jacobian.Algebra.Homology.CochainComplex.FlatBaseChange
import Jacobian.Algebra.Homology.DerivedCategory.KProjective
import Jacobian.Algebra.Homology.DerivedCategory.Perfect.Basic
import Jacobian.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Finite free local models of perfect complexes

A bounded flat complex which is perfect has a finite projective model with
the same bounds. Near any prime this model becomes finite free. Localization
uses the native extension-of-scalars functor, and the map to the original
complex remains a quasi-isomorphism.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u w

open CategoryTheory Limits TensorProduct

namespace DerivedCategory

variable {baseRing : Type u} [CommRing baseRing]
  [HasDerivedCategory.{w} (ModuleCat.{u} baseRing)]

/-- A perfect bounded flat complex has a finite projective model with the same bounds. -/
theorem exists_quasiIso_projective_finite_of_isPerfect
    (complex : CochainComplex (ModuleCat.{u} baseRing) ℤ) (lowerBound upperBound : ℤ)
    [complex.IsStrictlyGE lowerBound] [complex.IsStrictlyLE upperBound]
    (flat : ∀ degree, Module.Flat baseRing (complex.X degree))
    (perfect : (Q.obj complex).IsPerfect) :
    ∃ (model : CochainComplex (ModuleCat.{u} baseRing) ℤ)
      (_ : model.IsStrictlyGE lowerBound) (_ : model.IsStrictlyLE upperBound),
      (∀ degree, Module.Projective baseRing (model.X degree) ∧
        Module.Finite baseRing (model.X degree)) ∧
      ∃ comparison : model ⟶ complex, QuasiIso comparison := by
  obtain ⟨initial, _, initialUpperBound, _, _, initial_projective, ⟨derived_comparison⟩⟩ := perfect
  have : ∀ degree, Projective (initial.X degree) := fun degree ↦
    (IsProjective.iff_projective (initial.X degree)).1 (initial_projective degree).1
  obtain ⟨initial_comparison, _⟩ := exists_quasiIso_of_isStrictlyLE_of_projective
    initialUpperBound derived_comparison.symm
  have exact_above (degree : ℤ) (above : upperBound < degree) : initial.ExactAt degree :=
    (exactAt_iff_of_quasiIsoAt initial_comparison degree).2
      (complex.exactAt_of_isLE upperBound degree above)
  have : initial.IsLE upperBound := (initial.isLE_iff upperBound).2 exact_above
  let upperTruncation := initial.truncLE upperBound
  have upper_projective : ∀ degree, Module.Projective baseRing (upperTruncation.X degree) ∧
      Module.Finite baseRing (upperTruncation.X degree) :=
    CochainComplex.projective_finite_truncLE_X initial upperBound initial_projective
      (CochainComplex.projective_finite_ker_d_of_exactAt initial initialUpperBound
        initial_projective exact_above upperBound le_rfl)
  let upper_comparison : upperTruncation ⟶ complex := initial.ιTruncLE upperBound ≫ initial_comparison
  have exact_below (degree : ℤ) (below : degree < lowerBound) : upperTruncation.ExactAt degree :=
    (exactAt_iff_of_quasiIsoAt upper_comparison degree).2
      (complex.exactAt_of_isGE lowerBound degree below)
  have : upperTruncation.IsGE lowerBound := (upperTruncation.isGE_iff lowerBound).2 exact_below
  let model := upperTruncation.truncGE lowerBound
  have : QuasiIso (CochainComplex.truncGEMap upper_comparison lowerBound) :=
    (CochainComplex.quasiIso_truncGEMap_iff _ _).2 fun degree _ ↦ inferInstance
  let comparison : model ⟶ complex :=
    CochainComplex.truncGEMap upper_comparison lowerBound ≫ inv (complex.πTruncGE lowerBound)
  have : model.IsStrictlyLE upperBound := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro degree above
    rcases lt_trichotomy degree lowerBound with below | rfl | above_lower
    · exact model.isZero_of_isStrictlyGE lowerBound degree below
    · exact (IsZero.of_epi (upperTruncation.pOpcycles degree)
        (upperTruncation.isZero_of_isStrictlyLE upperBound degree above)).of_iso
          (upperTruncation.truncGEXIsoOpcycles degree)
    · exact (upperTruncation.isZero_of_isStrictlyLE upperBound degree above).of_iso
        (upperTruncation.truncGEXIso lowerBound degree above_lower)
  have projective_above (degree : ℤ) (above : lowerBound < degree) :
      Module.Projective baseRing (model.X degree) ∧ Module.Finite baseRing (model.X degree) := by
    obtain ⟨_, _⟩ := upper_projective degree
    let term_comparison := (upperTruncation.truncGEXIso lowerBound degree above).toLinearEquiv
    exact ⟨Module.Projective.of_equiv term_comparison.symm,
      Module.Finite.equiv term_comparison.symm⟩
  have projective_lowest : Module.Projective baseRing (model.X lowerBound) ∧
      Module.Finite baseRing (model.X lowerBound) := by
    have : Module.Flat baseRing (model.X lowerBound) :=
      CochainComplex.flat_X_of_quasiIso comparison lowerBound upperBound
        (fun degree above ↦ have := (projective_above degree above).1; inferInstance) flat
    have : Module.FinitePresentation baseRing (upperTruncation.opcycles lowerBound) :=
      CochainComplex.finitePresentation_opcycles upperTruncation (fun degree ↦ by
        obtain ⟨_, _⟩ := upper_projective degree
        exact Module.finitePresentation_of_projective _ _) lowerBound
    have : Module.FinitePresentation baseRing (model.X lowerBound) :=
      Module.FinitePresentation.of_equiv
        (upperTruncation.truncGEXIsoOpcycles lowerBound).toLinearEquiv.symm
    exact ⟨Module.Flat.projective_of_finitePresentation, inferInstance⟩
  refine ⟨model, inferInstance, inferInstance, fun degree ↦ ?_, comparison, inferInstance⟩
  rcases lt_trichotomy degree lowerBound with below | rfl | above
  · have : Subsingleton (model.X degree) := ModuleCat.subsingleton_of_isZero
      (model.isZero_of_isStrictlyGE lowerBound degree below)
    exact ⟨inferInstance, inferInstance⟩
  · exact projective_lowest
  · exact projective_above degree above

/-- Near any prime a perfect bounded flat complex has a finite free model with
the same bounds and a quasi-isomorphism to its native extension of scalars. -/
theorem exists_quasiIso_free_away_of_isPerfect
    (complex : CochainComplex (ModuleCat.{u} baseRing) ℤ) (lowerBound upperBound : ℤ)
    [complex.IsStrictlyGE lowerBound] [complex.IsStrictlyLE upperBound]
    (flat : ∀ degree, Module.Flat baseRing (complex.X degree))
    (perfect : (Q.obj complex).IsPerfect) (prime : Ideal baseRing) [prime.IsPrime] :
    ∃ denominator ∉ prime,
      ∃ (model : CochainComplex (ModuleCat.{u} (Localization.Away denominator)) ℤ)
        (_ : model.IsStrictlyGE lowerBound) (_ : model.IsStrictlyLE upperBound),
        (∀ degree, Module.Free (Localization.Away denominator) (model.X degree) ∧
          Module.Finite (Localization.Away denominator) (model.X degree)) ∧
        ∃ comparison : model ⟶ ((ModuleCat.extendScalars
          (algebraMap baseRing (Localization.Away denominator))).mapHomologicalComplex _).obj complex,
          QuasiIso comparison := by
  obtain ⟨model, _, _, finite_projective, comparison, quasi_iso⟩ :=
    exists_quasiIso_projective_finite_of_isPerfect complex lowerBound upperBound flat perfect
  obtain ⟨denominator, not_mem, locally_free⟩ :=
    CochainComplex.exists_free_away_tensor_X model lowerBound upperBound finite_projective prime
  let extension := ModuleCat.extendScalars (algebraMap baseRing (Localization.Away denominator))
  let extension_complex := extension.mapHomologicalComplex (ComplexShape.up ℤ)
  have model_flat (degree : ℤ) : Module.Flat baseRing (model.X degree) := by
    have := (finite_projective degree).1
    infer_instance
  have : CochainComplex.IsStrictlyGE (extension_complex.obj model) lowerBound :=
    (CochainComplex.isStrictlyGE_iff _ lowerBound).2 fun degree below ↦
      extension.map_isZero (model.isZero_of_isStrictlyGE lowerBound degree below)
  have : CochainComplex.IsStrictlyLE (extension_complex.obj model) upperBound :=
    (CochainComplex.isStrictlyLE_iff _ upperBound).2 fun degree above ↦
      extension.map_isZero (model.isZero_of_isStrictlyLE upperBound degree above)
  refine ⟨denominator, not_mem, extension_complex.obj model, inferInstance, inferInstance,
    fun degree ↦ ?_, extension_complex.map comparison, ?_⟩
  · obtain ⟨_, _⟩ := locally_free degree
    let term_comparison : Localization.Away denominator ⊗[baseRing] model.X degree ≃ₗ[
        Localization.Away denominator] (extension_complex.obj model).X degree :=
      ModuleCat.tensorEquivExtendScalars baseRing (Localization.Away denominator) (model.X degree)
    exact ⟨Module.Free.of_equiv term_comparison, Module.Finite.equiv term_comparison⟩
  · exact CochainComplex.quasiIso_extendScalars_of_boundedAbove_flat comparison upperBound
      model_flat flat quasi_iso (algebraMap baseRing (Localization.Away denominator))

end DerivedCategory
