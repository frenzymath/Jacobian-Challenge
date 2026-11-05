import Jacobian.Algebra.Homology.CochainComplex.FlatCycles
import Jacobian.Algebra.Homology.DerivedCategory.Perfect.Triangulated
import Jacobian.Algebra.Homology.MappingCone.Flat
import Jacobian.Algebra.Homology.ShortComplex.Finite
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Perfectness of bounded flat complexes with finite cohomology

Over a Noetherian ring, a bounded complex of flat modules with finite
cohomology is perfect. Finite free generators of its top cohomology lift to
cycles. Their mapping cone has vanishing top cohomology; truncating the cone
lowers the upper bound while retaining flat terms. Induction on the length
of the interval then gives a bounded finite projective representative.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u w

open CategoryTheory Limits

namespace DerivedCategory

variable {baseRing : Type u} [CommRing baseRing] [IsNoetherianRing baseRing]
  [HasDerivedCategory.{w} (ModuleCat.{u} baseRing)]

private lemma isPerfect_Q_obj_of_flat_single
    (complex : CochainComplex (ModuleCat.{u} baseRing) ℤ) (degree : ℤ)
    [complex.IsStrictlyGE degree] [complex.IsStrictlyLE degree]
    (flat : ∀ position, Module.Flat baseRing (complex.X position))
    (finite : Module.Finite baseRing (complex.homology degree)) : (Q.obj complex).IsPerfect := by
  refine isPerfect_Q_obj complex degree degree fun position ↦ ?_
  have := flat position
  have : Module.Finite baseRing (complex.X position) := by
    by_cases at_degree : position = degree
    · subst position
      have := complex.isIso_homologyπ (degree - 1) degree (by simp)
        ((complex.isZero_of_isStrictlyGE degree (degree - 1) (by omega)).eq_of_src _ _)
      have := complex.isIso_iCycles degree (degree + 1) (by simp)
        ((complex.isZero_of_isStrictlyLE degree (degree + 1) (by omega)).eq_of_tgt _ _)
      exact Module.Finite.equiv
        ((asIso (complex.homologyπ degree)).symm ≪≫ asIso (complex.iCycles degree)).toLinearEquiv
    · have : Subsingleton (complex.X position) := ModuleCat.subsingleton_of_isZero (by
        rcases lt_or_gt_of_ne at_degree with below | above
        · exact complex.isZero_of_isStrictlyGE degree position below
        · exact complex.isZero_of_isStrictlyLE degree position above)
      infer_instance
  have := Module.finitePresentation_of_finite baseRing (complex.X position)
  exact ⟨Module.Flat.projective_of_finitePresentation, inferInstance⟩

private lemma exists_lower_flat_model
    (complex : CochainComplex (ModuleCat.{u} baseRing) ℤ) (lowerBound upperBound : ℤ)
    [complex.IsStrictlyGE lowerBound] [complex.IsStrictlyLE upperBound]
    (nontrivial_interval : lowerBound < upperBound)
    (flat : ∀ degree, Module.Flat baseRing (complex.X degree))
    (finite : ∀ degree, Module.Finite baseRing (complex.homology degree)) :
    ∃ (reduced : CochainComplex (ModuleCat.{u} baseRing) ℤ)
      (_ : reduced.IsStrictlyGE lowerBound) (_ : reduced.IsStrictlyLE (upperBound - 1)),
      (∀ degree, Module.Flat baseRing (reduced.X degree)) ∧
      (∀ degree, Module.Finite baseRing (reduced.homology degree)) ∧
      ((Q.obj reduced).IsPerfect → (Q.obj complex).IsPerfect) := by
  have := finite upperBound
  obtain ⟨rank, generators, surjective_generators⟩ :=
    Module.Finite.exists_fin' baseRing (complex.homology upperBound)
  have surjective_projection : Function.Surjective (complex.homologyπ upperBound).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨cycles_lift, lift_eq⟩ := Module.projective_lifting_property
    (complex.homologyπ upperBound).hom generators surjective_projection
  let freeModule := ModuleCat.of baseRing (Fin rank → baseRing)
  let single : CochainComplex (ModuleCat.{u} baseRing) ℤ :=
    (HomologicalComplex.single (ModuleCat.{u} baseRing) (.up ℤ) upperBound).obj freeModule
  let comparison : single ⟶ complex := HomologicalComplex.mkHomFromSingle
    (ModuleCat.ofHom cycles_lift ≫ complex.iCycles upperBound)
    (by rintro degree (rfl : upperBound + 1 = degree); simp)
  let cone := CochainComplex.mappingCone comparison
  let triangle := CochainComplex.mappingCone.triangle comparison
  have distinguished : Q.mapTriangle.obj triangle ∈ distTriang _ :=
    mappingCone_triangle_distinguished comparison
  have single_zero (degree : ℤ) (different : degree ≠ upperBound) : IsZero (single.X degree) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ different
  have single_projective (degree : ℤ) : Module.Projective baseRing (single.X degree) ∧
      Module.Finite baseRing (single.X degree) := by
    by_cases at_top : degree = upperBound
    · subst degree
      let term_comparison := (HomologicalComplex.singleObjXSelf (.up ℤ) upperBound freeModule).toLinearEquiv
      exact ⟨Module.Projective.of_equiv term_comparison.symm,
        Module.Finite.equiv term_comparison.symm⟩
    · have : Subsingleton (single.X degree) := ModuleCat.subsingleton_of_isZero (single_zero degree at_top)
      exact ⟨inferInstance, inferInstance⟩
  have single_perfect : (Q.obj single).IsPerfect :=
    isPerfect_Q_obj single upperBound upperBound single_projective
  have single_flat (degree : ℤ) : Module.Flat baseRing (single.X degree) := by
    have := (single_projective degree).1
    infer_instance
  have cone_flat (degree : ℤ) : Module.Flat baseRing (cone.X degree) :=
    CochainComplex.mappingCone_flat_X comparison single_flat flat degree
  have : cone.IsStrictlyGE lowerBound :=
    CochainComplex.isStrictlyGE_mappingCone comparison upperBound lowerBound lowerBound
  have : cone.IsStrictlyLE upperBound :=
    CochainComplex.mappingCone_isStrictlyLE_of_common_bound comparison upperBound
  have top_surjective : Epi (HomologicalComplex.homologyMap comparison upperBound) := by
    have : IsIso (single.iCycles upperBound) := single.isIso_iCycles upperBound (upperBound + 1)
      (by simp) ((single_zero (upperBound + 1) (by omega)).eq_of_tgt _ _)
    have cycles_map : HomologicalComplex.cyclesMap comparison upperBound = single.iCycles upperBound ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) upperBound freeModule).hom ≫
          ModuleCat.ofHom cycles_lift := by
      rw [← cancel_mono (complex.iCycles upperBound), HomologicalComplex.cyclesMap_i]
      simp [comparison, HomologicalComplex.mkHomFromSingle_f]
    have : Epi (ModuleCat.ofHom cycles_lift ≫ complex.homologyπ upperBound) := by
      rw [ModuleCat.epi_iff_surjective]
      change Function.Surjective ((complex.homologyπ upperBound).hom ∘ₗ cycles_lift)
      rw [lift_eq]
      exact surjective_generators
    have : Epi (single.homologyπ upperBound ≫ HomologicalComplex.homologyMap comparison upperBound) := by
      rw [HomologicalComplex.homologyπ_naturality, cycles_map]
      simp only [Category.assoc]
      infer_instance
    exact epi_of_epi (single.homologyπ upperBound) _
  have top_zero : IsZero (cone.homology upperBound) :=
    (CochainComplex.homologyMap_exact₃_of_distTriang triangle distinguished upperBound
      (upperBound + 1)).isZero_X₂
        ((CochainComplex.homologyMap_exact₂_of_distTriang triangle distinguished upperBound).epi_f_iff.1
          top_surjective)
        (((single.exactAt_of_isLE upperBound (upperBound + 1) (by omega)).isZero_homology).eq_of_tgt _ _)
  have exact_tail (degree : ℤ) (above : upperBound ≤ degree) : cone.ExactAt degree := by
    obtain rfl | above := eq_or_lt_of_le above
    · exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 top_zero
    · exact cone.exactAt_of_isLE upperBound degree above
  have : cone.IsLE (upperBound - 1) := (cone.isLE_iff _).2 fun degree above ↦
    exact_tail degree (by omega)
  have cone_finite (degree : ℤ) : Module.Finite baseRing (cone.homology degree) := by
    have : Module.Finite baseRing (triangle.obj₂.homology degree) := finite degree
    have : Module.Finite baseRing (triangle.obj₁.homology (degree + 1)) := by
      have := single_perfect.finite_homology (degree + 1)
      let homology_comparison :
          (homologyFunctor (ModuleCat.{u} baseRing) (degree + 1)).obj (Q.obj single) ≅
            single.homology (degree + 1) := (homologyFunctorFactors _ (degree + 1)).app single
      exact Module.Finite.equiv homology_comparison.toLinearEquiv
    exact (CochainComplex.homologyMap_exact₃_of_distTriang triangle distinguished degree
      (degree + 1)).moduleFinite_X₂
  have zero_cycles_flat (degree : ℤ) (above : upperBound + 1 ≤ degree) :
      Module.Flat baseRing (LinearMap.ker (cone.d degree (degree + 1)).hom) := by
    have : Subsingleton (cone.X degree) := ModuleCat.subsingleton_of_isZero
      (cone.isZero_of_isStrictlyLE upperBound degree (by omega))
    infer_instance
  have truncation_cycles_flat : Module.Flat baseRing
      (LinearMap.ker (cone.d (upperBound - 1) (upperBound - 1 + 1)).hom) :=
    CochainComplex.flat_ker_d_of_exactAt cone_flat (m := upperBound) (N := upperBound + 1)
      exact_tail zero_cycles_flat (upperBound - 1) le_rfl
  let reduced := cone.truncLE (upperBound - 1)
  have : reduced.IsStrictlyGE lowerBound := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro degree below
    exact (cone.isZero_of_isStrictlyGE lowerBound degree below).of_iso
      (cone.truncLEXIso (upperBound - 1) degree (by omega))
  refine ⟨reduced, inferInstance, inferInstance,
    CochainComplex.flat_truncLE_X cone (upperBound - 1) cone_flat truncation_cycles_flat,
    fun degree ↦ ?_, fun reduced_perfect ↦ ?_⟩
  · have := cone_finite degree
    let homology_comparison : reduced.homology degree ≅ cone.homology degree :=
      asIso (HomologicalComplex.homologyMap (cone.ιTruncLE (upperBound - 1)) degree)
    exact Module.Finite.equiv homology_comparison.toLinearEquiv.symm
  · have cone_perfect : (Q.obj cone).IsPerfect := reduced_perfect.of_iso
      (asIso (Q.map (cone.ιTruncLE (upperBound - 1))))
    exact isPerfect_obj₂_of_distTriang _ distinguished single_perfect cone_perfect

private lemma isPerfect_Q_obj_of_bounded_flat (length : ℕ) :
    ∀ (complex : CochainComplex (ModuleCat.{u} baseRing) ℤ) (lowerBound upperBound : ℤ),
      complex.IsStrictlyGE lowerBound → complex.IsStrictlyLE upperBound →
      (∀ degree, Module.Flat baseRing (complex.X degree)) →
      (∀ degree, Module.Finite baseRing (complex.homology degree)) →
      upperBound - lowerBound ≤ length → (Q.obj complex).IsPerfect := by
  induction length with
  | zero =>
    intro complex lowerBound upperBound lower_bound upper_bound flat finite width
    have := lower_bound
    have := upper_bound
    have : complex.IsStrictlyGE upperBound := complex.isStrictlyGE_of_ge upperBound lowerBound (by omega)
    exact isPerfect_Q_obj_of_flat_single complex upperBound flat (finite _)
  | succ length induction_hypothesis =>
    intro complex lowerBound upperBound lower_bound upper_bound flat finite width
    have := lower_bound
    have := upper_bound
    by_cases empty_interval : upperBound ≤ lowerBound
    · have : complex.IsStrictlyGE upperBound :=
        complex.isStrictlyGE_of_ge upperBound lowerBound empty_interval
      exact isPerfect_Q_obj_of_flat_single complex upperBound flat (finite _)
    · obtain ⟨reduced, lower_bound, upper_bound, reduced_flat, reduced_finite, reconstruct⟩ :=
        exists_lower_flat_model complex lowerBound upperBound (by omega) flat finite
      exact reconstruct (induction_hypothesis reduced lowerBound (upperBound - 1)
        lower_bound upper_bound reduced_flat reduced_finite (by omega))

/-- A bounded flat model with finite cohomology over a Noetherian ring is perfect. -/
theorem isPerfect_of_flat_of_finite_homology
    {object : DerivedCategory (ModuleCat.{u} baseRing)}
    (complex : CochainComplex (ModuleCat.{u} baseRing) ℤ) (lowerBound upperBound : ℤ)
    [complex.IsStrictlyGE lowerBound] [complex.IsStrictlyLE upperBound]
    (flat : ∀ degree, Module.Flat baseRing (complex.X degree)) (model : object ≅ Q.obj complex)
    (finite : ∀ degree,
      Module.Finite baseRing ((homologyFunctor (ModuleCat.{u} baseRing) degree).obj object)) :
    object.IsPerfect := by
  have finite_model (degree : ℤ) : Module.Finite baseRing (complex.homology degree) := by
    have := finite degree
    let homology_comparison :
        (homologyFunctor (ModuleCat.{u} baseRing) degree).obj object ≅ complex.homology degree :=
      (homologyFunctor (ModuleCat.{u} baseRing) degree).mapIso model ≪≫
        (homologyFunctorFactors (ModuleCat.{u} baseRing) degree).app complex
    exact Module.Finite.equiv homology_comparison.toLinearEquiv
  exact (isPerfect_Q_obj_of_bounded_flat (upperBound - lowerBound).toNat complex lowerBound upperBound
    inferInstance inferInstance flat finite_model (by omega)).of_iso model.symm

end DerivedCategory
