import Jacobian.AlgebraicGeometry.Hilbert.Addition
import Jacobian.AlgebraicGeometry.Hilbert.CurveRepresentability
import Jacobian.AlgebraicGeometry.Geometrically.Irreducible

/-!
# Finite flat covers of Hilbert schemes of curves

Iterated addition gives a finite flat surjection from a power of a smooth proper
geometrically integral curve onto each of its finite flat Hilbert schemes.
The covering scheme is smooth of the expected relative dimension, proper and
geometrically irreducible. Consequently, each Hilbert scheme is universally
closed and geometrically irreducible over the ground field.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A morphism locally of finite type over a field is universally open. -/
lemma universallyOpen_of_locallyOfFiniteType_spec_field {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType g] : UniversallyOpen g := by
  have : LocallyOfFinitePresentation g :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  infer_instance

/-- The spectrum of a field is geometrically irreducible over itself. -/
lemma geometricallyIrreducible_id_spec_field : GeometricallyIrreducible (𝟙 (Spec (.of k))) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  rw [(asIso (pullback.snd (𝟙 _) y)).hom.homeomorph.irreducibleSpace_iff]
  infer_instance

/-- Iterated addition gives a finite flat surjection from a smooth proper power of the curve
onto its degree-`d` Hilbert scheme. -/
theorem exists_finite_flat_cover_of_representableBy_hilbertPresheaf_curve
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f]
    (d : ℕ) (H : Over (Spec (.of k))) (e : (hilbertPresheaf f d).RepresentableBy H) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k)) (π : Y ⟶ H.left),
      IsProper q ∧ SmoothOfRelativeDimension d q ∧ GeometricallyIrreducible q ∧
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧ Surjective π ∧ π ≫ H.hom = q := by
  induction d generalizing H with
  | zero =>
    have := isIso_of_representableBy_hilbertPresheaf_zero f e
    exact ⟨Spec (.of k), 𝟙 _, inv H.hom, inferInstance, inferInstance,
      geometricallyIrreducible_id_spec_field, inferInstance, inferInstance,
      inferInstance, inferInstance, by simp⟩
  | succ d ih =>
    obtain ⟨H₀, ⟨e₀⟩⟩ := isRepresentable_hilbertPresheaf_curve f d
    obtain ⟨Y, _, π, hq, hsmooth, hirr, hfinite, hflat, hlfp, hsurjective, rfl⟩ := ih H₀ e₀
    obtain ⟨a, ha, hfin, haflat, halfp, hrank, -⟩ :=
      exists_addition_hilbertPresheaf f d H₀ H e₀ e
    have : Surjective a :=
      (Scheme.Hom.one_le_finrank_iff_surjective a).mp fun t ↦ by simp [hrank t]
    have := universallyOpen_of_locallyOfFiniteType_spec_field f
    have := universallyOpen_of_locallyOfFiniteType_spec_field (π ≫ H₀.hom)
    refine ⟨pullback (π ≫ H₀.hom) f, pullback.fst _ _ ≫ π ≫ H₀.hom,
      (pullbackRightPullbackFstIso H₀.hom f π).inv ≫ pullback.snd _ _ ≫ a,
      inferInstance, ?_, GeometricallyIrreducible.comp _ _,
      inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    · have : SmoothOfRelativeDimension 1 (pullback.fst (π ≫ H₀.hom) f) :=
        (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
          (IsPullback.of_hasPullback (π ≫ H₀.hom) f).flip ‹_›
      have : SmoothOfRelativeDimension (1 + d)
          (pullback.fst (π ≫ H₀.hom) f ≫ (π ≫ H₀.hom)) :=
        smoothOfRelativeDimension_comp (n := 1) (m := d) _ _
      simpa only [Nat.add_comm] using this
    · rw [Category.assoc, Category.assoc, ha,
        pullbackRightPullbackFstIso_inv_snd_snd_assoc, pullback.condition]

/-- Hilbert schemes of smooth proper geometrically integral curves are universally closed
and geometrically irreducible over the ground field. -/
theorem universallyClosed_and_geometricallyIrreducible_of_representableBy_hilbertPresheaf_curve
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f]
    (d : ℕ) (H : Over (Spec (.of k))) (e : (hilbertPresheaf f d).RepresentableBy H) :
    UniversallyClosed H.hom ∧ GeometricallyIrreducible H.hom := by
  obtain ⟨Y, _, π, hq, hsmooth, hirr, hfinite, hflat, hlfp, hsurjective, rfl⟩ :=
    exists_finite_flat_cover_of_representableBy_hilbertPresheaf_curve f d H e
  exact ⟨UniversallyClosed.of_comp_surjective π H.hom,
    GeometricallyIrreducible.of_surjective π H.hom⟩

end AlgebraicGeometry
