import Jacobian.AlgebraicGeometry.Hilbert.CurveRepresentability
import Jacobian.AlgebraicGeometry.Hilbert.CurveCover
import Jacobian.AlgebraicGeometry.Hilbert.Points
import Jacobian.AlgebraicGeometry.Geometrically.Smooth
import Jacobian.AlgebraicGeometry.Morphisms.SmoothSourceDescent
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Geometry of Hilbert schemes of smooth curves

The degree-`d` Hilbert scheme of a smooth relative curve is smooth of relative
dimension `d`. Over a field, properness and geometric integrality of the curve
pass to every Hilbert scheme. Smoothness descends along the finite flat addition
maps; universal closedness and irreducibility follow from the curve-power covers.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A representing scheme for the degree-`d` Hilbert functor of a smooth relative curve is
smooth of relative dimension `d`, provided these Hilbert functors are representable. -/
theorem smoothOfRelativeDimension_of_representableBy_hilbertPresheaf [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] (hrep : ∀ degree, (hilbertPresheaf f degree).IsRepresentable)
    (d : ℕ) (H : Over S) (e : (hilbertPresheaf f d).RepresentableBy H) :
    SmoothOfRelativeDimension d H.hom := by
  induction d generalizing H with
  | zero =>
    have := isIso_of_representableBy_hilbertPresheaf_zero f e
    infer_instance
  | succ d ih =>
    obtain ⟨H₀, ⟨e₀⟩⟩ := hrep d
    have := ih H₀ e₀
    obtain ⟨a, ha, hfin, hflat, hlfp, hrank, -⟩ := exists_addition_hilbertPresheaf f d H₀ H e₀ e
    have : Surjective a :=
      (Scheme.Hom.one_le_finrank_iff_surjective a).mp fun point ↦ by simp [hrank point]
    have : SmoothOfRelativeDimension (d + 1) (a ≫ H.hom) := by
      rw [ha, ← pullback.condition]
      have : SmoothOfRelativeDimension 1 (pullback.fst H₀.hom f) :=
        (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
          (IsPullback.of_hasPullback H₀.hom f).flip ‹_›
      have := smoothOfRelativeDimension_comp (n := 1) (m := d)
        (pullback.fst H₀.hom f) H₀.hom
      simpa only [Nat.add_comm] using this
    exact smoothOfRelativeDimension_of_comp_of_isFinite_of_surjective a H.hom (d + 1)

/-- A degree-zero Hilbert scheme is smooth of relative dimension zero over the base. -/
theorem smoothOfRelativeDimension_of_representableBy_hilbertPresheaf_zero
    {representative : Over S}
    (representation : (hilbertPresheaf f 0).RepresentableBy representative) :
    SmoothOfRelativeDimension 0 representative.hom := by
  have := isIso_of_representableBy_hilbertPresheaf_zero f representation
  infer_instance

/-- A degree-one Hilbert scheme has the same relative smooth dimension as the source. -/
theorem smoothOfRelativeDimension_of_representableBy_hilbertPresheaf_one
    [IsSeparated f] {dimension : ℕ} [SmoothOfRelativeDimension dimension f]
    {representative : Over S}
    (representation : (hilbertPresheaf f 1).RepresentableBy representative) :
    SmoothOfRelativeDimension dimension representative.hom := by
  let representativeIso := hilbertPresheafOneIso f representation
  have : IsIso representativeIso.hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map representativeIso.hom))
  rw [← Over.w representativeIso.hom]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := (@SmoothOfRelativeDimension dimension : MorphismProperty Scheme.{u}))
    representativeIso.hom.left f).mpr inferInstance

/-- A degree-one Hilbert scheme is proper when its source is proper. -/
theorem isProper_of_representableBy_hilbertPresheaf_one [IsProper f]
    {representative : Over S}
    (representation : (hilbertPresheaf f 1).RepresentableBy representative) :
    IsProper representative.hom := by
  let representativeIso := hilbertPresheafOneIso f representation
  have : IsIso representativeIso.hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map representativeIso.hom))
  rw [← Over.w representativeIso.hom]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := (@IsProper : MorphismProperty Scheme.{u}))
    representativeIso.hom.left f).mpr inferInstance

/-- Geometric integrality of the source passes to its degree-one Hilbert scheme. -/
theorem geometricallyIntegral_of_representableBy_hilbertPresheaf_one
    [IsSeparated f] [GeometricallyIntegral f] {representative : Over S}
    (representation : (hilbertPresheaf f 1).RepresentableBy representative) :
    GeometricallyIntegral representative.hom := by
  let representativeIso := hilbertPresheafOneIso f representation
  have : IsIso representativeIso.hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map representativeIso.hom))
  rw [← Over.w representativeIso.hom]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := (@GeometricallyIntegral : MorphismProperty Scheme.{u}))
    representativeIso.hom.left f).mpr inferInstance

section Curve

variable {baseField : Type u} [Field baseField] {curve : Scheme.{u}}
  (structureMap : curve ⟶ Spec (.of baseField))

/-- Every Hilbert scheme of a smooth proper geometrically integral curve is proper and
geometrically integral. -/
theorem isProper_and_geometricallyIntegral_of_representableBy_hilbertPresheaf_curve
    [SmoothOfRelativeDimension 1 structureMap] [IsProper structureMap]
    [GeometricallyIntegral structureMap] (degree : ℕ) (representative : Over (Spec (.of baseField)))
    (representation : (hilbertPresheaf structureMap degree).RepresentableBy representative) :
    IsProper representative.hom ∧ GeometricallyIntegral representative.hom := by
  have := isSeparated_of_representableBy_hilbertPresheaf structureMap representation
  have := smoothOfRelativeDimension_of_representableBy_hilbertPresheaf structureMap
    (isRepresentable_hilbertPresheaf_curve structureMap) degree representative representation
  have := SmoothOfRelativeDimension.smooth degree representative.hom
  obtain ⟨closed, irreducible⟩ :=
    universallyClosed_and_geometricallyIrreducible_of_representableBy_hilbertPresheaf_curve
      structureMap degree representative representation
  letI : UniversallyClosed representative.hom := closed
  letI : GeometricallyIrreducible representative.hom := irreducible
  exact ⟨{}, inferInstance⟩

/-- The degree-`d` Hilbert functor of a smooth proper geometrically integral curve is represented
by a smooth proper geometrically integral scheme of relative dimension `d`. -/
theorem hilbertPresheaf_curve_representable [SmoothOfRelativeDimension 1 structureMap]
    [IsProper structureMap] [GeometricallyIntegral structureMap] (degree : ℕ) :
    ∃ (representative : Scheme.{u}) (projection : representative ⟶ Spec (.of baseField)),
      SmoothOfRelativeDimension degree projection ∧ IsProper projection ∧
      GeometricallyIntegral projection ∧
      Nonempty ((hilbertPresheaf structureMap degree).RepresentableBy (Over.mk projection)) := by
  obtain ⟨representative, ⟨representation⟩⟩ := isRepresentable_hilbertPresheaf_curve structureMap degree
  obtain ⟨proper, integral⟩ :=
    isProper_and_geometricallyIntegral_of_representableBy_hilbertPresheaf_curve
      structureMap degree representative representation
  exact ⟨representative.left, representative.hom,
    smoothOfRelativeDimension_of_representableBy_hilbertPresheaf structureMap
      (isRepresentable_hilbertPresheaf_curve structureMap) degree representative representation,
    proper, integral, ⟨representation⟩⟩

end Curve

end AlgebraicGeometry
