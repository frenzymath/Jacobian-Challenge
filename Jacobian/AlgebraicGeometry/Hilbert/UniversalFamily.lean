import Jacobian.AlgebraicGeometry.Hilbert.Basic

/-!
# The universal finite flat family

A representation of the degree-`degree` Hilbert functor supplies a universal
closed subscheme, finite and flat of that degree over the representing scheme.
Every family is its pullback along a unique classifying morphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Hilbert

variable {X S : Scheme.{u}} (f : X ⟶ S) {degree : ℕ} {representative : Over S}
    (representation : (hilbertPresheaf f degree).RepresentableBy representative)

/-- The ideal sheaf of the universal closed subscheme. -/
def universalIdeal : (pullback f representative.hom).IdealSheafData :=
  (representation.homEquiv (𝟙 representative)).1

/-- The universal family satisfies the defining Hilbert condition. -/
lemma isHilbertSubscheme_universalIdeal :
    IsHilbertSubscheme f degree representative (universalIdeal f representation) :=
  (representation.homEquiv (𝟙 representative)).2

/-- The structure morphism of the universal family. -/
def universalProjection : (universalIdeal f representation).subscheme ⟶ representative.left :=
  (universalIdeal f representation).subschemeι ≫ pullback.snd f representative.hom

instance : IsFinite (universalProjection f representation) :=
  (isHilbertSubscheme_universalIdeal f representation).1

instance : Flat (universalProjection f representation) :=
  (isHilbertSubscheme_universalIdeal f representation).2.1

instance : LocallyOfFinitePresentation (universalProjection f representation) :=
  (isHilbertSubscheme_universalIdeal f representation).2.2.1

/-- The degree of the universal family is constant. -/
lemma universalProjection_finrank (point : representative.left) :
    (universalProjection f representation).finrank point = degree :=
  (isHilbertSubscheme_universalIdeal f representation).2.2.2 point

/-- Pullback of the universal ideal gives the family classified by a morphism. -/
@[simp]
lemma universalIdeal_comap {test : Over S} (classifyingMap : test ⟶ representative) :
    (universalIdeal f representation).comap (baseChangeMap f classifyingMap) =
      (representation.homEquiv classifyingMap).1 := by
  simpa [universalIdeal] using
    (hilbertPresheaf_homEquiv_comp_val f representation classifyingMap (𝟙 representative)).symm

/-- The subscheme of a classified family is the pullback of the universal subscheme. -/
def familyIso {test : Over S} (classifyingMap : test ⟶ representative) :
    (representation.homEquiv classifyingMap).1.subscheme ≅
      pullback (baseChangeMap f classifyingMap) (universalIdeal f representation).subschemeι :=
  eqToIso (congrArg (fun ideal : (pullback f test.hom).IdealSheafData ↦ ideal.subscheme)
    (universalIdeal_comap f representation classifyingMap).symm) ≪≫
      (universalIdeal f representation).comapIso (baseChangeMap f classifyingMap)

/-- Changing the parameter scheme gives a cartesian square of universal families. -/
lemma isPullback_universalFamily {test : Over S} (classifyingMap : test ⟶ representative) :
    IsPullback
      (((universalIdeal f representation).comapIso (baseChangeMap f classifyingMap)).hom ≫
        pullback.snd _ _)
      (((universalIdeal f representation).comap (baseChangeMap f classifyingMap)).subschemeι ≫
        pullback.snd f test.hom)
      (universalProjection f representation) classifyingMap.left := by
  unfold universalProjection
  exact ((IsPullback.of_hasPullback (baseChangeMap f classifyingMap)
    (universalIdeal f representation).subschemeι).flip.paste_vert
      (isPullback_baseChangeMap f classifyingMap)).of_iso'
        ((universalIdeal f representation).comapIso _) (Iso.refl _) (Iso.refl _)
          (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

/-- Every finite flat closed subscheme is pulled back from the universal one uniquely. -/
theorem existsUnique_classifyingMap {test : Over S}
    (family : (hilbertPresheaf f degree).obj (op test)) :
    ∃! classifyingMap : test ⟶ representative,
      (universalIdeal f representation).comap (baseChangeMap f classifyingMap) = family.1 := by
  refine ⟨representation.homEquiv.symm family, ?_, ?_⟩
  · simp
  · intro classifyingMap equality
    apply representation.homEquiv.injective
    apply Subtype.ext
    simpa using equality

end AlgebraicGeometry.Hilbert
