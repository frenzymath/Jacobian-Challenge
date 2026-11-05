import Jacobian.AlgebraicGeometry.Picard.Presheaf
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# The Hilbert functor of finite flat subschemes

The degree-`rank` Hilbert functor assigns closed subschemes whose projection is
finite, flat and locally of finite presentation, with constant rank `rank`.
Pullback of ideal sheaves makes this assignment functorial.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A finite flat closed subscheme of constant degree over the test scheme. -/
def IsHilbertSubscheme (f : X ⟶ S) (d : ℕ) (T : Over S)
    (I : (Limits.pullback f T.hom).IdealSheafData) : Prop :=
  IsFinite (I.subschemeι ≫ Limits.pullback.snd f T.hom) ∧
    Flat (I.subschemeι ≫ Limits.pullback.snd f T.hom) ∧
      LocallyOfFinitePresentation (I.subschemeι ≫ Limits.pullback.snd f T.hom) ∧
        ∀ t, (I.subschemeι ≫ Limits.pullback.snd f T.hom).finrank t = d

/-- The defining condition of the Hilbert functor is stable under base change along a morphism
`φ : T' ⟶ T` of `S`-schemes.

Finiteness, flatness and local finite presentation are stable under base change, and so is the
rank `AlgebraicGeometry.Scheme.Hom.finrank`, since the closed subscheme cut out by the pullback
ideal sheaf is the base change of the one cut out by `I`. This makes `T ↦ Hilb^d_{X/S}(T)` a
contravariant functor by base change of closed subschemes. -/
theorem IsHilbertSubscheme.comap {f : X ⟶ S} {d : ℕ} {T T' : Over S} (φ : T' ⟶ T)
    {I : (Limits.pullback f T.hom).IdealSheafData} (hI : IsHilbertSubscheme f d T I) :
    IsHilbertSubscheme f d T' (I.comap (baseChangeMap f φ)) := by
  have hsq : IsPullback ((I.comapIso (baseChangeMap f φ)).hom ≫ pullback.snd _ _)
      ((I.comap (baseChangeMap f φ)).subschemeι ≫ pullback.snd f T'.hom)
      (I.subschemeι ≫ pullback.snd f T.hom) φ.left :=
    ((IsPullback.of_hasPullback (baseChangeMap f φ) I.subschemeι).flip.paste_vert
      (isPullback_baseChangeMap f φ)).of_iso' (I.comapIso _) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hI
  refine ⟨MorphismProperty.of_isPullback hsq h₁, MorphismProperty.of_isPullback hsq h₂,
    MorphismProperty.of_isPullback hsq h₃, fun t ↦ ?_⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq]
  exact h₄ _



/-- The Hilbert presheaf, with pullback of ideal sheaves as its restriction maps. -/
noncomputable def hilbertPresheaf (f : X ⟶ S) (d : ℕ) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := { I : (Limits.pullback f T.unop.hom).IdealSheafData // IsHilbertSubscheme f d T.unop I }
  map φ := TypeCat.ofHom fun I ↦ ⟨I.1.comap (baseChangeMap f φ.unop),
    IsHilbertSubscheme.comap φ.unop I.2⟩
  map_id T := congrArg TypeCat.ofHom (funext fun I ↦ Subtype.ext (by
    simp [baseChangeMap_id, Scheme.IdealSheafData.comap_id]))
  map_comp φ ψ := congrArg TypeCat.ofHom (funext fun I ↦ Subtype.ext (by
    simp only [unop_comp, baseChangeMap_comp, Scheme.IdealSheafData.comap_comp]
    rfl))

/-- Restriction in the Hilbert presheaf pulls back the defining ideal sheaf. -/
lemma hilbertPresheaf_map_val (f : X ⟶ S) {degree : ℕ} {test smallerTest : Over S}
    (restriction : smallerTest ⟶ test) (family : (hilbertPresheaf f degree).obj (op test)) :
    ((hilbertPresheaf f degree).map restriction.op family).1 =
      family.1.comap (baseChangeMap f restriction) :=
  rfl

/-- The family classified by a composite is the pullback of the classified family. -/
lemma hilbertPresheaf_homEquiv_comp_val (f : X ⟶ S) {degree : ℕ} {representative : Over S}
    (representation : (hilbertPresheaf f degree).RepresentableBy representative)
    {test smallerTest : Over S} (restriction : smallerTest ⟶ test)
    (classifyingMap : test ⟶ representative) :
    (representation.homEquiv (restriction ≫ classifyingMap)).1 =
      (representation.homEquiv classifyingMap).1.comap (baseChangeMap f restriction) := by
  rw [representation.homEquiv_comp]
  rfl

end AlgebraicGeometry
