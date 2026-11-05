import Jacobian.AlgebraicGeometry.Hilbert.Basic
import Jacobian.AlgebraicGeometry.IdealSheaf.Affine

/-!
# The Hilbert condition on affine schemes

For affine test schemes and affine ambient pullbacks, finite flat subschemes
of fixed degree correspond to finite flat quotient algebras of that rank.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- Composing a finite flat morphism with an isomorphism preserves its rank. -/
lemma Scheme.Hom.finrank_comp_isIso_apply {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g]
    [Flat f] [IsFinite f] (y : Y) :
    (f ≫ g).finrank (g y) = f.finrank y :=
  (finrank_of_isPullback (𝟙 X) f (f ≫ g) g (IsPullback.of_horiz_isIso (by simp)) y).symm

/-- The rank of a finite flat morphism of affine schemes `f : X ⟶ Y` at `y` is the rank of the
ring map `Γ(Y) ⟶ Γ(X)` at the prime corresponding to `y`. -/
lemma Scheme.Hom.finrank_eq_finrank_appTop {Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [Flat f] [IsFinite f] (y : Y) :
    f.finrank y = f.appTop.hom.finrank (Y.isoSpec.hom y) := by
  have : Flat (Spec.map f.appTop) := Flat.SpecMap_iff.mpr f.flat_appTop
  have : IsFinite (Spec.map f.appTop) := (IsFinite.SpecMap_iff _).mpr f.finite_appTop
  rw [← finrank_comp_isIso_apply f Y.isoSpec.hom, ← Scheme.isoSpec_hom_naturality,
    finrank_comp_left_of_isIso, finrank_SpecMap_eq_finrank f.finite_appTop f.flat_appTop]

/-- **The Hilbert condition over an affine base.** If `T` and `X ×[S] T` are affine, an ideal
sheaf `I` on `X ×[S] T` is a point of `Hilb^d_{X/S}(T)` if and only if the ring map
`Γ(T) ⟶ Γ(X ×[S] T) ⧸ I(⊤)` is finite, flat, of finite presentation and of rank `d` at every
prime. -/
theorem isHilbertSubscheme_iff_of_isAffine (f : X ⟶ S) (d : ℕ) (T : Over S) [IsAffine T.left]
    [IsAffine (pullback f T.hom)] (I : (pullback f T.hom).IdealSheafData) :
    IsHilbertSubscheme f d T I ↔
      ((Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top _⟩)).comp
          (pullback.snd f T.hom).appTop.hom).Finite ∧
        ((Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top _⟩)).comp
          (pullback.snd f T.hom).appTop.hom).Flat ∧
        ((Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top _⟩)).comp
          (pullback.snd f T.hom).appTop.hom).FinitePresentation ∧
        ∀ p, ((Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top _⟩)).comp
          (pullback.snd f T.hom).appTop.hom).finrank p = d := by
  set ψ := (Ideal.Quotient.mk (I.ideal ⟨⊤, isAffineOpen_top _⟩)).comp
    (pullback.snd f T.hom).appTop.hom
  have hZ : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have hp : (I.subschemeι ≫ pullback.snd f T.hom).appTop.hom =
      (I.subschemeObjIso ⟨⊤, isAffineOpen_top _⟩).inv.hom.comp ψ := by
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    rw [Scheme.Hom.appTop, I.subschemeι_app ⟨⊤, isAffineOpen_top _⟩]
    rfl
  have hfin : IsFinite (I.subschemeι ≫ pullback.snd f T.hom) ↔ ψ.Finite := by
    rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite), and_iff_right hZ, hp]
    exact RingHom.finite_respectsIso.cancel_right_isIso (CommRingCat.ofHom ψ) _
  have hflat : Flat (I.subschemeι ≫ pullback.snd f T.hom) ↔ ψ.Flat := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Flat), hp]
    exact RingHom.Flat.respectsIso.cancel_right_isIso (CommRingCat.ofHom ψ) _
  have hfp : LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd f T.hom) ↔
      ψ.FinitePresentation := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation), hp]
    exact RingHom.finitePresentation_respectsIso.cancel_right_isIso (CommRingCat.ofHom ψ) _
  rw [IsHilbertSubscheme, hfin, hflat, hfp]
  refine and_congr_right fun h₁ ↦ and_congr_right fun h₂ ↦ and_congr_right fun _ ↦ ?_
  have := hfin.2 h₁
  have := hflat.2 h₂
  have hrank (t : T.left) : (I.subschemeι ≫ pullback.snd f T.hom).finrank t =
      ψ.finrank (T.left.isoSpec.hom t) := by
    rw [Scheme.Hom.finrank_eq_finrank_appTop, hp, RingHom.finrank_comp_left_of_bijective _ _
      (ConcreteCategory.bijective_of_isIso (I.subschemeObjIso _).inv) h₁ h₂]
  refine (forall_congr' fun t ↦ by rw [hrank]).trans ?_
  exact ((Scheme.homeoOfIso T.left.isoSpec).surjective.forall
    (p := fun P : PrimeSpectrum Γ(T.left, ⊤) ↦ ψ.finrank P = d)).symm

end AlgebraicGeometry
