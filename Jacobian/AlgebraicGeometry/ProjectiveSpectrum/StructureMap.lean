import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The structure morphism on homogeneous affine charts

The structure morphism from a projective spectrum to its degree-zero spectrum
induces the canonical inclusion of degree-zero elements on every homogeneous
affine chart.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) {degree : ℕ}

/-- On a homogeneous affine chart, the structure morphism includes degree-zero elements. -/
lemma toSpecZero_appTop_res (hf : f ∈ 𝒜 degree) (degreePositive : 0 < degree) :
    (Scheme.ΓSpecIso (.of (𝒜 0))).inv ≫ (toSpecZero 𝒜).appTop ≫
        (Proj 𝒜).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 f ≤ ⊤)).op =
      CommRingCat.ofHom (fromZeroRingHom 𝒜 _) ≫ awayToSection 𝒜 f := by
  have diagram : (basicOpen 𝒜 f).ι ≫ toSpecZero 𝒜 =
      basicOpenToSpec 𝒜 f ≫ Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _)) := by
    apply (cancel_epi (basicOpenIsoSpec 𝒜 f hf degreePositive).inv).mp
    calc
      (basicOpenIsoSpec 𝒜 f hf degreePositive).inv ≫
          (basicOpen 𝒜 f).ι ≫ toSpecZero 𝒜 =
          awayι 𝒜 f hf degreePositive ≫ toSpecZero 𝒜 := (Category.assoc _ _ _).symm
      _ = Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _)) :=
        awayι_toSpecZero 𝒜 f hf degreePositive
      _ = (basicOpenIsoSpec 𝒜 f hf degreePositive).inv ≫ basicOpenToSpec 𝒜 f ≫
          Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _)) := by
        rw [← basicOpenIsoSpec_hom 𝒜 f hf degreePositive, Iso.inv_hom_id_assoc]
  have restriction : (basicOpen 𝒜 f).ι.appTop ≫ (basicOpen 𝒜 f).topIso.hom =
      (Proj 𝒜).presheaf.map (homOfLE (le_top : basicOpen 𝒜 f ≤ ⊤)).op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
    rfl
  have sectionsDiagram := congrArg (fun morphism : (basicOpen 𝒜 f).toScheme ⟶
      Spec (.of (𝒜 0)) ↦ (Scheme.ΓSpecIso (.of (𝒜 0))).inv ≫ morphism.appTop ≫
        (basicOpen 𝒜 f).topIso.hom) diagram
  simpa only [Scheme.Hom.comp_appTop, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality_assoc, basicOpenToSpec_app_top,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, restriction] using sectionsDiagram

end AlgebraicGeometry.Proj
