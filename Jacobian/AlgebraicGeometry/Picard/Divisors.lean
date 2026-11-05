import Jacobian.AlgebraicGeometry.Hilbert.RelativeDivisor
import Jacobian.AlgebraicGeometry.Picard.Normalized

/-!
# Divisor classes normalized along a section

An effective Cartier divisor determines the class of the dual of its ideal.
Removing the pullback of its restriction to a chosen section gives a normalized
relative Picard class. This construction is compatible with base change, hence
defines the Abel map from each finite flat Hilbert functor of a smooth curve.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits Opposite MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme

variable {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

/-- Normalize a relative Picard class by removing its class along the section. -/
def normalizePicardClass (T : Over S) (L : (pullback f T.hom).Pic) :
    (picardFunctorNormalized f σ hσ).toFunctor.obj (op T) :=
  ⟨L * Pic.map (pullback.snd f T.hom)
      ((Pic.map (sectionBaseChange f σ hσ T) L)⁻¹), by
    change Pic.map (sectionBaseChange f σ hσ T)
      (L * Pic.map (pullback.snd f T.hom)
        ((Pic.map (sectionBaseChange f σ hσ T) L)⁻¹)) = 1
    rw [Pic.map_mul, ← Pic.map_comp, sectionBaseChange_snd, Pic.map_id]
    exact mul_inv_cancel _⟩

/-- Normalization is unchanged by pulling back the parameter scheme. -/
lemma normalizePicardClass_naturality {T T' : Over S} (i : T' ⟶ T)
    (L : (pullback f T.hom).Pic) :
    (picardFunctorNormalized f σ hσ).toFunctor.map i.op
        (normalizePicardClass f σ hσ T L) =
      normalizePicardClass f σ hσ T' (Pic.map (baseChangeMap f i) L) := by
  apply Subtype.ext
  change Pic.map (baseChangeMap f i)
      (L * Pic.map (pullback.snd f T.hom)
        ((Pic.map (sectionBaseChange f σ hσ T) L)⁻¹)) = _
  rw [Pic.map_mul, ← Pic.map_comp, (isPullback_baseChangeMap f i).w, Pic.map_comp]
  congr 1
  change Pic.map (pullback.snd f T'.hom)
      (Pic.mapHom i.left ((Pic.map (sectionBaseChange f σ hσ T) L)⁻¹)) = _
  rw [map_inv, Pic.mapHom_apply, ← Pic.map_comp,
    ← sectionBaseChange_comp_baseChangeMap f σ hσ i, Pic.map_comp]

/-- The line bundle of a divisor, normalized along the section. -/
def normalizedDualIdealSheaf (T : Over S) (D : (pullback f T.hom).IdealSheafData) :
    (pullback f T.hom).Modules :=
  D.toModulesᵛ ⊗ (Modules.pullback (pullback.snd f T.hom)).obj
    ((Modules.pullback (sectionBaseChange f σ hσ T)).obj D.toModulesᵛ)ᵛ

/-- Normalization preserves invertibility of the divisor line bundle. -/
lemma isInvertible_normalizedDualIdealSheaf (T : Over S)
    {D : (pullback f T.hom).IdealSheafData} (hD : D.IsInvertible) :
    (normalizedDualIdealSheaf f σ hσ T D).IsInvertible := by
  letI : D.toModules.IsInvertible := hD.isInvertible_toModules
  dsimp [normalizedDualIdealSheaf]
  infer_instance

/-- The normalized divisor class of a finite flat family on a smooth relative curve. -/
def hilbertToPicardNormalized [SmoothOfRelativeDimension 1 f] (d : ℕ) (T : Over S)
    (D : (hilbertPresheaf f d).obj (op T)) :
    (picardFunctorNormalized f σ hσ).toFunctor.obj (op T) := by
  letI : D.1.toModules.IsInvertible := D.2.isInvertible.isInvertible_toModules
  exact normalizePicardClass f σ hσ T (Pic.mk D.1.toModulesᵛ)

/-- Divisor line-bundle classes commute with change of parameter. -/
lemma hilbertToPicardNormalized_naturality [SmoothOfRelativeDimension 1 f] (d : ℕ)
    {T T' : Over S} (i : T' ⟶ T) (D : (hilbertPresheaf f d).obj (op T)) :
    (picardFunctorNormalized f σ hσ).toFunctor.map i.op
        (hilbertToPicardNormalized f σ hσ d T D) =
      hilbertToPicardNormalized f σ hσ d T' ((hilbertPresheaf f d).map i.op D) := by
  letI : D.1.toModules.IsInvertible := D.2.isInvertible.isInvertible_toModules
  have pulledCartier := (IsHilbertSubscheme.comap i D.2).isInvertible
  letI := pulledCartier.isInvertible_toModules
  obtain ⟨comparison⟩ := D.2.isInvertible.nonempty_pullback_dual_toModules_iso
    (baseChangeMap f i) pulledCartier
  change (picardFunctorNormalized f σ hσ).toFunctor.map i.op
    (normalizePicardClass f σ hσ T (Pic.mk D.1.toModulesᵛ)) =
      normalizePicardClass f σ hσ T' (Pic.mk (D.1.comap (baseChangeMap f i)).toModulesᵛ)
  rw [normalizePicardClass_naturality, Pic.map_mk,
    (Pic.mk_eq_mk_iff _ _).mpr ⟨comparison⟩]

/-- The Abel map from the degree-`d` Hilbert functor to the normalized Picard presheaf. -/
def hilbertToPicardNormalizedNatTrans [SmoothOfRelativeDimension 1 f] (d : ℕ) :
    hilbertPresheaf f d ⋙ uliftFunctor.{u + 1, u} ⟶
      (picardFunctorNormalized f σ hσ).toFunctor where
  app T := TypeCat.ofHom fun D ↦ hilbertToPicardNormalized f σ hσ d T.unop D.down
  naturality T T' i := by
    ext D
    exact (hilbertToPicardNormalized_naturality f σ hσ d i.unop D.down).symm

end AlgebraicGeometry
