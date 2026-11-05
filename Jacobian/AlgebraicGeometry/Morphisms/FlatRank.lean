import Jacobian.AlgebraicGeometry.FiniteOverField.Rank
import Jacobian.AlgebraicGeometry.Morphisms.FiniteRank
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Rank of composites of finite flat morphisms

A finite flat morphism of constant rank multiplies the rank of a subsequent
finite flat morphism. The field case is proved from affine coordinate rings;
the general case follows by residue-field base change.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

/- The rank is unchanged after composing with an isomorphism on the target. -/
lemma finrank_comp_of_isIso_right {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ Y')
    [IsIso e] [IsFinite f] [Flat f] (y : Y) : (f ≫ e).finrank (e y) = f.finrank y := by
  have h : IsPullback (𝟙 X) (f ≫ e) f (inv e) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ h, ← Scheme.Hom.comp_apply,
    IsIso.hom_inv_id]
  rfl

/-- The rank is multiplicative over the spectrum of a field. -/
theorem finrank_comp_of_forall_finrank_eq_of_field {K : Type u} [Field K]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Spec (.of K)) [IsFinite f] [Flat f] [IsFinite g]
    [Flat g] {n : ℕ} (hf : ∀ y, f.finrank y = n) (z : Spec (.of K)) :
    (f ≫ g).finrank z = n * g.finrank z := by
  have : IsAffine Y := isAffine_of_isAffineHom g
  have : IsAffine X := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ g)
  have hfg : f ≫ g = X.isoSpec.hom ≫ Spec.map φ ≫ Spec.map ψ := by simp [hφ, hψ]
  have hφf (y : _) : (Spec.map φ).finrank y = n := by
    have hy : Y.isoSpec.hom (Y.isoSpec.inv y) = y := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    rw [hφ, Scheme.Hom.finrank_comp_left_of_isIso, ← hy,
      Scheme.Hom.finrank_comp_of_isIso_right, hf]
  have hφ₁ : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have hφ₂ : φ.hom.Flat := by
    rw [← Flat.SpecMap_iff, hφ]
    infer_instance
  have hψ₁ : ψ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hψ]
    infer_instance
  have hψ₂ : ψ.hom.Flat := by
    rw [← Flat.SpecMap_iff, hψ]
    infer_instance
  have hφψ₁ : (ψ ≫ φ).hom.Finite := by
    rw [CommRingCat.hom_comp]
    exact hφ₁.comp hψ₁
  have hφψ₂ : (ψ ≫ φ).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact hψ₂.comp hφ₂
  letI : IsFinite (Spec.map φ) := by
    rw [IsFinite.SpecMap_iff]
    exact hφ₁
  letI : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hφ₂
  letI : IsFinite (Spec.map ψ) := by
    rw [IsFinite.SpecMap_iff]
    exact hψ₁
  letI : Flat (Spec.map ψ) := Flat.SpecMap_iff.mpr hψ₂
  rw [hfg, Scheme.Hom.finrank_comp_left_of_isIso,
    ← Scheme.Hom.finrank_comp_left_of_isIso Y.isoSpec.inv g, ← hψ, ← Spec.map_comp,
    Scheme.Hom.finrank_SpecMap_eq_finrank hψ₁ hψ₂,
    Scheme.Hom.finrank_SpecMap_eq_finrank hφψ₁ hφψ₂]
  simp only [Scheme.Hom.finrank_SpecMap_eq_finrank hφ₁ hφ₂] at hφf
  rw [CommRingCat.hom_comp]
  algebraize [ψ.hom, φ.hom, φ.hom.comp ψ.hom]
  rw [← RingHom.algebraMap_toAlgebra (φ.hom.comp ψ.hom),
    ← RingHom.algebraMap_toAlgebra ψ.hom, RingHom.finrank_algebraMap,
    RingHom.finrank_algebraMap, Module.rankAtStalk_eq_finrank_of_free,
    Module.rankAtStalk_eq_finrank_of_free]
  refine Module.finrank_eq_mul_of_rankAtStalk_eq fun q ↦ ?_
  rw [← hφf q, ← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap]

/-- The rank is multiplicative for finite flat morphisms over any base. -/
theorem finrank_comp_of_forall_finrank_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsFinite f] [Flat f] [IsFinite g] [Flat g] {n : ℕ}
    (hf : ∀ y, f.finrank y = n) (z : Z) :
    (f ≫ g).finrank z = n * g.finrank z := by
  let s := Z.fromSpecResidueField z
  let t : Spec (Z.residueField z) := IsLocalRing.closedPoint _
  have hs : s t = z := Z.fromSpecResidueField_apply z t
  have e : pullback.snd (f ≫ g) s = (pullbackRightPullbackFstIso g s f).inv ≫
      pullback.snd f (pullback.fst g s) ≫ pullback.snd g s := by simp
  rw [← hs, ← Scheme.Hom.finrank_pullback_snd (f ≫ g) s,
    ← Scheme.Hom.finrank_pullback_snd g s, e,
    Scheme.Hom.finrank_comp_left_of_isIso]
  exact Scheme.Hom.finrank_comp_of_forall_finrank_eq_of_field (K := Z.residueField z) _ _
    (fun y ↦ by rw [Scheme.Hom.finrank_pullback_snd, hf]) t

end AlgebraicGeometry.Scheme.Hom
