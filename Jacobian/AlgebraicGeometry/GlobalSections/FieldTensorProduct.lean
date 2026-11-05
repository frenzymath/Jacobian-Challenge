import Jacobian.Algebra.Category.Ring.Pushout
import Jacobian.AlgebraicGeometry.GlobalSections.FlatBaseChange
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Sections after extending the base field

On the inverse image of an affine open, sections of a field base change are the tensor
product of the original sections with the base algebra. The comparison identifies both factors.
-/

set_option backward.isDefEq.respectTransparency false

section
universe schemeUniverse

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

/-- **Sections of a base change over the preimage of an affine open.** Let `X` be a scheme over a
field `k`, `R` a `k`-algebra and `W ⊆ X` an affine open. Then the ring of sections of
`X ×_k Spec R` over the preimage `π⁻¹ W` of `W` under the first projection is
`Γ(X, W) ⊗_k R`, via `a ⊗ r ↦ π^♯ a · pr^♯ r` (flat base change,
`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`). Here `Γ(X, W)` is a
`k`-algebra via the structure morphism. -/
theorem exists_ringEquiv_tensor_app_preimage_fst {baseField baseAlgebra : Type schemeUniverse} [Field baseField] [CommRing baseAlgebra]
    [Algebra baseField baseAlgebra] {scheme : Scheme.{schemeUniverse}} (sX : scheme ⟶ Spec (.of baseField)) {openSubset : scheme.Opens} (hW : IsAffineOpen openSubset) :
    letI : Algebra baseField Γ(scheme, openSubset) :=
      ((sX.appLE ⊤ openSubset le_top).hom.comp (Scheme.ΓSpecIso (.of baseField)).inv.hom).toAlgebra
    ∃ sectionEquiv : Γ(scheme, openSubset) ⊗[baseField] baseAlgebra ≃+* Γ(pullback sX (Spec.map (CommRingCat.ofHom (algebraMap baseField baseAlgebra))),
        pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap baseField baseAlgebra))) ⁻¹ᵁ openSubset),
      (∀ coefficient, sectionEquiv (coefficient ⊗ₜ 1) =
        (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap baseField baseAlgebra)))).app openSubset coefficient) ∧
      ∀ scalar, sectionEquiv (1 ⊗ₜ scalar) = (pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap baseField baseAlgebra)))).appLE ⊤
        _ le_top ((Scheme.ΓSpecIso (.of baseAlgebra)).inv scalar) := by
  let : Algebra baseField Γ(scheme, openSubset) :=
    ((sX.appLE ⊤ openSubset le_top).hom.comp (Scheme.ΓSpecIso (.of baseField)).inv.hom).toAlgebra
  set sU := Spec.map (CommRingCat.ofHom (algebraMap baseField baseAlgebra))
  have : Flat sU := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    infer_instance
  have hUY :
      pullback.fst sX sU ⁻¹ᵁ openSubset = pullback.fst sX sU ⁻¹ᵁ openSubset ⊓ pullback.snd sX sU ⁻¹ᵁ ⊤ := by
    simp
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback sX sU) (US := ⊤) (UT := ⊤) (UX := openSubset) le_top le_top hUY
    (isAffineOpen_top _) (isAffineOpen_top _) hW.isCompact hW.isQuasiSeparated
  have hpush := ((isIso_pushoutSection_iff _ _ _ _).mp hiso).flip
  have pushoutComparison := hpush.of_iso (Scheme.ΓSpecIso (.of baseField)) (Scheme.ΓSpecIso (.of baseAlgebra)) (Iso.refl _)
    (Iso.refl _) (f' := CommRingCat.ofHom (algebraMap baseField baseAlgebra))
    (g' := CommRingCat.ofHom (algebraMap baseField Γ(scheme, openSubset)))
    (inl' := (Scheme.ΓSpecIso (.of baseAlgebra)).inv ≫ (pullback.snd sX sU).appLE ⊤ _ le_top)
    (inr' := (pullback.fst sX sU).appLE openSubset _ le_rfl) ?_ ?_ ?_ ?_
  · refine ⟨pushoutComparison.tensorEquiv rfl rfl, fun coefficient ↦ ?_, fun scalar ↦ ?_⟩
    · rw [pushoutComparison.tensorEquiv_tmul, map_one, mul_one, Scheme.Hom.app_eq_appLE]
    · rw [pushoutComparison.tensorEquiv_tmul, map_one, one_mul]
      rfl
  · have topRestriction : sU.appLE ⊤ ⊤ le_top = sU.appTop :=
      Scheme.Hom.appLE_eq_app sU
    rw [topRestriction, Scheme.ΓSpecIso_naturality]
  · ext element
    simp [RingHom.algebraMap_toAlgebra]
  · simp
  · simp

end AlgebraicGeometry
