import Jacobian.AlgebraicGeometry.GlobalSections.Rank
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Sections on finite disjoint unions of open subschemes

Restriction decomposes sections on disjoint opens as a product. For schemes over
a field, finiteness passes to each factor and the dimensions add.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {Z : Scheme.{u}} (q : Z ⟶ Spec (.of K))


/-- For disjoint opens `O₁, O₂` of a scheme `Z` over a field `K`, restriction identifies the
`K`-algebra `Γ(Z, O₁ ⊔ O₂)` with `Γ(Z, O₁) × Γ(Z, O₂)`; in particular the dimensions add up. -/
lemma finite_and_finrank_sections_sup_of_inf_eq_bot (O₁ O₂ : Z.Opens) (h : O₁ ⊓ O₂ = ⊥)
    (hfin : letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ (O₁ ⊔ O₂) le_top).hom.toAlgebra;
      Module.Finite K Γ(Z, O₁ ⊔ O₂)) :
    (letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ O₁ le_top).hom.toAlgebra;
      Module.Finite K Γ(Z, O₁)) ∧
    (letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ O₂ le_top).hom.toAlgebra;
      Module.Finite K Γ(Z, O₂)) ∧
    (letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ (O₁ ⊔ O₂) le_top).hom.toAlgebra;
      Module.finrank K Γ(Z, O₁ ⊔ O₂)) =
      (letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ O₁ le_top).hom.toAlgebra;
        Module.finrank K Γ(Z, O₁)) +
      (letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ O₂ le_top).hom.toAlgebra;
        Module.finrank K Γ(Z, O₂)) := by
  let _ := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ (O₁ ⊔ O₂) le_top).hom.toAlgebra
  let _ := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ O₁ le_top).hom.toAlgebra
  let _ := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ O₂ le_top).hom.toAlgebra
  let c := Z.sheaf.isProductOfDisjoint O₁ O₂ h
  let e := c.conePointUniqueUpToIso (CommRingCat.prodFanIsLimit Γ(Z, O₁) Γ(Z, O₂))
  have hbij : Function.Bijective (RingHom.prod
      (Z.presheaf.map (homOfLE (le_sup_left : O₁ ≤ O₁ ⊔ O₂)).op).hom
      (Z.presheaf.map (homOfLE (le_sup_right : O₂ ≤ O₁ ⊔ O₂)).op).hom) :=
    ConcreteCategory.bijective_of_isIso e.hom
  let r₁ : Γ(Z, O₁ ⊔ O₂) →ₐ[K] Γ(Z, O₁) :=
    { (Z.presheaf.map (homOfLE (le_sup_left : O₁ ≤ O₁ ⊔ O₂)).op).hom with
      commutes' := fun k ↦ by
        change (Z.presheaf.map _).hom (((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ _ _).hom k) =
          ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ _ _).hom k
        rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map] }
  let r₂ : Γ(Z, O₁ ⊔ O₂) →ₐ[K] Γ(Z, O₂) :=
    { (Z.presheaf.map (homOfLE (le_sup_right : O₂ ≤ O₁ ⊔ O₂)).op).hom with
      commutes' := fun k ↦ by
        change (Z.presheaf.map _).hom (((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ _ _).hom k) =
          ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ _ _).hom k
        rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map] }
  let E : Γ(Z, O₁ ⊔ O₂) ≃ₐ[K] Γ(Z, O₁) × Γ(Z, O₂) := AlgEquiv.ofBijective (r₁.prod r₂) hbij
  have h₁ : Module.Finite K Γ(Z, O₁) :=
    Module.Finite.of_surjective (LinearMap.fst _ _ _ ∘ₗ E.toLinearEquiv.toLinearMap)
      (Prod.fst_surjective.comp E.surjective)
  have h₂ : Module.Finite K Γ(Z, O₂) :=
    Module.Finite.of_surjective (LinearMap.snd _ _ _ ∘ₗ E.toLinearEquiv.toLinearMap)
      (Prod.snd_surjective.comp E.surjective)
  exact ⟨h₁, h₂, by rw [E.toLinearEquiv.finrank_eq, Module.finrank_prod]⟩

/-- For finitely many pairwise disjoint opens `O i` of a scheme `Z` over a field `K`, the
dimension of the `K`-algebra of sections over their union is the sum of the dimensions of the
sections over the `O i`. -/
lemma finite_and_finrank_sections_iSup {ι : Type*} (O : ι → Z.Opens)
    (s : Finset ι) (hs : (s : Set ι).PairwiseDisjoint O) (U : Z.Opens) (hU : ⨆ i ∈ s, O i = U)
    (hfin : letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ U le_top).hom.toAlgebra;
      Module.Finite K Γ(Z, U)) :
    (∀ i ∈ s, letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ (O i) le_top).hom.toAlgebra;
      Module.Finite K Γ(Z, O i)) ∧
    (letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ U le_top).hom.toAlgebra;
      Module.finrank K Γ(Z, U)) =
      ∑ i ∈ s, (letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ (O i) le_top).hom.toAlgebra;
        Module.finrank K Γ(Z, O i)) := by
  classical
  induction s using Finset.induction_on generalizing U with
  | empty =>
    simp only [Finset.notMem_empty, iSup_false, iSup_bot] at hU
    subst hU
    let _ := ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ ⊥ le_top).hom.toAlgebra
    exact ⟨by simp, by simp [Module.finrank_zero_of_subsingleton]⟩
  | insert a s ha ih =>
    rw [Finset.iSup_insert] at hU
    subst hU
    have hdisj : O a ⊓ ⨆ i ∈ s, O i = ⊥ := by
      rw [← disjoint_iff, disjoint_iSup₂_iff]
      intro i hi
      exact hs (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
        (fun h ↦ ha (h ▸ hi))
    obtain ⟨h₁, h₂, hrank⟩ := finite_and_finrank_sections_sup_of_inf_eq_bot q _ _ hdisj hfin
    obtain ⟨ih₁, ih₂⟩ := ih (hs.subset (by simp)) _ rfl h₂
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · exact h₁
      · exact ih₁ i hi
    · rw [hrank, ih₂, Finset.sum_insert ha]

end AlgebraicGeometry
