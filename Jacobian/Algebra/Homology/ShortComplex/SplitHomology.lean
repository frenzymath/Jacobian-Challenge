import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# Homology from a split middle term

A retract of the middle term that kills boundaries and lies in the cycles computes homology when its complementary summand has a contracting homotopy.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CategoryTheory.ShortComplex

open Limits

variable {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C) {H : C}
  (σ : S.X₂ ⟶ S.X₁) (τ : S.X₃ ⟶ S.X₂) (i : H ⟶ S.X₂) (p : S.X₂ ⟶ H)
  (hip : i ≫ p = 𝟙 H) (hig : i ≫ S.g = 0) (hfp : S.f ≫ p = 0)
  (hsum : p ≫ i + σ ≫ S.f + S.g ≫ τ = 𝟙 S.X₂)

include hig hsum in
lemma kernel_lift_comp_kernel_lift_of_split :
    kernel.ι S.g ≫ p ≫ kernel.lift S.g i hig =
      𝟙 _ - (kernel.ι S.g ≫ σ) ≫ kernel.lift S.g S.f S.zero := by
  refine (cancel_mono (kernel.ι S.g)).1 ?_
  have h := kernel.ι S.g ≫= hsum
  simp only [Preadditive.comp_add, kernel.condition_assoc, zero_comp, add_zero,
    Category.comp_id] at h
  simp only [Category.assoc, kernel.lift_ι, Preadditive.sub_comp, Category.id_comp]
  exact eq_sub_of_add_eq h

/-- The left homology data of a short complex with a split middle term, with homology `H`. -/
noncomputable def leftHomologyDataOfSplit : S.LeftHomologyData where
  K := kernel S.g
  H := H
  i := kernel.ι S.g
  π := kernel.ι S.g ≫ p
  wi := kernel.condition S.g
  hi := kernelIsKernel S.g
  wπ := by
    simp [hfp]
  hπ := CokernelCofork.IsColimit.ofπ _ _ (fun φ _ ↦ kernel.lift S.g i hig ≫ φ)
    (fun φ hφ ↦ by
      simp only [Category.assoc]
      rw [← Category.assoc p, ← Category.assoc, kernel_lift_comp_kernel_lift_of_split S σ τ i p
        hig hsum, Preadditive.sub_comp, Category.id_comp, Category.assoc]
      rw [hφ, comp_zero, sub_zero])
    (fun φ hφ m hm ↦ by
      rw [← hm, ← Category.assoc, kernel.lift_ι_assoc, hip, Category.id_comp])

/-- **Homology of a short complex with a split middle term.** If `H` is a retract of `S.X₂` via
`i` and `p`, with `i` landing in the cycles, `p` killing the boundaries, and
`p ≫ i + σ ≫ S.f + S.g ≫ τ = 𝟙 S.X₂`, then `S.homology ≅ H`. -/
noncomputable def homologyIsoOfSplit : S.homology ≅ H :=
  (S.leftHomologyDataOfSplit σ τ i p hip hig hfp hsum).homologyIso

end CategoryTheory.ShortComplex
