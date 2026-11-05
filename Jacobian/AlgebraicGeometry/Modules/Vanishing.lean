import Jacobian.AlgebraicGeometry.Modules.RestrictionLimits

/-!
# Vanishing of module sheaves is local

A module sheaf vanishes if all its sections vanish. Vanishing on an open
subset can be tested on its subopens, and vanishing near every point implies
global vanishing.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}}

/-- A module is zero if and only if all its sections vanish. -/
lemma isZero_iff_forall_subsingleton (M : X.Modules) :
    IsZero M ↔ ∀ U : X.Opens, Subsingleton Γ(M, U) := by
  refine ⟨fun h U ↦ ?_, fun h ↦ ?_⟩
  · have h0 (a : Γ(M, U)) : a = 0 := by
      have := congrArg (fun f : M ⟶ M ↦ Hom.app f U a) (h.eq_of_src (𝟙 M) 0)
      simpa using this
    exact ⟨fun a b ↦ (h0 a).trans (h0 b).symm⟩
  · refine (IsZero.iff_id_eq_zero M).mpr (hom_ext _ _ fun U ↦ ?_)
    ext x
    exact Subsingleton.elim _ _

/-- The restriction of `M` to `U` is zero if and only if all sections of `M` over opens contained
in `U` vanish. -/
lemma isZero_restrict_iff (M : X.Modules) (U : X.Opens) :
    IsZero (M.restrict U.ι) ↔ ∀ V : X.Opens, V ≤ U → Subsingleton Γ(M, V) := by
  rw [isZero_iff_forall_subsingleton]
  refine ⟨fun h V hV ↦ ?_, fun h V ↦ h _ (U.ι.image_le_opensRange _ |>.trans (by simp))⟩
  obtain ⟨V', rfl⟩ : ∃ V' : U.toScheme.Opens, U.ι ''ᵁ V' = V :=
    ⟨U.ι ⁻¹ᵁ V, by rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, inf_eq_right.2 hV]⟩
  exact h V'

/-- Vanishing on an open is inherited by smaller opens. -/
lemma isZero_restrict_of_le {M : X.Modules} {U W : X.Opens} (hWU : W ≤ U)
    (h : IsZero (M.restrict U.ι)) : IsZero (M.restrict W.ι) :=
  (isZero_restrict_iff M W).mpr fun V hV ↦ (isZero_restrict_iff M U).mp h V (hV.trans hWU)


/-- **Vanishing is local.** An `𝒪_T`-module whose restriction to a neighbourhood of every point
vanishes is zero: every section vanishes locally. -/
lemma isZero_of_forall_exists_isZero_restrict (M : X.Modules)
    (h : ∀ t : X, ∃ U : X.Opens, t ∈ U ∧ IsZero (M.restrict U.ι)) : IsZero M := by
  rw [isZero_iff_forall_subsingleton]
  intro V
  refine ⟨fun a b ↦ ?_⟩
  choose U hU hMU using h
  let S : Sieve V := Sieve.generate (Presieve.ofArrows (fun t : V ↦ V ⊓ U t)
    (fun _ ↦ homOfLE inf_le_left))
  have hS : S ∈ Opens.grothendieckTopology X V := fun t ht ↦
    ⟨V ⊓ U t, homOfLE inf_le_left,
      ⟨_, 𝟙 _, _, Presieve.ofArrows.mk (⟨t, ht⟩ : V), Category.id_comp _⟩, ⟨ht, hU t⟩⟩
  have hM := ((isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget _ M.presheaf
      (CategoryTheory.forget AddCommGrpCat)).mp M.isSheaf)) _ hS
  refine hM.isSeparatedFor.ext fun Z l hl ↦ ?_
  obtain ⟨Y, g, _, hf, rfl⟩ := hl
  obtain ⟨t⟩ := hf
  exact ((isZero_restrict_iff M (U t)).mp (hMU t) Z ((leOfHom g).trans inf_le_right)).elim _ _

end AlgebraicGeometry.Scheme.Modules
