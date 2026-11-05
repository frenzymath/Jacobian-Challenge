import Jacobian.AlgebraicGeometry.Modules.Sections
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Local lifting and epimorphisms of module sheaves

A morphism is an epimorphism when every target section locally lifts near
each point. This is the local-surjectivity criterion for its underlying
abelian sheaf.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Surjectivity on sections over every open implies that a morphism is an epimorphism. -/
lemma epi_of_forall_surjective_app {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U, Function.Surjective (φ.app U)) : Epi φ where
  left_cancellation a b hab := by
    refine hom_ext _ _ fun U ↦ ?_
    ext x
    obtain ⟨y, rfl⟩ := h U x
    have := congrArg (fun ψ ↦ ψ.app U y) hab
    simpa using this

/-- Local lifting of target sections implies that a morphism is an epimorphism. -/
lemma epi_of_forall_exists_app_eq {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (W : X.Opens) (y : Γ(N, W)) (x : X), x ∈ W → ∃ (V : X.Opens) (hVW : V ≤ W),
      x ∈ V ∧ ∃ z : Γ(M, V), φ.app V z = N.presheaf.map (homOfLE hVW).op y) :
    Epi φ := by
  have h₁ : TopCat.Presheaf.IsLocallySurjective ((toPresheaf X).map φ) := by
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro W y x hx
    obtain ⟨V, hVW, hxV, z, hz⟩ := h W y x hx
    exact ⟨V, hVW, ⟨z, hz⟩, hxV⟩
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) := h₁
  exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map
    (Sheaf.epi_of_isLocallySurjective _)

end AlgebraicGeometry.Scheme.Modules
