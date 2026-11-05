import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Isomorphisms of sheaves are local

A morphism of sheaves is an isomorphism if its components are isomorphisms on a covering
sieve at each object. This follows by expressing the sheaf values as limits over the sieve.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory Category Limits Opposite

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {A : Type u₂} [Category.{v₂} A]
  (J : GrothendieckTopology C) {G G' : Cᵒᵖ ⥤ A}

namespace Presheaf

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of sheaves which is invertible at every object of some covering sieve of `X`
is invertible at `X`: both sides are the limit of their restrictions to the sieve, and the
induced morphism of the two limit diagrams is an isomorphism by assumption. -/
lemma isIso_app_of_isIso_app_of_mem (hG : IsSheaf J G) (hG' : IsSheaf J G') (φ : G ⟶ G')
    {X : C} (S : Sieve X) (hS : S ∈ J X)
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f → IsIso (φ.app (op Y))) :
    IsIso (φ.app (op X)) := by
  obtain ⟨hc⟩ := (isSheaf_iff_isLimit J G).1 hG S hS
  obtain ⟨hc'⟩ := (isSheaf_iff_isLimit J G').1 hG' S hS
  have hiso : ∀ T, IsIso ((Functor.whiskerLeft S.arrows.diagram.op φ).app T) := by
    rintro ⟨T⟩
    exact h T.obj.hom T.property
  have : IsIso (Functor.whiskerLeft S.arrows.diagram.op φ) := NatIso.isIso_of_isIso_app _
  have key : φ.app (op X) = (IsLimit.conePointsIsoOfNatIso hc hc'
      (asIso (Functor.whiskerLeft S.arrows.diagram.op φ))).hom := by
    refine hc'.hom_ext fun T => ?_
    rw [IsLimit.conePointsIsoOfNatIso_hom_comp]
    exact (φ.naturality (S.arrows.cocone.ι.app T.unop).op).symm
  rw [key]
  infer_instance

/-- A morphism of sheaves which, at every object, is invertible on the members of some
covering sieve is an isomorphism. -/
lemma isIso_of_isIso_app_of_mem (hG : IsSheaf J G) (hG' : IsSheaf J G') (φ : G ⟶ G')
    (h : ∀ X : C, ∃ S : Sieve X, S ∈ J X ∧
      ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f → IsIso (φ.app (op Y))) :
    IsIso φ := by
  have : ∀ X : Cᵒᵖ, IsIso (φ.app X) := by
    rintro ⟨X⟩
    obtain ⟨S, hS, hSiso⟩ := h X
    exact isIso_app_of_isIso_app_of_mem J hG hG' φ S hS hSiso
  exact NatIso.isIso_of_isIso_app _

end Presheaf

namespace Sheaf

/-- A morphism of sheaves which, at every object, is invertible on the members of some
covering sieve is an isomorphism. -/
lemma isIso_of_isIso_app_of_mem {G G' : Sheaf J A} (φ : G ⟶ G')
    (h : ∀ X : C, ∃ S : Sieve X, S ∈ J X ∧
      ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f → IsIso (φ.hom.app (op Y))) :
    IsIso φ := by
  have hval : IsIso φ.hom :=
    Presheaf.isIso_of_isIso_app_of_mem J G.property G'.property φ.hom h
  have : IsIso ((sheafToPresheaf J A).map φ) := hval
  exact isIso_of_reflects_iso φ (sheafToPresheaf J A)

end Sheaf

end CategoryTheory
