import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Dimension of global sections over an affine base

A morphism to an affine scheme gives its global sections an algebra structure.
Its dimension is invariant under isomorphisms over isomorphic affine bases.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {Z : Scheme.{u}} {R : CommRingCat.{u}}

/-- The algebra of global sections induced by a morphism to `Spec R`. -/
@[instance_reducible]
noncomputable def Scheme.Hom.ΓAlgebra (h : Z ⟶ Spec R) : Algebra R Γ(Z, ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ h.appTop).hom.toAlgebra

lemma Scheme.Hom.algebraMap_ΓAlgebra (h : Z ⟶ Spec R) :
    letI := h.ΓAlgebra
    algebraMap R Γ(Z, ⊤) = ((Scheme.ΓSpecIso R).inv ≫ h.appTop).hom :=
  rfl

/-- The `R`-dimension of the ring of global sections of a scheme over `Spec R`.

For a finite group scheme `G` over a field `K` this is its *order* `|G| = dim_K Γ(G, 𝒪_G)`. -/
noncomputable def Scheme.Hom.finrankΓ (h : Z ⟶ Spec R) : ℕ :=
  letI := h.ΓAlgebra
  Module.finrank R Γ(Z, ⊤)

/-- An isomorphism of schemes over an isomorphism of affine bases induces an isomorphism of
rings of global sections compatible with the algebra structures. -/
lemma Scheme.Hom.finrankΓ_eq_of_iso {Z Z' : Scheme.{u}} {R R' : CommRingCat.{u}}
    (h : Z ⟶ Spec R) (h' : Z' ⟶ Spec R') (e : Z ≅ Z') (i : R ≅ R')
    (he : e.hom ≫ h' ≫ Spec.map i.hom = h) :
    h.finrankΓ = h'.finrankΓ := by
  let _ := h.ΓAlgebra
  let _ := h'.ΓAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv i.commRingCatIsoToRingEquiv
    (asIso e.inv.appTop).commRingCatIsoToRingEquiv ?_
  have he' : e.inv ≫ h = h' ≫ Spec.map i.hom := by
    rw [← he, Iso.inv_hom_id_assoc]
  change ((ΓSpecIso R').inv ≫ h'.appTop).hom.comp i.hom.hom =
    e.inv.appTop.hom.comp ((ΓSpecIso R).inv ≫ h.appTop).hom
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Category.assoc, ← Scheme.Hom.comp_appTop, he',
    Scheme.Hom.comp_appTop, ← ΓSpecIso_inv_naturality_assoc]

/-- The `R`-dimension of the global sections of `Spec S` over `Spec R` is `dim_R S`. -/
lemma Scheme.Hom.finrankΓ_SpecMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).finrankΓ = Module.finrank R S := by
  let _ := (Spec.map (CommRingCat.ofHom (algebraMap R S))).ΓAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
    (Scheme.ΓSpecIso (.of S)).commRingCatIsoToRingEquiv ?_
  refine RingHom.ext fun y ↦ ?_
  change algebraMap R S y = (Scheme.ΓSpecIso (.of S)).hom
    (((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop) y)
  rw [← CommRingCat.comp_apply, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]
  rfl


/-- Global rank can be computed using the map on sections over the top open. -/
lemma Scheme.Hom.finrankΓ_eq_finrank_appLE {Z : Scheme.{u}} {R : CommRingCat.{u}}
    (g : Z ⟶ Spec R) : g.finrankΓ =
      letI := ((Scheme.ΓSpecIso R).inv ≫ g.appLE ⊤ ⊤ le_top).hom.toAlgebra
      Module.finrank R Γ(Z, ⊤) := by
  let P : (R →+* Γ(Z, ⊤)) → ℕ := fun φ =>
    letI := φ.toAlgebra
    Module.finrank R Γ(Z, ⊤)
  change P ((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom =
    P ((Scheme.ΓSpecIso R).inv ≫ g.appLE ⊤ ⊤ le_top).hom
  have hmap : g.appLE ⊤ ⊤ le_top = g.appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  exact congrArg P (congrArg
    (fun a : Γ(Spec R, ⊤) ⟶ Γ(Z, ⊤) => ((Scheme.ΓSpecIso R).inv ≫ a).hom)
    hmap).symm

end AlgebraicGeometry
