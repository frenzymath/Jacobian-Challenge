import Jacobian.CategoryTheory.Sites.SheafCohomology.ExactSequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# First cohomology and lifting global sections

A sheaf whose global sections lift through every short exact sequence with
that kernel has vanishing first cohomology. The proof embeds the sheaf into
an injective and uses the Ext connecting map.
-/

universe w' w v u
namespace CategoryTheory
open Abelian Limits AddCommGrpCat

section VanishingH1

open Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]

/-- **`H¹` vanishes when global sections lift.** Let `T` be a terminal object, so that global
sections are sections over `T`. If for every short exact sequence `0 → F → E → Q → 0` of
abelian sheaves every global section of `Q` lifts to a global section of `E`, then
`H¹(F) = 0`.

In torsor language: the fibre of `E → Q` over a global section of `Q` is an `F`-torsor, which
is trivial exactly when the section lifts; every class in `H¹(F) = Ext¹(ℤ, F)` arises this way
from an embedding of `F` into an injective sheaf. This is the half of the classification of
`H¹` by torsors that is needed for vanishing results. -/
theorem Sheaf.subsingleton_H_one_of_surjective (F : Sheaf J AddCommGrpCat.{w}) {T : C}
    (hT : IsTerminal T)
    (h : ∀ ⦃E Q : Sheaf J AddCommGrpCat.{w}⦄ (ι : F ⟶ E) (π : E ⟶ Q) (w : ι ≫ π = 0),
      (ShortComplex.mk ι π w).ShortExact → Function.Surjective (π.hom.app (op T))) :
    Subsingleton (H F 1) := by
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ :=
    Ext.covariant_sequence_exact₁ _ hS x (Ext.eq_zero_of_injective _) (zero_add 1)
  obtain ⟨t, ht⟩ := h S.f S.g S.zero hS (H.equiv₀ S.X₃ hT y)
  have hy : ((H.equiv₀ S.X₂ hT).symm t).comp (Ext.mk₀ S.g) (add_zero 0) = y := by
    rw [← H.map_apply, H.equiv₀_symm_naturality, ht, AddEquiv.symm_apply_apply]
  rw [← hy, Ext.comp_assoc _ _ _ (add_zero 0) (zero_add 1) (zero_add 1), hS.comp_extClass,
    Ext.comp_zero]

end VanishingH1

end CategoryTheory
