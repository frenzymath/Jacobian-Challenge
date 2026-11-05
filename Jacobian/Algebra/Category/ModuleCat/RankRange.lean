import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Rank of the image under isomorphisms

Composing a module homomorphism with isomorphisms preserves the finrank of its image.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

/-- Composing a linear map with isomorphisms on both sides does not change the dimension of its
range: `dim range (a ≫ m ≫ b) = dim range m` for isomorphisms `a` and `b`. -/
lemma ModuleCat.finrank_range_iso_comp {R : Type*} [Ring R] {M N M' N' : ModuleCat.{u} R}
    (a : M' ≅ M) (m : M ⟶ N) (b : N ≅ N') :
    Module.finrank R (LinearMap.range (a.hom ≫ m ≫ b.hom).hom) =
      Module.finrank R (LinearMap.range m.hom) := by
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.2 (ConcreteCategory.bijective_of_isIso a.hom).2, Submodule.map_top,
    LinearMap.range_comp]
  exact b.toLinearEquiv.finrank_map_eq _
