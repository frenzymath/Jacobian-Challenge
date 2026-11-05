import Jacobian.RingTheory.FaithfullyFlat.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Flatness under surjective source maps

Flatness descends along a flat surjection on the source, by faithfully flat
local maps of stalks.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If `u` is flat and surjective and `u ≫ f` is flat, then `f` is flat. -/
theorem Flat.of_comp_of_flat_of_surjective {X' X S : Scheme.{u}} (u : X' ⟶ X) (f : X ⟶ S)
    [Flat u] [Surjective u] [Flat (u ≫ f)] : Flat f := by
  refine Flat.of_stalkMap f fun x ↦ ?_
  obtain ⟨x', rfl⟩ := u.surjective x
  have h := Flat.stalkMap (u ≫ f) x'
  rw [Scheme.Hom.stalkMap_comp] at h
  have hu := Flat.stalkMap u x'
  algebraize [(f.stalkMap (u x')).hom, (u.stalkMap x').hom,
    (u.stalkMap x').hom.comp (f.stalkMap (u x')).hom]
  have : Module.FaithfullyFlat (X.presheaf.stalk (u x')) (X'.presheaf.stalk x') :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ hu (u.toLRSHom.prop x')
  have : Module.Flat (S.presheaf.stalk (f (u x'))) (X'.presheaf.stalk x') := h
  exact Module.Flat.of_flat_of_faithfullyFlat (B := X.presheaf.stalk (u x'))
    (C := X'.presheaf.stalk x')

end AlgebraicGeometry
