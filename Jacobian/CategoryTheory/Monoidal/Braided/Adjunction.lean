import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braiding and the lax monoidal right adjoint

The tensorator of the lax monoidal right adjoint of a braided functor commutes
with the braidings.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

open Functor.LaxMonoidal Functor.OplaxMonoidal

section

variable {sourceCategory : Type u₁} [Category.{v₁} sourceCategory] [MonoidalCategory sourceCategory] [BraidedCategory sourceCategory]
  {targetCategory : Type u₂} [Category.{v₂} targetCategory] [MonoidalCategory targetCategory] [BraidedCategory targetCategory]
  {leftAdjoint : sourceCategory ⥤ targetCategory} {rightAdjoint : targetCategory ⥤ sourceCategory} (adj : leftAdjoint ⊣ rightAdjoint) [leftAdjoint.Braided]

/-- The right adjoint of a braided monoidal functor, with its lax monoidal structure
`Adjunction.rightAdjointLaxMonoidal`, is compatible with the braidings: the square
```
  G X ⊗ G Y ──μ──▶ G (X ⊗ Y)
      │                │
   β_(G X, G Y)     G (β_(X, Y))
      ▼                ▼
  G Y ⊗ G X ──μ──▶ G (Y ⊗ X)
```
commutes. -/
lemma rightAdjointLaxMonoidal_μ_comp_map_braiding (firstObject secondObject : targetCategory) :
    letI := adj.rightAdjointLaxMonoidal
    μ rightAdjoint firstObject secondObject ≫ rightAdjoint.map (β_ firstObject secondObject).hom = (β_ (rightAdjoint.obj firstObject) (rightAdjoint.obj secondObject)).hom ≫ μ rightAdjoint secondObject firstObject := by
  let := adj.rightAdjointLaxMonoidal
  rw [rightAdjointLaxMonoidal_μ, rightAdjointLaxMonoidal_μ, homEquiv_unit, homEquiv_unit,
    Category.assoc, ← rightAdjoint.map_comp, ← adj.unit_naturality_assoc, ← rightAdjoint.map_comp]
  congr 2
  simp

end


end CategoryTheory.Adjunction
