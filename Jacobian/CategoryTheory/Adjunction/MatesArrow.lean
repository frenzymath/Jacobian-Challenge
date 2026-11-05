import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Counits and invertible mates

An invertible square of left adjoints whose mate is invertible identifies
the corresponding counits as objects of the arrow category.
-/

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Adjunction

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- An invertible mate identifies the image of one counit with the other counit. -/
noncomputable def arrowIsoMapCounit (α : TwoSquare G L₁ L₂ H) (d : D)
    [IsIso (α.app (R₁.obj d))] [IsIso ((mateEquiv adj₁ adj₂ α).app d)] :
    Arrow.mk (H.map (adj₁.counit.app d)) ≅ Arrow.mk (adj₂.counit.app (H.obj d)) :=
  Arrow.isoMk (asIso (inv (α.app (R₁.obj d)) ≫ L₂.map ((mateEquiv adj₁ adj₂ α).app d)))
    (Iso.refl _) (by
      simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, asIso_hom, Category.assoc,
        mateEquiv_counit, IsIso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id])

end CategoryTheory.Adjunction
