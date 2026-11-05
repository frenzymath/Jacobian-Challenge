import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Functoriality on homotopy categories

The identity and composition comparison isomorphisms for additive functors on homotopy categories.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe v u

open CategoryTheory

namespace CategoryTheory.Functor

variable (V : Type u) [Category.{v} V] [Preadditive V] {ι : Type*} (c : ComplexShape ι)

/-- The functor on homotopy categories induced by the identity functor is isomorphic to
the identity functor: the homotopy category counterpart of
`CategoryTheory.Functor.mapHomologicalComplexIdIso`. -/
noncomputable def mapHomotopyCategoryIdIso :
    (𝟭 V).mapHomotopyCategory c ≅ 𝟭 (HomotopyCategory V c) :=
  Quotient.natIsoLift _ ((𝟭 V).mapHomotopyCategoryFactors c ≪≫
    isoWhiskerRight (mapHomologicalComplexIdIso V c) (HomotopyCategory.quotient V c) ≪≫
    (HomotopyCategory.quotient V c).leftUnitor ≪≫
    (HomotopyCategory.quotient V c).rightUnitor.symm)

@[simp]
lemma mapHomotopyCategoryIdIso_hom_app (K : HomologicalComplex V c) :
    (mapHomotopyCategoryIdIso V c).hom.app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient V c).map
        ((mapHomologicalComplexIdIso V c).hom.app K) := by
  simp only [mapHomotopyCategoryIdIso, HomotopyCategory.quotient, mapHomotopyCategoryFactors,
    Quotient.natIsoLift_hom, Quotient.natTransLift_app, id_obj, Iso.trans_hom,
    isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app, comp_obj, Quotient.lift.isLift_hom,
    whiskerRight_app, leftUnitor_hom_app, rightUnitor_inv_app, Category.comp_id]
  apply Category.id_comp

@[simp]
lemma mapHomotopyCategoryIdIso_inv_app (K : HomologicalComplex V c) :
    (mapHomotopyCategoryIdIso V c).inv.app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient V c).map
        ((mapHomologicalComplexIdIso V c).inv.app K) := by
  simp [mapHomotopyCategoryIdIso, HomotopyCategory.quotient, mapHomotopyCategoryFactors]

/-- The isomorphism `Functor.mapHomotopyCategoryIdIso` is the identity: it is induced by
`Functor.mapHomologicalComplexIdIso`, which is the identity by definition. -/
lemma mapHomotopyCategoryIdIso_hom_app_eq_id (Y : HomotopyCategory V c) :
    (mapHomotopyCategoryIdIso V c).hom.app Y = 𝟙 Y := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  rw [mapHomotopyCategoryIdIso_hom_app]
  exact (HomotopyCategory.quotient V c).map_id X

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {V W V' : Type*} [Category V] [Category W] [Category V'] [Preadditive V]
  [Preadditive W] [Preadditive V'] {ι : Type*} (c : ComplexShape ι)

/-- The isomorphism `Functor.mapHomotopyCategoryCompIso` attached to `Iso.refl (F ⋙ G)` is
the identity: it is induced by `Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))`,
which is the identity by definition. -/
lemma mapHomotopyCategoryCompIso_refl_hom_app (F : V ⥤ W) (G : W ⥤ V') [F.Additive]
    [G.Additive] (Y : HomotopyCategory V c) :
    (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).hom.app Y = 𝟙 _ := by
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  have h₁ : (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) c).hom.app
      ((HomotopyCategory.quotient V c).obj X) =
      (HomotopyCategory.quotient V' c).map
        ((mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c).hom.app X) := rfl
  have h₂ : (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c).hom.app X = 𝟙 _ := rfl
  rw [h₁, h₂]
  exact (HomotopyCategory.quotient V' c).map_id _

end CategoryTheory.Functor
