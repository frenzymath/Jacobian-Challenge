import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Jacobian.CategoryTheory.Shift.CommShift

/-!
# Functorial maps and shifts

Natural transformations and composition comparisons induced by additive functors commute with shifts.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory

namespace CategoryTheory.NatTrans

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]

instance commShift_mapHomologicalComplex {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) : NatTrans.CommShift (NatTrans.mapHomologicalComplex τ (.up ℤ)) ℤ where
  shift_comm n := by
    ext K i
    dsimp
    erw [Category.id_comp, Category.comp_id]
    rfl

instance commShift_mapHomologicalComplexCompIso {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) :
    NatTrans.CommShift (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom ℤ where
  shift_comm n := by
    ext K i
    simp only [Functor.comp_obj, CochainComplex.shiftFunctor_obj_X', comp_app,
      Functor.whiskerRight_app, HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
      Functor.mapHomologicalComplexCompIso_hom_app_f, Functor.whiskerLeft_app,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Category.comp_id,
      Functor.commShiftIso_comp_hom_app, Functor.mapHomologicalComplex_map_f]
    erw [Functor.map_id, Category.id_comp]

instance commShift_mapHomotopyCategory {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) : NatTrans.CommShift (NatTrans.mapHomotopyCategory τ (.up ℤ)) ℤ := by
  have : Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (NatTrans.mapHomotopyCategory τ (.up ℤ)) =
      (F.mapHomotopyCategoryFactors (.up ℤ)).hom ≫
        Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (.up ℤ))
          (HomotopyCategory.quotient D (.up ℤ)) ≫
        (G.mapHomotopyCategoryFactors (.up ℤ)).inv := by
    ext K
    simp only [Functor.mapHomotopyCategoryFactors, NatTrans.comp_app]
    erw [Category.id_comp, Category.comp_id]
    rfl
  have : NatTrans.CommShift (Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (NatTrans.mapHomotopyCategory τ (.up ℤ))) ℤ := by
    rw [this]; infer_instance
  exact CommShift.of_whiskerLeft _ (HomotopyCategory.quotient C (.up ℤ))
    (fun X ↦ by
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      exact ⟨K, 𝟙 _, inferInstance⟩)

instance commShift_mapHomotopyCategoryCompIso {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) :
    NatTrans.CommShift (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom ℤ := by
  have : Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom =
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom
        (G.mapHomotopyCategory (.up ℤ)) ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
        (G.mapHomotopyCategoryFactors (.up ℤ)).hom ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom
          (HomotopyCategory.quotient E (.up ℤ)) ≫
        (H.mapHomotopyCategoryFactors (.up ℤ)).inv := by
    ext K
    simp only [Functor.mapHomotopyCategoryFactors, Functor.mapHomotopyCategoryCompIso,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Quotient.natIsoLift_hom, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.isoWhiskerRight_hom]
    erw [Quotient.natTransLift_app]
    simp only [Functor.comp_obj, Functor.whiskerRight_app, Quotient.lift.isLift_hom,
      Quotient.lift.isLift_inv, Category.comp_id, Category.id_comp]
    erw [Functor.map_id, Category.id_comp, Category.id_comp]
  have : NatTrans.CommShift (Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom) ℤ := by
    rw [this]; infer_instance
  exact CommShift.of_whiskerLeft _ (HomotopyCategory.quotient C (.up ℤ))
    (fun X ↦ by
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      exact ⟨K, 𝟙 _, inferInstance⟩)

end CategoryTheory.NatTrans
