import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Jacobian.Algebra.Homology.HomotopyCategory.Functor
import Jacobian.Algebra.Homology.HomotopyCategory.Shift

/-!
# Functoriality on bounded below homotopy categories

Natural transformations and identity comparisons descend to the bounded below homotopy category and commute with shifts.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace CategoryTheory.NatTrans

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]

/-- The components of `NatTrans.mapHomotopyCategoryPlus τ`, viewed in the ambient homotopy
category, are those of `NatTrans.mapHomotopyCategory τ`. -/
@[simp]
lemma ι_map_mapHomotopyCategoryPlus_app {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G)
    (K : HomotopyCategory.Plus C) :
    (HomotopyCategory.Plus.ι D).map ((NatTrans.mapHomotopyCategoryPlus τ).app K) =
      (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K.obj :=
  NatTrans.congr_app (((HomotopyCategory.plus D).fullyFaithfulι.whiskeringRight
    (HomotopyCategory.Plus C)).map_preimage (X := F.mapHomotopyCategoryPlus)
      (Y := G.mapHomotopyCategoryPlus) (Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
        (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)))) K

/-- `NatTrans.mapHomotopyCategoryPlus` sends a right unitor to the identity. -/
@[simp]
lemma mapHomotopyCategoryPlus_rightUnitor_hom_app {𝒞 𝒟 : Type*}
    [Category* 𝒞] [Category* 𝒟] [Preadditive 𝒞] [Preadditive 𝒟] (F : 𝒞 ⥤ 𝒟) [F.Additive]
    (K : HomotopyCategory.Plus 𝒞) :
    (NatTrans.mapHomotopyCategoryPlus F.rightUnitor.hom).app K = 𝟙 _ := by
  apply (HomotopyCategory.Plus.ι 𝒟).map_injective
  obtain ⟨⟨X⟩, hK⟩ := K
  rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app]
  erw [CategoryTheory.Functor.map_id]
  change (HomotopyCategory.quotient _ _).map _ = 𝟙 ((HomotopyCategory.quotient _ _).obj _)
  rw [← (HomotopyCategory.quotient _ _).map_id]
  congr 1

/-- `NatTrans.mapHomotopyCategoryPlus` sends the inverse of a right unitor to the identity. -/
@[simp]
lemma mapHomotopyCategoryPlus_rightUnitor_inv_app {𝒞 𝒟 : Type*}
    [Category* 𝒞] [Category* 𝒟] [Preadditive 𝒞] [Preadditive 𝒟] (F : 𝒞 ⥤ 𝒟) [F.Additive]
    (K : HomotopyCategory.Plus 𝒞) :
    (NatTrans.mapHomotopyCategoryPlus F.rightUnitor.inv).app K = 𝟙 _ := by
  apply (HomotopyCategory.Plus.ι 𝒟).map_injective
  obtain ⟨⟨X⟩, hK⟩ := K
  rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app]
  erw [CategoryTheory.Functor.map_id]
  change (HomotopyCategory.quotient _ _).map _ = 𝟙 ((HomotopyCategory.quotient _ _).obj _)
  rw [← (HomotopyCategory.quotient _ _).map_id]
  congr 1

/-- `NatTrans.mapHomotopyCategoryPlus` sends the inverse of a left unitor to the identity. -/
@[simp]
lemma mapHomotopyCategoryPlus_leftUnitor_inv_app {𝒞 𝒟 : Type*}
    [Category* 𝒞] [Category* 𝒟] [Preadditive 𝒞] [Preadditive 𝒟] (F : 𝒞 ⥤ 𝒟) [F.Additive]
    (K : HomotopyCategory.Plus 𝒞) :
    (NatTrans.mapHomotopyCategoryPlus F.leftUnitor.inv).app K = 𝟙 _ := by
  apply (HomotopyCategory.Plus.ι 𝒟).map_injective
  obtain ⟨⟨X⟩, hK⟩ := K
  rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app]
  erw [CategoryTheory.Functor.map_id]
  change (HomotopyCategory.quotient _ _).map _ = 𝟙 ((HomotopyCategory.quotient _ _).obj _)
  rw [← (HomotopyCategory.quotient _ _).map_id]
  congr 1

/-- The natural transformation `NatTrans.mapHomotopyCategoryPlus τ` induced by a natural
isomorphism is an isomorphism, with inverse induced by the inverse. -/
instance isIso_mapHomotopyCategoryPlus {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) [IsIso τ] : IsIso (NatTrans.mapHomotopyCategoryPlus τ) :=
  ⟨NatTrans.mapHomotopyCategoryPlus (inv τ),
    by rw [← mapHomotopyCategoryPlus_comp, IsIso.hom_inv_id, mapHomotopyCategoryPlus_id],
    by rw [← mapHomotopyCategoryPlus_comp, IsIso.inv_hom_id, mapHomotopyCategoryPlus_id]⟩

end CategoryTheory.NatTrans

namespace CategoryTheory.Functor

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]

/-- The functor on bounded below homotopy categories induced by the identity functor is
isomorphic to the identity functor: the bounded below counterpart of
`CategoryTheory.Functor.mapHomotopyCategoryIdIso`. -/
noncomputable def mapHomotopyCategoryPlusIdIso :
    (𝟭 C).mapHomotopyCategoryPlus ≅ 𝟭 (HomotopyCategory.Plus C) :=
  fullyFaithfulCancelRight (HomotopyCategory.Plus.ι C)
    (isoWhiskerLeft (HomotopyCategory.Plus.ι C)
        (mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)) ≪≫
      (HomotopyCategory.Plus.ι C).rightUnitor ≪≫
      (HomotopyCategory.Plus.ι C).leftUnitor.symm)

@[simp]
lemma ι_map_mapHomotopyCategoryPlusIdIso_hom_app (K : HomotopyCategory.Plus C) :
    (HomotopyCategory.Plus.ι C).map ((mapHomotopyCategoryPlusIdIso C).hom.app K) =
      (mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app K.obj := by
  rw [mapHomotopyCategoryPlusIdIso, fullyFaithfulCancelRight_hom_app,
    Functor.map_preimage]
  simp

@[simp]
lemma ι_map_mapHomotopyCategoryPlusIdIso_inv_app (K : HomotopyCategory.Plus C) :
    (HomotopyCategory.Plus.ι C).map ((mapHomotopyCategoryPlusIdIso C).inv.app K) =
      (mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).inv.app K.obj := by
  rw [mapHomotopyCategoryPlusIdIso, fullyFaithfulCancelRight_inv_app,
    Functor.map_preimage]
  simp

/-- The isomorphism `Functor.mapHomotopyCategoryPlusIdIso` is the identity: this is the
bounded below counterpart of `Functor.mapHomotopyCategoryIdIso_hom_app_eq_id`. -/
lemma mapHomotopyCategoryPlusIdIso_hom_app_eq_id (K : HomotopyCategory.Plus C) :
    (mapHomotopyCategoryPlusIdIso C).hom.app K = 𝟙 K := by
  apply (HomotopyCategory.Plus.ι C).map_injective
  refine Eq.trans ?_ ((HomotopyCategory.Plus.ι C).map_id K).symm
  rw [ι_map_mapHomotopyCategoryPlusIdIso_hom_app]
  exact mapHomotopyCategoryIdIso_hom_app_eq_id C (ComplexShape.up ℤ) K.obj

/-- The inverse form of `Functor.mapHomotopyCategoryPlusIdIso_hom_app_eq_id`. -/
lemma mapHomotopyCategoryPlusIdIso_inv_app_eq_id (K : HomotopyCategory.Plus C) :
    (mapHomotopyCategoryPlusIdIso C).inv.app K = 𝟙 _ :=
  congrArg Iso.inv (Iso.ext (mapHomotopyCategoryPlusIdIso_hom_app_eq_id C K) :
    (mapHomotopyCategoryPlusIdIso C).app K = Iso.refl _)

/-- The isomorphism `Functor.mapHomotopyCategoryPlusCompIso` attached to `Iso.refl (F ⋙ G)`
is the identity: this is the bounded below counterpart of
`Functor.mapHomotopyCategoryCompIso_refl_hom_app`. -/
lemma mapHomotopyCategoryPlusCompIso_refl_hom_app {C D E : Type*} [Category C] [Category D]
    [Category E] [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory.Plus C) :
    (mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K = 𝟙 _ := by
  apply (HomotopyCategory.Plus.ι E).map_injective
  refine Eq.trans ?_ ((HomotopyCategory.Plus.ι E).map_id _).symm
  have h : (HomotopyCategory.Plus.ι E).map
      ((mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K) =
      (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app K.obj := rfl
  rw [h]
  exact mapHomotopyCategoryCompIso_refl_hom_app (ComplexShape.up ℤ) F G K.obj

/-- The inverse form of `Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app`. -/
lemma mapHomotopyCategoryPlusCompIso_refl_inv_app {C D E : Type*} [Category C] [Category D]
    [Category E] [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory.Plus C) :
    (mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app K = 𝟙 _ :=
  congrArg Iso.inv (Iso.ext (mapHomotopyCategoryPlusCompIso_refl_hom_app F G K) :
    (mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).app K = Iso.refl _)

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]

instance commShift_mapHomotopyCategoryPlus {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) : NatTrans.CommShift (NatTrans.mapHomotopyCategoryPlus τ) ℤ := by
  have : Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus τ) (HomotopyCategory.Plus.ι D) =
      ((HomotopyCategory.plus D).liftCompιIso _ _).hom ≫
        Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
          (NatTrans.mapHomotopyCategory τ (.up ℤ)) ≫
        ((HomotopyCategory.plus D).liftCompιIso _ _).inv := by
    ext K
    simp [ObjectProperty.liftCompιIso]
    rfl
  have : NatTrans.CommShift (Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus τ)
      (HomotopyCategory.Plus.ι D)) ℤ := by
    rw [this]; infer_instance
  exact CommShift.of_whiskerRight _ (HomotopyCategory.Plus.ι D)

instance commShift_mapHomotopyCategoryPlusCompIso {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) :
    NatTrans.CommShift (Functor.mapHomotopyCategoryPlusCompIso e).hom ℤ := by
  have : Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso e).hom
      (HomotopyCategory.Plus.ι E) =
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft F.mapHomotopyCategoryPlus
        ((HomotopyCategory.plus E).liftCompιIso _ _).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ((HomotopyCategory.plus D).liftCompιIso _ _).hom
        (G.mapHomotopyCategory (.up ℤ)) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
        (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom ≫
      ((HomotopyCategory.plus E).liftCompιIso _ _).inv := by
    ext K
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.whiskerRight_app,
      ObjectProperty.ι_map, comp_app, ObjectProperty.lift_obj_obj, Functor.associator_hom_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Category.id_comp]
    rw [show ((Functor.mapHomotopyCategoryPlusCompIso e).hom.app K).hom =
      (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app K.obj from rfl]
    simp only [ObjectProperty.liftCompιIso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [Category.id_comp, Functor.map_id, Category.id_comp, Category.id_comp,
      Category.comp_id]
  have : NatTrans.CommShift (Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso e).hom
      (HomotopyCategory.Plus.ι E)) ℤ := by
    rw [this]; infer_instance
  exact CommShift.of_whiskerRight _ (HomotopyCategory.Plus.ι E)

end CategoryTheory.NatTrans
