import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Jacobian.Algebra.Homology.HomotopyCategory.Plus

/-!
# The triangulated bounded below right derived functor

The bounded below derived category is equivalent to the homotopy category of bounded below complexes of injectives. This equips the right derived functor with a triangulated structure.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory

namespace Functor

@[inherit_doc rightDerivedFunctorPlus]
scoped notation "R+(" F ")" => rightDerivedFunctorPlus F

variable {C₀ C D : Type*} [Category* C₀] [Category* C] [Category* D] [Preadditive C₀]
  [HasZeroObject C₀] [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]

/-- For an additive functor `G : C₀ ⥤ D`, the image in `DerivedCategory.Plus D` of the
single complex `X[n]` under `G.mapHomotopyCategoryPlus` is the single complex `(G.obj X)[n]`. -/
noncomputable def mapHomotopyCategoryPlusSingleFunctorQhObjIso (G : C₀ ⥤ D) [G.Additive]
    (n : ℤ) (X : C₀) :
    DerivedCategory.Plus.Qh.obj (G.mapHomotopyCategoryPlus.obj
      ((HomotopyCategory.Plus.singleFunctor C₀ n).obj X)) ≅
      (DerivedCategory.Plus.singleFunctor D n).obj (G.obj X) :=
  DerivedCategory.Plus.ι.preimageIso
    (DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex G _ n).app X))

variable (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- The right derived functor of `F` sends an injective object `I` placed in degree `n` to
`F.obj I` placed in degree `n`: the single complex `I[n]` is a bounded below complex of
injective objects, on which the unit of the right derived functor is an isomorphism. -/
noncomputable def rightDerivedFunctorPlusObjSingleFunctorIso (n : ℤ) (I : C) [Injective I] :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C n).obj I) ≅
      (DerivedCategory.Plus.singleFunctor D n).obj (F.obj I) :=
  F.rightDerivedFunctorPlus.mapIso (mapHomotopyCategoryPlusSingleFunctorQhObjIso
      (InjectiveObject.ι C) n ⟨I, inferInstance⟩).symm ≪≫
    (asIso (F.rightDerivedFunctorPlusUnith.app ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj
      ((HomotopyCategory.Plus.singleFunctor (InjectiveObject C) n).obj
        ⟨I, inferInstance⟩)))).symm ≪≫
    (mapHomotopyCategoryPlusSingleFunctorQhObjIso (InjectiveObject.ι C ⋙ F) n
      ⟨I, inferInstance⟩ :)

end Functor

end CategoryTheory

open CategoryTheory Limits

/-- For an additive functor `F` out of an abelian category with enough injectives and an
injective object `I`, the higher right derived functors of `F` vanish on `I`: the degree-`q`
homology of `R⁺F(I[0])` is zero for `q ≠ 0`. -/
theorem CategoryTheory.Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_singleFunctor
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (I : C) [Injective I] {q : ℤ} (hq : q ≠ 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor D q).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj I))) := by
  let K : CochainComplex.Plus C := ⟨(CochainComplex.singleFunctor C 0).obj I, ⟨0, inferInstance⟩⟩
  have (n : ℤ) : Injective (((HomotopyCategory.Plus.quotient C).obj K).obj.as.X n) := by
    by_cases hn : n = 0
    · subst hn
      exact Injective.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 I).symm
        inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn).injective
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor D q).mapIso
    (asIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj K))).symm)
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactorsh D q).app _)
  refine IsZero.of_iso ?_ ((HomotopyCategory.homologyFunctorFactors D _ q).app _)
  refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
  exact Functor.map_isZero F (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)

/-- For an additive functor `F` out of an abelian category with enough injectives, the right
derived functor `R⁺F` preserves the property of being cohomologically `≥ n`: if `K` has no
homology in degrees `< n`, neither has `R⁺F(K)`, since `K` is represented by a complex of
injective objects concentrated in degrees `≥ n`. -/
theorem CategoryTheory.Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (K : DerivedCategory.Plus C) (n : ℤ) [K.IsGE n] {q : ℤ}
    (hq : q < n) :
    IsZero ((DerivedCategory.Plus.homologyFunctor D q).obj (F.rightDerivedFunctorPlus.obj K)) := by
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  let M := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor D q).mapIso
    (F.rightDerivedFunctorPlus.mapIso e.symm))
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor D q).mapIso
    (asIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj M))).symm)
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactorsh D q).app _)
  refine IsZero.of_iso ?_ ((HomotopyCategory.homologyFunctorFactors D _ q).app _)
  refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
  change IsZero (F.obj ((InjectiveObject.ι C).obj (L.obj.X q)))
  exact F.map_isZero ((InjectiveObject.ι C).map_isZero
    (CochainComplex.isZero_of_isStrictlyGE L.obj n q hq))

namespace DerivedCategory.Plus

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [EnoughInjectives C]

/-- A bounded below complex of injective objects is K-injective. -/
instance (X : HomotopyCategory.Plus (InjectiveObject C)) :
    CochainComplex.IsKInjective ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X).obj.as := by
  obtain ⟨X, hX⟩ := X
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨n, hn⟩ := (HomotopyCategory.plus_quotient_obj_iff _).mp hX
  let L := ((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj K
  have (m : ℤ) : Injective (L.X m) := (K.X m).2
  exact CochainComplex.isKInjective_of_injective L n

variable (C) in
/-- The functor from the bounded below homotopy category of injective objects to the
bounded below derived category. -/
noncomputable abbrev injectiveObjectFunctor :
    HomotopyCategory.Plus (InjectiveObject C) ⥤ DerivedCategory.Plus C :=
  (InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙ Qh

instance : (injectiveObjectFunctor C).Full where
  map_surjective f := by
    obtain ⟨g, rfl⟩ := (Qh_map_bijective_of_isKInjective _ _ inferInstance).2 f
    obtain ⟨h, rfl⟩ := (InjectiveObject.ι C).mapHomotopyCategoryPlus.map_surjective g
    exact ⟨h, rfl⟩

instance : (injectiveObjectFunctor C).Faithful where
  map_injective h :=
    (InjectiveObject.ι C).mapHomotopyCategoryPlus.map_injective
      ((Qh_map_bijective_of_isKInjective _ _ inferInstance).1 h)

instance : (injectiveObjectFunctor C).EssSurj where
  mem_essImage K := by
    obtain ⟨n, hn⟩ := K.2
    have : K.IsGE n := (K.isGE_ι_obj_iff n).1 hn
    obtain ⟨L, _, ⟨e⟩⟩ := exists_injective_nonempty_iso K n
    exact ⟨(HomotopyCategory.Plus.quotient _).obj L, ⟨e⟩⟩

instance : (injectiveObjectFunctor C).IsEquivalence where

variable (C) in
/-- The equivalence between the bounded below homotopy category of injective objects and the
bounded below derived category. -/
noncomputable def injectiveObjectEquivalence :
    HomotopyCategory.Plus (InjectiveObject C) ≌ DerivedCategory.Plus C :=
  (injectiveObjectFunctor C).asEquivalence

noncomputable instance : (injectiveObjectEquivalence C).functor.CommShift ℤ :=
  inferInstanceAs ((injectiveObjectFunctor C).CommShift ℤ)

noncomputable instance : (injectiveObjectEquivalence C).inverse.CommShift ℤ :=
  (injectiveObjectEquivalence C).commShiftInverse ℤ

instance : (injectiveObjectEquivalence C).CommShift ℤ :=
  (injectiveObjectEquivalence C).commShift_of_functor ℤ

instance : (injectiveObjectEquivalence C).functor.IsTriangulated :=
  inferInstanceAs (injectiveObjectFunctor C).IsTriangulated

instance : (injectiveObjectEquivalence C).IsTriangulated :=
  .mk' _ inferInstance

end DerivedCategory.Plus

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] (F : C ⥤ D) [F.Additive]

open DerivedCategory.Plus in
/-- The right derived functor of `F` on bounded below derived categories identifies to the
composition of the inverse of the equivalence `K⁺(Inj) ≌ D⁺` with `F` applied termwise. -/
noncomputable def rightDerivedFunctorPlusIsoInjectiveObject :
    F.rightDerivedFunctorPlus ≅ (injectiveObjectEquivalence C).inverse ⋙
      (InjectiveObject.ι C ⋙ F).mapHomotopyCategoryPlus ⋙ Qh :=
  have : IsIso (whiskerLeft (InjectiveObject.ι C).mapHomotopyCategoryPlus
      F.rightDerivedFunctorPlusUnith) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun X ↦ by dsimp; infer_instance)
  let α : (InjectiveObject.ι C ⋙ F).mapHomotopyCategoryPlus ⋙ Qh ≅
      (injectiveObjectEquivalence C).functor ⋙ F.rightDerivedFunctorPlus :=
    isoWhiskerRight (mapHomotopyCategoryPlusCompIso (Iso.refl _)).symm _ ≪≫
      asIso (whiskerLeft (InjectiveObject.ι C).mapHomotopyCategoryPlus
        F.rightDerivedFunctorPlusUnith)
  (Functor.leftUnitor _).symm ≪≫
    isoWhiskerRight (injectiveObjectEquivalence C).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ α.symm

noncomputable instance : F.rightDerivedFunctorPlus.CommShift ℤ :=
  Functor.CommShift.ofIso F.rightDerivedFunctorPlusIsoInjectiveObject.symm ℤ

instance : F.rightDerivedFunctorPlus.IsTriangulated := by
  have := Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorPlusIsoInjectiveObject.symm ℤ
  exact Functor.isTriangulated_of_iso F.rightDerivedFunctorPlusIsoInjectiveObject.symm

open DerivedCategory.Plus in
/-- The inverse of `Functor.rightDerivedFunctorPlusIsoInjectiveObject` at `Y` is the unit of the
right derived functor at the complex of injective objects attached to `Y`, followed by the
image of the counit of the equivalence `K⁺(Inj) ≌ D⁺`. -/
lemma rightDerivedFunctorPlusIsoInjectiveObject_inv_app (Y : DerivedCategory.Plus C) :
    F.rightDerivedFunctorPlusIsoInjectiveObject.inv.app Y =
      F.rightDerivedFunctorPlusUnith.app ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj
          ((injectiveObjectEquivalence C).inverse.obj Y)) ≫
        F.rightDerivedFunctorPlus.map ((injectiveObjectEquivalence C).counit.app Y) := by
  simp [rightDerivedFunctorPlusIsoInjectiveObject, mapHomotopyCategoryPlusCompIso_refl_inv_app]

open DerivedCategory.Plus in
/-- The unit `F.mapHomotopyCategoryPlus ⋙ Qh ⟶ Qh ⋙ F.rightDerivedFunctorPlus` of the right
derived functor commutes with the shifts. On complexes of injective objects, this is the
definition of the shift structure on `F.rightDerivedFunctorPlus`; in general, every bounded
below complex maps to a complex of injective objects by a quasi-isomorphism. -/
instance commShift_rightDerivedFunctorPlusUnit :
    NatTrans.CommShift F.rightDerivedFunctorPlusUnith ℤ := by
  let inj := (InjectiveObject.ι C).mapHomotopyCategoryPlus
  let E := injectiveObjectEquivalence C
  let G := (InjectiveObject.ι C ⋙ F).mapHomotopyCategoryPlus ⋙ Qh
  let c := mapHomotopyCategoryPlusCompIso (Iso.refl (InjectiveObject.ι C ⋙ F))
  have hI : NatTrans.CommShift F.rightDerivedFunctorPlusIsoInjectiveObject.inv ℤ :=
    Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorPlusIsoInjectiveObject.symm ℤ
  have heq : whiskerLeft inj F.rightDerivedFunctorPlusUnith =
      (associator inj F.mapHomotopyCategoryPlus Qh).inv ≫ whiskerRight c.hom Qh ≫
        (leftUnitor G).inv ≫ whiskerRight E.unitIso.hom G ≫
        (associator E.functor E.inverse G).hom ≫
        whiskerLeft E.functor F.rightDerivedFunctorPlusIsoInjectiveObject.inv ≫
        (associator inj Qh F.rightDerivedFunctorPlus).hom := by
    refine NatTrans.ext (funext fun X ↦ ?_)
    have h₁ := c.hom.naturality (E.unit.app X)
    have h₂ := F.rightDerivedFunctorPlusUnith.naturality (inj.map (E.unit.app X))
    simp only [c, mapHomotopyCategoryPlusCompIso_refl_hom_app, Category.comp_id,
      Category.id_comp] at h₁
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_inv_app,
      associator_hom_app, leftUnitor_inv_app, Category.id_comp, c,
      mapHomotopyCategoryPlusCompIso_refl_hom_app, Functor.map_id,
      rightDerivedFunctorPlusIsoInjectiveObject_inv_app]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    change _ = Qh.map ((InjectiveObject.ι C ⋙ F).mapHomotopyCategoryPlus.map (E.unit.app X)) ≫ _
    rw [← h₁]
    erw [reassoc_of% h₂]
    change _ = _ ≫ R+(F).map (E.functor.map (E.unit.app X)) ≫
      R+(F).map (E.counit.app (E.functor.obj X))
    rw [← Functor.map_comp]
    erw [E.functor_unit_comp, Functor.map_id, Category.comp_id]
  have : NatTrans.CommShift (whiskerLeft inj F.rightDerivedFunctorPlusUnith) ℤ := by
    rw [heq]; infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ inj (fun K ↦ ?_)
  obtain ⟨f, hf⟩ := (Qh_map_bijective_of_isKInjective K (inj.obj (E.inverse.obj (Qh.obj K)))
    inferInstance).2 (E.counitIso.inv.app (Qh.obj K))
  refine ⟨_, f, ?_⟩
  rw [Functor.comp_map, hf]
  infer_instance

end CategoryTheory.Functor
