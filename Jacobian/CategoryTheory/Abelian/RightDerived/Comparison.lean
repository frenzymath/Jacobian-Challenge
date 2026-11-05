import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Jacobian.Algebra.Homology.Embedding.Map
import Jacobian.Algebra.Homology.DerivedCategory.RightDerived
import Jacobian.CategoryTheory.Abelian.RightDerived

/-!
# Right derived functors on single complexes

The homology of the bounded below right derived functor on a complex concentrated in degree zero identifies naturally with the classical right derived functors.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace DerivedCategory.Plus

open CategoryTheory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The homology of the image in `DerivedCategory.Plus C` of a bounded below cochain complex
is the homology of the complex. -/
noncomputable def homologyFunctorObjQIso (K : CochainComplex.Plus C) (n : ℤ) :
    (homologyFunctor C n).obj (Q.obj K) ≅ K.obj.homology n :=
  (DerivedCategory.homologyFunctorFactorsh C n).app _ ≪≫
    (HomotopyCategory.homologyFunctorFactors C _ n).app K.obj

/-- The isomorphism `DerivedCategory.Plus.homologyFunctorObjQIso` is natural. -/
@[reassoc]
lemma homologyFunctorObjQIso_hom_naturality {K L : CochainComplex.Plus C} (g : K ⟶ L) (n : ℤ) :
    (homologyFunctor C n).map (Q.map g) ≫ (homologyFunctorObjQIso L n).hom =
      (homologyFunctorObjQIso K n).hom ≫ HomologicalComplex.homologyMap g.hom n := by
  have h₁ := (DerivedCategory.homologyFunctorFactorsh C n).hom.naturality
    ((HomotopyCategory.quotient C _).map g.hom)
  have h₂ := (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n).hom.naturality g.hom
  dsimp at h₁ h₂
  simp only [homologyFunctorObjQIso]
  change (DerivedCategory.homologyFunctor C n).map
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map g.hom)) ≫ _ = _
  erw [Iso.trans_hom, Iso.trans_hom, reassoc_of% h₁, h₂]
  simp only [Category.assoc]
  rfl

end DerivedCategory.Plus

namespace CategoryTheory

open Limits ZeroObject

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

namespace InjectiveResolution

variable [HasInjectiveResolutions C]

/-- If `R` is an injective resolution of `X`, then `R^n F X` is the `n`-th homology of `F`
applied to the `ℤ`-indexed cochain complex `R.cochainComplex`. -/
noncomputable def isoRightDerivedObjCochainComplex {X : C} (R : InjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.rightDerived n).obj X ≅
      ((F.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex).homology n :=
  R.isoRightDerivedObj F n ≪≫
    (((F.mapHomologicalComplex _).obj R.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat rfl).symm ≪≫
    (HomologicalComplex.homologyFunctor D _ (n : ℤ)).mapIso
      (HomologicalComplex.mapExtendIso R.cocomplex ComplexShape.embeddingUpNat F).symm

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `R^n F X ≅ H^n(F(I))` is natural with respect to morphisms of injective
resolutions. -/
lemma isoRightDerivedObjCochainComplex_inv_naturality {X Y : C} {f : X ⟶ Y}
    (R : InjectiveResolution X) {R' : InjectiveResolution Y} (φ : R.Hom R' f) (F : C ⥤ D)
    [F.Additive] (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ.hom') n ≫
        (R'.isoRightDerivedObjCochainComplex F n).inv =
      (R.isoRightDerivedObjCochainComplex F n).inv ≫ (F.rightDerived n).map f := by
  rw [F.rightDerived_map_eq n f φ.hom φ.ι_comp_hom]
  have h : (F.mapHomologicalComplex _).map φ.hom' ≫
      (R'.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom =
      (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex _).map φ.hom)
          ComplexShape.embeddingUpNat := by
    ext i
    exact HomologicalComplex.mapExtensIso_hom_f_naturality _ _ _ _
  simp only [InjectiveResolution.isoRightDerivedObjCochainComplex, Iso.trans_inv, Iso.symm_inv,
    Category.assoc]
  simp only [Functor.mapIso_inv, Iso.symm_inv, Functor.comp_map,
    HomologicalComplex.homologyFunctor_map, Iso.inv_hom_id_assoc]
  rw [← HomologicalComplex.homologyMap_comp_assoc, h, HomologicalComplex.homologyMap_comp_assoc,
    HomologicalComplex.extendHomologyIso_hom_naturality_assoc]

end InjectiveResolution

namespace Functor

variable (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

section

variable [HasDerivedCategory C] [HasDerivedCategory D]

/-- If `L` is a bounded below complex of injective objects, the homology of `R⁺F(L)` is the
homology of `F(L)`. -/
noncomputable def homologyRightDerivedFunctorPlusObjQIsoOfInjective (L : CochainComplex.Plus C)
    [∀ n, Injective (L.obj.X n)] (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D n).obj
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj L)) ≅
      ((F.mapHomologicalComplex _).obj L.obj).homology n :=
  (DerivedCategory.Plus.homologyFunctor D n).mapIso
      (asIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj L))).symm ≪≫
    (DerivedCategory.homologyFunctorFactorsh D n).app _ ≪≫
    (HomotopyCategory.homologyFunctorFactors D _ n).app _

/-- The bounded below cochain complex `F(I)`, where `I` is the chosen injective resolution of
`X : C` (as a `ℤ`-indexed complex). Its image in `DerivedCategory.Plus D` is `R⁺F(X[0])`, see
`Functor.rightDerivedFunctorPlusObjSingleFunctorIsoQ`. -/
noncomputable def rightDerivedPlusComplex (X : C) : CochainComplex.Plus D :=
  ⟨(F.mapHomologicalComplex _).obj (injectiveResolution X).cochainComplex, 0, inferInstance⟩

/-- `R⁺F(X[0])` is the image in the derived category of the complex `F(I)`, where `I` is the
chosen injective resolution of `X`. -/
noncomputable def rightDerivedFunctorPlusObjSingleFunctorIsoQ (X : C) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≅
      DerivedCategory.Plus.Q.obj (F.rightDerivedPlusComplex X) :=
  let R := injectiveResolution X
  let L : CochainComplex.Plus C := ⟨R.cochainComplex, 0, inferInstance⟩
  have : ∀ n, Injective (L.obj.X n) := fun n ↦ inferInstanceAs (Injective (R.cochainComplex.X n))
  F.rightDerivedFunctorPlus.mapIso (DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app X ≪≫
      asIso (DerivedCategory.Q.map R.ι') ≪≫ (DerivedCategory.quotientCompQhIso C).symm.app _)) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj L))).symm

/-- The `n`-th homology of `R⁺F` applied to `X` placed in degree `0` is `R^n F X`. -/
noncomputable def homologyRightDerivedFunctorPlusObjSingleFunctorIso (X : C) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor D n).obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X)) ≅
      (F.rightDerived n).obj X :=
  (DerivedCategory.Plus.homologyFunctor D n).mapIso
      (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ X) ≪≫
    DerivedCategory.Plus.homologyFunctorObjQIso _ n ≪≫
    ((injectiveResolution X).isoRightDerivedObjCochainComplex F n).symm

/-- The morphism `F(I) ⟶ F(J)` of complexes induced by a morphism of the chosen injective
resolutions `I` of `X` and `J` of `Y`. -/
noncomputable def rightDerivedPlusComplexMap {X Y : C} {f : X ⟶ Y}
    (φ : (injectiveResolution X).Hom (injectiveResolution Y) f) :
    F.rightDerivedPlusComplex X ⟶ F.rightDerivedPlusComplex Y :=
  ObjectProperty.homMk ((F.mapHomologicalComplex _).map φ.hom')

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `R⁺F(X[0]) ≅ F(I)` is compatible with morphisms of injective
resolutions. -/
lemma rightDerivedFunctorPlusObjSingleFunctorIsoQ_hom_naturality {X Y : C} {f : X ⟶ Y}
    (φ : (injectiveResolution X).Hom (injectiveResolution Y) f) :
    F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f) ≫
        (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ Y).hom =
      (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ X).hom ≫
        DerivedCategory.Plus.Q.map (F.rightDerivedPlusComplexMap φ) := by
  let LX : CochainComplex.Plus C := ⟨(injectiveResolution X).cochainComplex, 0, inferInstance⟩
  let LY : CochainComplex.Plus C := ⟨(injectiveResolution Y).cochainComplex, 0, inferInstance⟩
  let g : LX ⟶ LY := ObjectProperty.homMk φ.hom'
  have h₁ := F.rightDerivedFunctorPlusUnith.naturality
    ((HomotopyCategory.Plus.quotient C).map g)
  have h₂ : (DerivedCategory.Plus.singleFunctor C 0).map f ≫
      (DerivedCategory.Plus.ι.preimageIso (X := (DerivedCategory.Plus.singleFunctor C 0).obj Y)
        (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj LY))
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app Y ≪≫
          asIso (DerivedCategory.Q.map (injectiveResolution Y).ι') ≪≫
          (DerivedCategory.quotientCompQhIso C).symm.app _)).hom =
      (DerivedCategory.Plus.ι.preimageIso (X := (DerivedCategory.Plus.singleFunctor C 0).obj X)
        (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj LX))
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app X ≪≫
          asIso (DerivedCategory.Q.map (injectiveResolution X).ι') ≪≫
          (DerivedCategory.quotientCompQhIso C).symm.app _)).hom ≫
        DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map g) := by
    apply DerivedCategory.Plus.ι.map_injective
    have := (DerivedCategory.quotientCompQhIso C).inv.naturality φ.hom'
    simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
    dsimp at this ⊢
    change (DerivedCategory.singleFunctor C 0).map f ≫ _ =
      _ ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map φ.hom')
    rw [Category.assoc, Category.assoc, ← this,
      (DerivedCategory.singleFunctorIsoCompQ C 0).hom.naturality_assoc]
    simp only [Functor.comp_map, ← Functor.map_comp_assoc,
      InjectiveResolution.Hom.ι'_comp_hom']
  dsimp [rightDerivedFunctorPlusObjSingleFunctorIsoQ]
  rw [← F.rightDerivedFunctorPlus.map_comp_assoc, h₂, Functor.map_comp, Category.assoc,
    Category.assoc]
  congr 1
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
  exact h₁.symm

/-- The isomorphism `H^n(R⁺F(X[0])) ≅ R^n F X` is natural in `X`. -/
@[reassoc]
lemma homologyRightDerivedFunctorPlusObjSingleFunctorIso_hom_naturality {X Y : C} (f : X ⟶ Y)
    (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor D n).map
        (F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f)) ≫
      (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso Y n).hom =
    (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso X n).hom ≫ (F.rightDerived n).map f := by
  let φ : (injectiveResolution X).Hom (injectiveResolution Y) f :=
    ⟨InjectiveResolution.desc f _ _, by simp [InjectiveResolution.desc_commutes_zero]⟩
  simp only [homologyRightDerivedFunctorPlusObjSingleFunctorIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, rightDerivedFunctorPlusObjSingleFunctorIsoQ_hom_naturality F φ,
    Functor.map_comp, Category.assoc]
  congr 1
  have key := (injectiveResolution X).isoRightDerivedObjCochainComplex_inv_naturality φ F n
  have key₂ := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality
    (F.rightDerivedPlusComplexMap φ) n
  change _ ≫ (DerivedCategory.Plus.homologyFunctorObjQIso (F.rightDerivedPlusComplex Y) n).hom ≫
      ((injectiveResolution Y).isoRightDerivedObjCochainComplex F n).inv =
    (DerivedCategory.Plus.homologyFunctorObjQIso (F.rightDerivedPlusComplex X) n).hom ≫
      ((injectiveResolution X).isoRightDerivedObjCochainComplex F n).inv ≫ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key₂).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) key)))

/-- The isomorphism `H^n(R⁺F(X[0])) ≅ R^n F X` of
`Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso`, as a natural isomorphism of
functors `C ⥤ D`. -/
noncomputable def singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso (n : ℕ) :
    DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor D n ≅ F.rightDerived n :=
  NatIso.ofComponents (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso · n)
    (fun f ↦ F.homologyRightDerivedFunctorPlusObjSingleFunctorIso_hom_naturality f n)

end

end Functor

end CategoryTheory
