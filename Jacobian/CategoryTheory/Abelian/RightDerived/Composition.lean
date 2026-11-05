import Jacobian.CategoryTheory.Abelian.RightDerived.Resolution

/-!
# Exact functors and right derived composition

Exact postcomposition commutes with right derivation. Exact precomposition does as well when it sends injectives to acyclic objects.
-/

set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Right derived functors of composites

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has injective
resolutions.

* Isomorphic functors have isomorphic right derived functors
  (`CategoryTheory.Functor.rightDerivedObjIsoOfIso`).
* For an exact functor `G : D ⥤ D'`, `R^q (F ⋙ G) X ≅ G (R^q F X)`
  (`CategoryTheory.Functor.rightDerivedCompObjIso`).
* For an exact functor `E : C' ⥤ C` sending injective objects to `F`-acyclic objects,
  `R^q (E ⋙ F) X ≅ R^q F (E X)` (`CategoryTheory.Functor.compRightDerivedObjIso`): `E` sends an
  injective resolution of `X` to a resolution of `E X` by `F`-acyclic objects.
-/

section
namespace CategoryTheory.Functor

open Limits

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  [Abelian C] [Abelian C'] [Abelian D] [Abelian D'] [HasInjectiveResolutions C]
  [HasInjectiveResolutions C']

/-- Isomorphic functors have isomorphic right derived functors. -/
noncomputable def rightDerivedObjIsoOfIso {F F' : C ⥤ D} [F.Additive] [F'.Additive]
    (e : F ≅ F') (q : ℕ) (X : C) : (F.rightDerived q).obj X ≅ (F'.rightDerived q).obj X :=
  (injectiveResolution X).isoRightDerivedObj F q ≪≫
    (HomologicalComplex.homologyFunctor D _ q).mapIso
      ((NatIso.mapHomologicalComplex e _).app _) ≪≫
    ((injectiveResolution X).isoRightDerivedObj F' q).symm

/-- **Right derived functors of a composite with an exact functor.** For an additive functor
`F : C ⥤ D` and an exact functor `G : D ⥤ D'`, `R^q (F ⋙ G) X ≅ G (R^q F X)`: both are computed
from an injective resolution `I` of `X`, and `G` commutes with taking cohomology of `F I`. -/
noncomputable def rightDerivedCompObjIso (F : C ⥤ D) (G : D ⥤ D') [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (q : ℕ) (X : C) :
    ((F ⋙ G).rightDerived q).obj X ≅ G.obj ((F.rightDerived q).obj X) :=
  (injectiveResolution X).isoRightDerivedObj (F ⋙ G) q ≪≫
    (HomologicalComplex.homologyFunctor D' _ q).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) _).symm.app _) ≪≫
    (((F.mapHomologicalComplex _).obj (injectiveResolution X).cocomplex).sc q).mapHomologyIso G ≪≫
    G.mapIso ((injectiveResolution X).isoRightDerivedObj F q).symm

/-- An exact functor sends a resolution `X ⟶ I` to a resolution `E X ⟶ E I`. -/
noncomputable def mapResolution (E : C' ⥤ C) [E.Additive] {X : C'} {K : CochainComplex C' ℕ}
    (ι : (CochainComplex.single₀ C').obj X ⟶ K) :
    (CochainComplex.single₀ C).obj (E.obj X) ⟶ (E.mapHomologicalComplex _).obj K :=
  (HomologicalComplex.singleMapHomologicalComplex E _ 0).inv.app X ≫
    (E.mapHomologicalComplex _).map ι

instance quasiIso_mapResolution (E : C' ⥤ C) [E.Additive] [PreservesFiniteLimits E]
    [PreservesFiniteColimits E] {X : C'} {K : CochainComplex C' ℕ}
    (ι : (CochainComplex.single₀ C').obj X ⟶ K) [QuasiIso ι] : QuasiIso (E.mapResolution ι) := by
  unfold mapResolution
  infer_instance

/-- **Right derived functors of a composite with an exact functor preserving acyclicity.** Let
`E : C' ⥤ C` be an exact functor sending injective objects to `F`-acyclic objects, for a left exact
`F : C ⥤ D`. Then `R^q (E ⋙ F) X ≅ R^q F (E X)`: an injective resolution `I` of `X` computes the
left side, and `E I` is a resolution of `E X` by `F`-acyclic objects, which computes the right
side. -/
noncomputable def compRightDerivedObjIso (E : C' ⥤ C) (F : C ⥤ D) [E.Additive] [F.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E] [PreservesFiniteLimits F]
    (hE : ∀ (I : C') [Injective I], F.rightAcyclic (E.obj I)) (q : ℕ) (X : C') :
    ((E ⋙ F).rightDerived q).obj X ≅ (F.rightDerived q).obj (E.obj X) :=
  (injectiveResolution X).isoRightDerivedObj (E ⋙ F) q ≪≫
    (HomologicalComplex.homologyFunctor D _ q).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ F)) _).symm.app _) ≪≫
    (F.rightDerivedObjIsoOfResolution (E.mapResolution (injectiveResolution X).ι)
      (fun n ↦ hE ((injectiveResolution X).cocomplex.X n)) q).symm

end CategoryTheory.Functor
