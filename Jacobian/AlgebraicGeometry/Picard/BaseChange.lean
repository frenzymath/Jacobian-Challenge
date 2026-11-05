import Jacobian.AlgebraicGeometry.Picard.Sheaf
import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Base change for relative Picard sheaves

A cartesian square of families induces a natural isomorphism of their
relative Picard presheaves and their fppf sheafifications. The isomorphism
acts on an invertible sheaf by pullback along the canonical fiber-product
isomorphism, so it is compatible with the map from Picard classes.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {X S : Scheme.{u}}

variable {X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- For a cartesian square exhibiting `f' : X' ⟶ S'` as the base change of `f : X ⟶ S` along
`g : S' ⟶ S` and a scheme `T` over `S'`, the fibre products `X' ×_{S'} T` and `X ×_S T` agree. -/
def pullbackIsoOfIsPullback (h : IsPullback g' f' f g) (T : Over S') :
    Limits.pullback f' T.hom ≅ Limits.pullback f (T.hom ≫ g) :=
  ((IsPullback.of_hasPullback f' T.hom).paste_horiz h).isoPullback

@[reassoc (attr := simp)]
lemma pullbackIsoOfIsPullback_hom_fst (h : IsPullback g' f' f g) (T : Over S') :
    (pullbackIsoOfIsPullback h T).hom ≫ Limits.pullback.fst f (T.hom ≫ g) =
      Limits.pullback.fst f' T.hom ≫ g' :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)]
lemma pullbackIsoOfIsPullback_hom_snd (h : IsPullback g' f' f g) (T : Over S') :
    (pullbackIsoOfIsPullback h T).hom ≫ Limits.pullback.snd f (T.hom ≫ g) =
      Limits.pullback.snd f' T.hom :=
  IsPullback.isoPullback_hom_snd _

@[reassoc]
lemma pullbackIsoOfIsPullback_hom_comp_baseChangeMap (h : IsPullback g' f' f g)
    {T T' : Over S'} (φ : T' ⟶ T) :
    (pullbackIsoOfIsPullback h T').hom ≫ baseChangeMap f ((Over.map g).map φ) =
      baseChangeMap f' φ ≫ (pullbackIsoOfIsPullback h T).hom := by
  apply Limits.pullback.hom_ext <;>
    simp [baseChangeMap]

/-- **The Picard presheaf is compatible with base change.** For a cartesian square exhibiting
`f' : X' ⟶ S'` as the base change of `f : X ⟶ S` along `g : S' ⟶ S`, the restriction of the
Picard presheaf of `f` to schemes over `S'` is the Picard presheaf of `f'`, through the
identifications `X' ×_{S'} T ≅ X ×_S T` (`AlgebraicGeometry.pullbackIsoOfIsPullback`). -/
def picardPresheafIsoOfIsPullback (h : IsPullback g' f' f g) :
    (Over.map g).op ⋙ picardPresheaf f ≅ picardPresheaf f' :=
  NatIso.ofComponents (fun T ↦ Equiv.toIso
    { toFun := Pic.map (pullbackIsoOfIsPullback h T.unop).hom
      invFun := Pic.map (pullbackIsoOfIsPullback h T.unop).inv
      left_inv L := by rw [← Pic.map_comp, Iso.inv_hom_id, Pic.map_id]
      right_inv L := by rw [← Pic.map_comp, Iso.hom_inv_id, Pic.map_id] })
    fun {T T'} φ ↦ by
      ext L
      exact (Pic.map_comp _ _ L).symm.trans ((congrArg (fun m ↦ Pic.map m L)
        (pullbackIsoOfIsPullback_hom_comp_baseChangeMap h φ.unop)).trans (Pic.map_comp _ _ L))

@[simp]
lemma picardPresheafIsoOfIsPullback_hom_app (h : IsPullback g' f' f g) (T : (Over S')ᵒᵖ)
    (L : (picardPresheaf f).obj ((Over.map g).op.obj T)) :
    (picardPresheafIsoOfIsPullback h).hom.app T L =
      Pic.map (pullbackIsoOfIsPullback h T.unop).hom L :=
  rfl

/-- Restricting the fppf sheafification of a presheaf `P` on schemes over `S` to schemes over
`S'`, along `g : S' ⟶ S`, gives the fppf sheafification of the restriction of `P`: the functor
`Over.map g` is continuous and cocontinuous for the fppf topologies. -/
def overMapOpCompSheafifyIso (g : S' ⟶ S) (P : (Over S)ᵒᵖ ⥤ Type (u + 1)) :
    (Over.map g).op ⋙ ((presheafToSheaf (Scheme.fppfTopology.over S) _).obj P).obj ≅
      ((presheafToSheaf (Scheme.fppfTopology.over S') _).obj ((Over.map g).op ⋙ P)).obj :=
  (sheafToPresheaf _ _).mapIso
    (((Over.map g).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
      (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).app P).symm

/-- The identification `AlgebraicGeometry.overMapOpCompSheafifyIso` is compatible with the maps
from the presheaves to their sheafifications. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_toSheafify_overMapOpCompSheafifyIso_hom (g : S' ⟶ S)
    (P : (Over S)ᵒᵖ ⥤ Type (u + 1)) :
    Functor.whiskerLeft (Over.map g).op (toSheafify (Scheme.fppfTopology.over S) P) ≫
        (overMapOpCompSheafifyIso g P).hom =
      toSheafify (Scheme.fppfTopology.over S') ((Over.map g).op ⋙ P) := by
  rw [overMapOpCompSheafifyIso, Functor.mapIso_symm, Iso.symm_hom, Iso.comp_inv_eq,
    Functor.mapIso_hom, Iso.app_hom]
  exact (Functor.toSheafify_pullbackSheafificationCompatibility (Over.map g) (Type (u + 1))
    (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S) P).symm

/-- **The Picard functor is compatible with base change**, as a canonical isomorphism. For a
cartesian square exhibiting `f' : X' ⟶ S'` as the base change of `f : X ⟶ S` along
`g : S' ⟶ S`, the restriction of `Pic_{X/S}` to schemes over `S'` is `Pic_{X'/S'}`, through the
identifications `X' ×_{S'} T ≅ X ×_S T` (`AlgebraicGeometry.pullbackIsoOfIsPullback`); see
`AlgebraicGeometry.picardFunctorIsoOfIsPullback_hom_app_toPicardFunctor`.
 -/
def picardFunctorIsoOfIsPullback (h : IsPullback g' f' f g) :
    (Over.map g).op ⋙ (picardFunctor f).obj ≅ (picardFunctor f').obj :=
  overMapOpCompSheafifyIso g (picardPresheaf f) ≪≫
    (sheafToPresheaf _ _).mapIso ((presheafToSheaf _ _).mapIso (picardPresheafIsoOfIsPullback h))

/-- The canonical isomorphism `AlgebraicGeometry.picardFunctorIsoOfIsPullback`, on presheaf
level: it is induced by the Picard presheaf identification
`AlgebraicGeometry.picardPresheafIsoOfIsPullback`. -/
@[reassoc]
lemma whiskerLeft_toPicardFunctor_picardFunctorIsoOfIsPullback_hom (h : IsPullback g' f' f g) :
    Functor.whiskerLeft (Over.map g).op (toPicardFunctor f) ≫
        (picardFunctorIsoOfIsPullback h).hom =
      (picardPresheafIsoOfIsPullback h).hom ≫ toPicardFunctor f' := by
  rw [picardFunctorIsoOfIsPullback, Iso.trans_hom,
    whiskerLeft_toSheafify_overMapOpCompSheafifyIso_hom_assoc, toSheafify_naturality,
    Functor.mapIso_hom, Functor.mapIso_hom]
  rfl

/-- **The canonical base change isomorphism on classes.** The isomorphism
`AlgebraicGeometry.picardFunctorIsoOfIsPullback` sends the class of an invertible module `ℒ` on
`X ×_S T` to the class of its pullback along `X' ×_{S'} T ≅ X ×_S T`.
 -/
lemma picardFunctorIsoOfIsPullback_hom_app_toPicardFunctor (h : IsPullback g' f' f g)
    (T : (Over S')ᵒᵖ) (L : (picardPresheaf f).obj ((Over.map g).op.obj T)) :
    (picardFunctorIsoOfIsPullback h).hom.app T ((toPicardFunctor f).app _ L) =
      (toPicardFunctor f').app T (Pic.map (pullbackIsoOfIsPullback h T.unop).hom L) := by
  have h' := NatTrans.congr_app (whiskerLeft_toPicardFunctor_picardFunctorIsoOfIsPullback_hom h) T
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h'
  rw [← picardPresheafIsoOfIsPullback_hom_app]
  rw [← ConcreteCategory.comp_apply, ← h', ConcreteCategory.comp_apply]
  rfl

end AlgebraicGeometry
