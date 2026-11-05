import Jacobian.AlgebraicGeometry.Cohomology.Flasque
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Jacobian.AlgebraicGeometry.Modules.RestrictPushforward
import Jacobian.AlgebraicGeometry.Modules.RestrictionLimits
import Jacobian.CategoryTheory.Abelian.RightDerived.Composition

/-!
# Higher direct images and open restriction

Higher direct images commute with restriction to an open subscheme of the base. Exact restriction sends injective modules to flasque modules, which are acyclic for pushforward.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules
variable {X T : Scheme.{u}}

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctor f).Additive where
  map_add := by intros; rfl

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (restrictFunctor f) :=
  PreservesLimitsOfSize.preservesFiniteLimits _

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteColimits (restrictFunctor f) :=
  PreservesColimitsOfSize.preservesFiniteColimits.{u, u} _

variable [HasInjectiveResolutions X.Modules]

section BaseChange

variable {T' X' : Scheme.{u}} {f : X ⟶ T} {g : T' ⟶ T} {g' : X' ⟶ X} {f' : X' ⟶ T'}

/-- In a cartesian square whose bottom arrow `g` is an open immersion, the top arrow `g'` is an
open immersion. -/
lemma isOpenImmersion_of_isPullback [IsOpenImmersion g] (sq : IsPullback g' f' f g) :
    IsOpenImmersion g' := by
  rw [← sq.isoPullback_hom_fst]
  infer_instance

variable [IsOpenImmersion g] [IsOpenImmersion g'] (sq : IsPullback g' f' f g)

/-- **The higher direct images commute with restriction to an open subscheme of the base**: in a
cartesian square whose bottom arrow `g` is an open immersion,
`R^q f'_* (g'^* ℱ) ≅ (R^q f_* ℱ)|_{T'}`.
Restriction to `X'` is exact and sends injective modules to flasque, hence `f'_*`-acyclic, ones,
restriction to `T'` is exact, and `f'_* ((-)|_{X'}) ≅ (f_* -)|_{T'}`. -/
noncomputable def higherDirectImagePullbackIsoRestrict (ℱ : X.Modules)
    [HasInjectiveResolutions X'.Modules] (q : ℕ) :
    (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ) ≅
      ((higherDirectImage f q).obj ℱ).restrict g :=
  (higherDirectImage f' q).mapIso ((restrictFunctorIsoPullback g').app ℱ).symm ≪≫
    (Functor.compRightDerivedObjIso (restrictFunctor g') (pushforward f')
      (fun I _ ↦ rightAcyclic_pushforward_of_isFlasque f' _
        (isFlasque_restrict g' _ (isFlasque_of_injective I))) q ℱ).symm ≪≫
    Functor.rightDerivedObjIsoOfIso (pushforwardRestrictIso sq).symm q ℱ ≪≫
    Functor.rightDerivedCompObjIso (pushforward f) (restrictFunctor g) q ℱ

end BaseChange

end AlgebraicGeometry.Scheme.Modules
