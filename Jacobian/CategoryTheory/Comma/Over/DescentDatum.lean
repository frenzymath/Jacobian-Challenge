import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Yoneda

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Descent data for objects over a base, and the canonical descent datum of a representing object

Let `baseMap : source ⟶ target` be a morphism in a category `CategoryType` and let `representation` be an object over `source`. Classically, a
descent datum on `representation` relative to `baseMap` is an isomorphism `φ : pr₀^* representation ≅ pr₁^* representation` over `source ×_Y source`
satisfying the cocycle condition over `source ×_Y source ×_Y source`. By the Yoneda lemma this is the same as a
*transport* of points: for every object `test` and every pair of morphisms `f₁ f₂ : test ⟶ source` with
`f₁ ≫ baseMap = f₂ ≫ baseMap`, a bijection between the `test`-points of `representation` lying over `f₁` and those lying over
`f₂`, natural in `test`, trivial for `f₁ = f₂` and compatible with composition. This file uses the
transport form, `CategoryTheory.Over.DescentDatum`, which needs neither fibre products nor the
canonical isomorphisms between iterated pullbacks.

If `presheaf` is a presheaf on `Over target` and `representation` represents the restriction of `presheaf` to `Over source`, then `representation`
carries a canonical descent datum: the two pullbacks of `representation` to `source ×_Y source` represent the same
restriction of `presheaf`, and the datum is the comparison isomorphism between them. In transport form
it reads: a point of `representation` over `f₁` corresponds to an element of `presheaf(test)`, and so does a point of `representation`
over `f₂`, because `f₁` and `f₂` define the same object of `Over target`.

## Main definitions

- `CategoryTheory.Over.DescentDatum`: a descent datum on `representation : Over source` relative to `baseMap : source ⟶ target`.
- `CategoryTheory.Over.DescentDatum.IsEffective`: the datum comes from an object over `target`.
- `CategoryTheory.Over.DescentDatum.IsBaseChange`: a descent datum is the base change of
  another one.
- `CategoryTheory.Functor.RepresentableBy.overDescentDatum`: the canonical descent datum on an
  object representing the restriction of a presheaf to `Over source`.

## Main statements

- `CategoryTheory.Functor.RepresentableBy.overTransport_overTransport`: the cocycle condition for
  the canonical descent datum.
-/

section
universe valueUniverse homUniverse categoryUniverse

namespace CategoryTheory

open Limits

namespace Over

variable {CategoryType : Type categoryUniverse} [Category.{homUniverse} CategoryType] {source target : CategoryType} (baseMap : source ⟶ target)

/-- A **descent datum** on an object `representation` over `source` relative to `baseMap : source ⟶ target`, in transport form: for
every pair of `test`-points `f₁ f₂ : test ⟶ source` with the same image in `target`, a map sending the `test`-points
of `representation` lying over `f₁` to `test`-points of `representation` lying over `f₂`. It is natural in `test`, trivial when
`f₁ = f₂`, and satisfies the cocycle condition; in particular each transport map is a bijection.

By the Yoneda lemma this is the same as an isomorphism `φ : pr₀^* representation ≅ pr₁^* representation` over `source ×_Y source`
satisfying `pr₀₂^* φ = pr₁₂^* φ ∘ pr₀₁^* φ` over `source ×_Y source ×_Y source` (Stacks 023V): `φ` is the
transport for the universal pair `pr₀, pr₁`.

Mathlib's `CategoryTheory.Pseudofunctor.DescentData` is the same transport-style notion for a
pseudofunctor `presheaf` on `CategoryType`: its `hom` compares the pullbacks of the object along any two morphisms
`test ⟶ source` with the same composite to `target`. It is not used here because there is no pullback
pseudofunctor `source ↦ Over source` available, and the points of `representation` are what the descent arguments
below manipulate. -/
structure DescentDatum (representation : Over source) where
  /-- The transport of points of `representation` over `f₁` to points of `representation` over `f₂`. -/
  transport {test : CategoryType} (f₁ f₂ : test ⟶ source) (equality : f₁ ≫ baseMap = f₂ ≫ baseMap) : (Over.mk f₁ ⟶ representation) → (Over.mk f₂ ⟶ representation)
  /-- The transport is natural in `test`. -/
  transport_homMk_comp {test test' : CategoryType} (comparison : test' ⟶ test) (f₁ f₂ : test ⟶ source) (equality : f₁ ≫ baseMap = f₂ ≫ baseMap)
    (point : Over.mk f₁ ⟶ representation) :
    transport (comparison ≫ f₁) (comparison ≫ f₂) (by rw [Category.assoc, Category.assoc, equality])
      ((Over.homMk comparison : Over.mk (comparison ≫ f₁) ⟶ Over.mk f₁) ≫ point) =
      (Over.homMk comparison : Over.mk (comparison ≫ f₂) ⟶ Over.mk f₂) ≫ transport f₁ f₂ equality point
  /-- The transport along a pair of equal points is the identity. -/
  transport_self {test : CategoryType} (map : test ⟶ source) (point : Over.mk map ⟶ representation) : transport map map rfl point = point
  /-- The cocycle condition. -/
  transport_transport {test : CategoryType} (f₁ f₂ f₃ : test ⟶ source) (h₁₂ : f₁ ≫ baseMap = f₂ ≫ baseMap)
    (h₂₃ : f₂ ≫ baseMap = f₃ ≫ baseMap) (point : Over.mk f₁ ⟶ representation) :
    transport f₂ f₃ h₂₃ (transport f₁ f₂ h₁₂ point) = transport f₁ f₃ (h₁₂.trans h₂₃) point

namespace DescentDatum

variable {baseMap} {representation : Over source}

/-- A descent datum on `representation` relative to `baseMap : source ⟶ target` is **effective** if `representation` is the pullback along
`baseMap` of an object `descendedObject` over `target`, through a morphism `descentMap : representation ⟶ descendedObject` which is invariant under the
transport. Equivalently, `representation ≅ descendedObject ×_Y source` over `source` and the datum is the one induced by `descendedObject`. -/
def IsEffective (datum : DescentDatum baseMap representation) : Prop :=
  ∃ (descendedObject : Over target) (descentMap : representation.left ⟶ descendedObject.left), IsPullback descentMap representation.hom descendedObject.hom baseMap ∧
    ∀ {test : CategoryType} (f₁ f₂ : test ⟶ source) (equality : f₁ ≫ baseMap = f₂ ≫ baseMap) (point : Over.mk f₁ ⟶ representation),
      (datum.transport f₁ f₂ equality point).left ≫ descentMap = point.left ≫ descentMap

/-- The transport of a descent datum only depends on the underlying morphisms. -/
lemma transport_left_congr (datum : DescentDatum baseMap representation) {test : CategoryType} {f₁ f₂ f₁' f₂' : test ⟶ source}
    (equality : f₁ ≫ baseMap = f₂ ≫ baseMap) (equality' : f₁' ≫ baseMap = f₂' ≫ baseMap) (point : Over.mk f₁ ⟶ representation)
    (point' : Over.mk f₁' ⟶ representation) (e₁ : f₁ = f₁') (e₂ : f₂ = f₂') (ea : point.left = point'.left) :
    (datum.transport f₁ f₂ equality point).left = (datum.transport f₁' f₂' equality' point').left := by
  subst e₁ e₂
  obtain rfl : point = point' := Over.OverMorphism.ext ea
  rfl

section Universal

variable [HasPullback (representation.hom ≫ baseMap) baseMap]

/-- The universal point for a descent datum on `representation`: the first projection
`representation ×_Y source ⟶ representation`, a point of `representation` over `representation ×_Y source ⟶ representation ⟶ source`. -/
noncomputable abbrev universalPoint :
    Over.mk (pullback.fst (representation.hom ≫ baseMap) baseMap ≫ representation.hom) ⟶ representation :=
  Over.homMk (pullback.fst (representation.hom ≫ baseMap) baseMap) rfl

/-- The morphism `φ : representation ×_Y source ⟶ representation` over `source` underlying a descent datum on `representation`: the transport of
the universal point. -/
noncomputable def toHom (datum : DescentDatum baseMap representation) : Limits.pullback (representation.hom ≫ baseMap) baseMap ⟶ representation.left :=
  (datum.transport _ (pullback.snd (representation.hom ≫ baseMap) baseMap) (by rw [Category.assoc, pullback.condition])
    universalPoint).left

/-- **A descent datum is determined by its morphism `φ : representation ×_Y source ⟶ representation`.** The transport of a
point `point` of `representation` over `f₁` to `f₂` is `(point, f₂) ≫ φ`, by naturality of the transport. -/
lemma transport_left_eq_lift_toHom (datum : DescentDatum baseMap representation) {test : CategoryType} (f₁ f₂ : test ⟶ source)
    (equality : f₁ ≫ baseMap = f₂ ≫ baseMap) (point : Over.mk f₁ ⟶ representation) :
    (datum.transport f₁ f₂ equality point).left =
      pullback.lift point.left f₂ (by rw [← Category.assoc, Over.w point]; exact equality) ≫ datum.toHom := by
  let comparison : test ⟶ Limits.pullback (representation.hom ≫ baseMap) baseMap :=
    pullback.lift point.left f₂ (by rw [← Category.assoc, Over.w point]; exact equality)
  have key := datum.transport_homMk_comp comparison _ (pullback.snd (representation.hom ≫ baseMap) baseMap)
    (by rw [Category.assoc, pullback.condition]) universalPoint
  have e₁ : f₁ = comparison ≫ pullback.fst (representation.hom ≫ baseMap) baseMap ≫ representation.hom := by
    rw [pullback.lift_fst_assoc]; exact (Over.w point).symm
  have e₂ : f₂ = comparison ≫ pullback.snd (representation.hom ≫ baseMap) baseMap := (pullback.lift_snd _ _ _).symm
  rw [datum.transport_left_congr equality (by rw [← e₁, ← e₂]; exact equality) point
    ((Over.homMk comparison rfl : Over.mk (comparison ≫ pullback.fst (representation.hom ≫ baseMap) baseMap ≫ representation.hom) ⟶
      Over.mk (pullback.fst (representation.hom ≫ baseMap) baseMap ≫ representation.hom)) ≫ universalPoint)
    e₁ e₂ (by simp [comparison]), key]
  rfl

/-- Two descent data on `representation` with the same morphism `representation ×_Y source ⟶ representation` have the same transport. -/
lemma transport_eq_of_toHom_eq {datum secondDatum : DescentDatum baseMap representation} (hDE : datum.toHom = secondDatum.toHom) {test : CategoryType}
    (f₁ f₂ : test ⟶ source) (equality : f₁ ≫ baseMap = f₂ ≫ baseMap) (point : Over.mk f₁ ⟶ representation) :
    datum.transport f₁ f₂ equality point = secondDatum.transport f₁ f₂ equality point :=
  Over.OverMorphism.ext (by
    rw [transport_left_eq_lift_toHom, transport_left_eq_lift_toHom, hDE])

end Universal

/-- A descent datum `datum` on `representation` relative to `baseMap : source ⟶ target` **base changes** to a descent datum `secondDatum` on
`representation'` relative to `baseMap' = ι ≫ baseMap : source' ⟶ target`, through a morphism `descentMap : representation' ⟶ representation` over `ι : source' ⟶ source`, if
transporting a point `point` of `representation'` by `secondDatum` and then mapping it to `representation` by `descentMap` is the same as mapping
`point` to `representation` and transporting it by `datum`:
```
  representation'(f₁) --secondDatum--> representation'(f₂)
    |             |
    descentMap             descentMap
    homUniverse             homUniverse
  representation(f₁ ≫ ι) --datum--> representation(f₂ ≫ ι)
```
When `q` exhibits `V'` as `V ×_X X'`, this says that `E` is the pullback of `D` along `ι`. -/
def IsBaseChange {source' : CategoryType} {ι : source' ⟶ source} {baseMap' : source' ⟶ target} (hp : ι ≫ baseMap = baseMap') {representation' : Over source'}
    {descentMap : representation'.left ⟶ representation.left} (hq : descentMap ≫ representation.hom = representation'.hom ≫ ι) (datum : DescentDatum baseMap representation)
    (secondDatum : DescentDatum baseMap' representation') : Prop :=
  ∀ ⦃test : CategoryType⦄ (f₁ f₂ : test ⟶ source') (equality : f₁ ≫ baseMap' = f₂ ≫ baseMap') (point : Over.mk f₁ ⟶ representation'),
    (datum.transport (f₁ ≫ ι) (f₂ ≫ ι) (by rw [Category.assoc, Category.assoc, hp, equality])
      (Over.homMk (point.left ≫ descentMap) (by simp [hq]))).left = (secondDatum.transport f₁ f₂ equality point).left ≫ descentMap

end DescentDatum

end Over

namespace Functor.RepresentableBy

variable {CategoryType : Type categoryUniverse} [Category.{homUniverse} CategoryType] {source target : CategoryType} {baseMap : source ⟶ target} {presheaf : (Over target)ᵒᵖ ⥤ Type valueUniverse}
  {representation : Over source} (representability : ((Over.map baseMap).op ⋙ presheaf).RepresentableBy representation)

/-- The identity of `test`, viewed as a morphism `(test, f₂ ≫ baseMap) ⟶ (test, f₁ ≫ baseMap)` in `Over target`. -/
abbrev overMapHomMkId {test : CategoryType} (f₁ f₂ : test ⟶ source) (equality : f₁ ≫ baseMap = f₂ ≫ baseMap) :
    (Over.map baseMap).obj (Over.mk f₂) ⟶ (Over.map baseMap).obj (Over.mk f₁) :=
  Over.homMk (𝟙 test) (by simp [equality])

/-- The transport of the canonical descent datum of a representing object: a point of `representation` over
`f₁` is an element of `presheaf(test, f₁ ≫ baseMap)`, and `(test, f₁ ≫ baseMap) = (test, f₂ ≫ baseMap)` in `Over target`, so it is
also a point of `representation` over `f₂`. -/
def overTransport {test : CategoryType} (f₁ f₂ : test ⟶ source) (equality : f₁ ≫ baseMap = f₂ ≫ baseMap) (point : Over.mk f₁ ⟶ representation) :
    Over.mk f₂ ⟶ representation :=
  representability.homEquiv.symm (presheaf.map (overMapHomMkId f₁ f₂ equality).op (representability.homEquiv point))

lemma homEquiv_overTransport {test : CategoryType} (f₁ f₂ : test ⟶ source) (equality : f₁ ≫ baseMap = f₂ ≫ baseMap)
    (point : Over.mk f₁ ⟶ representation) :
    representability.homEquiv (representability.overTransport f₁ f₂ equality point) = presheaf.map (overMapHomMkId f₁ f₂ equality).op (representability.homEquiv point) :=
  representability.homEquiv.apply_symm_apply _

/-- The transport of the canonical descent datum is natural in `test`: for `comparison : test' ⟶ test`, the square
```
  representation(f₁)     --transport-->  representation(f₂)
    | comparison^*                     | comparison^*
    homUniverse                         homUniverse
  representation(comparison ≫ f₁) --transport-->  representation(comparison ≫ f₂)
```
commutes, where `V(f)` denotes the points of `V` over `f`. -/
lemma overTransport_homMk_comp {test test' : CategoryType} (comparison : test' ⟶ test) (f₁ f₂ : test ⟶ source) (equality : f₁ ≫ baseMap = f₂ ≫ baseMap)
    (point : Over.mk f₁ ⟶ representation) :
    representability.overTransport (comparison ≫ f₁) (comparison ≫ f₂) (by rw [Category.assoc, Category.assoc, equality])
      ((Over.homMk comparison : Over.mk (comparison ≫ f₁) ⟶ Over.mk f₁) ≫ point) =
      (Over.homMk comparison : Over.mk (comparison ≫ f₂) ⟶ Over.mk f₂) ≫ representability.overTransport f₁ f₂ equality point := by
  have equivalence : overMapHomMkId (comparison ≫ f₁) (comparison ≫ f₂) (by rw [Category.assoc, Category.assoc, equality]) ≫
      (Over.map baseMap).map (Over.homMk comparison : Over.mk (comparison ≫ f₁) ⟶ Over.mk f₁) =
      (Over.map baseMap).map (Over.homMk comparison : Over.mk (comparison ≫ f₂) ⟶ Over.mk f₂) ≫
        overMapHomMkId f₁ f₂ equality := by
    ext
    simp
  rw [overTransport, overTransport, representability.comp_homEquiv_symm, representability.homEquiv_comp]
  congr 1
  have equivalence' := ConcreteCategory.congr_hom (congrArg (fun φ ↦ presheaf.map φ.op) equivalence) (representability.homEquiv point)
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at equivalence'
  exact equivalence'

lemma overTransport_self {test : CategoryType} (map : test ⟶ source) (point : Over.mk map ⟶ representation) :
    representability.overTransport map map rfl point = point := by
  have : overMapHomMkId (baseMap := baseMap) map map rfl = 𝟙 _ := by ext; simp
  rw [overTransport, this, op_id, Functor.map_id_apply]
  exact representability.homEquiv.symm_apply_apply point

/-- **The cocycle condition is automatic** for the canonical descent datum of a representing
object: both sides are the transport of an element of `presheaf(test)` along the identity of `test`. The
triangle
```
  representation(f₁) --transport--> representation(f₂)
       \                 |
    transport        transport
          \              homUniverse
           ----------> representation(f₃)
```
commutes, where `V(f)` denotes the points of `V` over `f`. -/
theorem overTransport_overTransport {test : CategoryType} (f₁ f₂ f₃ : test ⟶ source) (h₁₂ : f₁ ≫ baseMap = f₂ ≫ baseMap)
    (h₂₃ : f₂ ≫ baseMap = f₃ ≫ baseMap) (point : Over.mk f₁ ⟶ representation) :
    representability.overTransport f₂ f₃ h₂₃ (representability.overTransport f₁ f₂ h₁₂ point) =
      representability.overTransport f₁ f₃ (h₁₂.trans h₂₃) point := by
  have equivalence : overMapHomMkId f₂ f₃ h₂₃ ≫ overMapHomMkId f₁ f₂ h₁₂ =
      overMapHomMkId f₁ f₃ (h₁₂.trans h₂₃) := by
    ext
    simp
  have equivalence' := ConcreteCategory.congr_hom (congrArg (fun φ ↦ presheaf.map φ.op) equivalence) (representability.homEquiv point)
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at equivalence'
  unfold overTransport
  congr 1
  exact (congrArg (presheaf.map (overMapHomMkId f₂ f₃ h₂₃).op) (representability.homEquiv.apply_symm_apply _)).trans equivalence'

/-- **The canonical descent datum.** If `representation` represents the restriction `(Over.map baseMap).op ⋙ presheaf` of a
presheaf `presheaf` on `Over target` to `Over source`, then `representation` carries a canonical descent datum relative to
`baseMap : source ⟶ target`: the two pullbacks of `representation` to `source ×_Y source` represent the same restriction of `presheaf`, and the
datum is the unique isomorphism between them compatible with the representations. No choice is
involved, which is what makes the datum canonical. -/
def overDescentDatum : Over.DescentDatum baseMap representation where
  transport := representability.overTransport
  transport_homMk_comp := representability.overTransport_homMk_comp
  transport_self := representability.overTransport_self
  transport_transport := representability.overTransport_overTransport

@[simp]
lemma overDescentDatum_transport {test : CategoryType} (f₁ f₂ : test ⟶ source) (equality : f₁ ≫ baseMap = f₂ ≫ baseMap)
    (point : Over.mk f₁ ⟶ representation) :
    representability.overDescentDatum.transport f₁ f₂ equality point = representability.overTransport f₁ f₂ equality point :=
  rfl

end Functor.RepresentableBy

end CategoryTheory
