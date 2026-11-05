import Jacobian.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Restricting scheme descent data to invariant open subschemes

An open subscheme is invariant if point transport preserves its underlying
open set. This condition can be checked on the universal transport morphism.
The transport then restricts to the open subscheme and satisfies the same
naturality and cocycle identities. This is the local input for gluing
effective scheme descent.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

variable {source base : Scheme.{u}} {baseMap : source ⟶ base}
  {representation : Over source} (datum : DescentDatum baseMap representation)

private theorem transport_left_comp {test otherTest : Scheme.{u}}
    (comparison : test ⟶ otherTest) (firstMap secondMap : otherTest ⟶ source)
    (equality : firstMap ≫ baseMap = secondMap ≫ baseMap)
    (otherPoint : Over.mk firstMap ⟶ representation)
    {restrictedFirst restrictedSecond : test ⟶ source}
    (restrictedEquality : restrictedFirst ≫ baseMap = restrictedSecond ≫ baseMap)
    (first_eq : restrictedFirst = comparison ≫ firstMap)
    (second_eq : restrictedSecond = comparison ≫ secondMap)
    (point : Over.mk restrictedFirst ⟶ representation)
    (point_eq : point.left = comparison ≫ otherPoint.left) :
    (datum.transport restrictedFirst restrictedSecond restrictedEquality point).left =
      comparison ≫ (datum.transport firstMap secondMap equality otherPoint).left := by
  subst first_eq second_eq
  obtain rfl : point = (Over.homMk comparison :
      Over.mk (comparison ≫ firstMap) ⟶ Over.mk firstMap) ≫ otherPoint := by
    ext
    simpa using point_eq
  rw [datum.transport_homMk_comp comparison firstMap secondMap equality otherPoint]
  rfl

/-- The universal transport is a morphism over the second base projection. -/
@[reassoc (attr := simp)]
theorem toHom_comp_hom :
    datum.toHom ≫ representation.hom = pullback.snd (representation.hom ≫ baseMap) baseMap :=
  Over.w (datum.transport _ _ _ _)

/-- The universal transport restricts to the identity on the diagonal. -/
@[reassoc (attr := simp)]
theorem lift_toHom :
    pullback.lift (𝟙 representation.left) representation.hom (by simp) ≫ datum.toHom =
      𝟙 representation.left := by
  have identityTransport := datum.transport_left_eq_lift_toHom
    representation.hom representation.hom rfl (𝟙 _)
  rw [datum.transport_self] at identityTransport
  exact identityTransport.symm

/-- Point transport preserves an invariant open subset. -/
def IsInvariant (openSubset : representation.left.Opens) : Prop :=
  ∀ ⦃test : Scheme.{u}⦄ (firstMap secondMap : test ⟶ source)
    (equality : firstMap ≫ baseMap = secondMap ≫ baseMap)
    (point : Over.mk firstMap ⟶ representation),
    Set.range point.left ⊆ openSubset →
      Set.range (datum.transport firstMap secondMap equality point).left ⊆ openSubset

/-- Invariance is equivalent to preservation by the universal transport. -/
theorem isInvariant_iff (openSubset : representation.left.Opens) :
    datum.IsInvariant openSubset ↔ ∀ point,
      pullback.fst (representation.hom ≫ baseMap) baseMap point ∈ openSubset →
        datum.toHom point ∈ openSubset := by
  refine ⟨fun invariant point point_mem ↦ ?_,
    fun invariant test firstMap secondMap equality point point_mem ↦ ?_⟩
  · let preimageOpen := (pullback.fst (representation.hom ≫ baseMap) baseMap) ⁻¹ᵁ openSubset
    have restricted := invariant
      (preimageOpen.ι ≫ pullback.fst _ _ ≫ representation.hom)
      (preimageOpen.ι ≫ pullback.snd _ _)
      (by rw [Category.assoc, Category.assoc, Category.assoc, pullback.condition])
      (Over.homMk (preimageOpen.ι ≫ pullback.fst _ _) (by simp)) (by
        rintro _ ⟨preimagePoint, rfl⟩
        exact preimagePoint.2)
    have transport_eq := datum.transport_left_comp
      (restrictedFirst := preimageOpen.ι ≫ pullback.fst _ _ ≫ representation.hom)
      (restrictedSecond := preimageOpen.ι ≫ pullback.snd _ _)
      preimageOpen.ι
      (pullback.fst (representation.hom ≫ baseMap) baseMap ≫ representation.hom)
      (pullback.snd (representation.hom ≫ baseMap) baseMap)
      (by rw [Category.assoc, pullback.condition]) universalPoint
      (by simp only [Category.assoc, pullback.condition])
      rfl rfl
      (Over.homMk (preimageOpen.ι ≫ pullback.fst _ _) rfl) rfl
    change _ = preimageOpen.ι ≫ datum.toHom at transport_eq
    rw [transport_eq] at restricted
    exact restricted ⟨⟨point, point_mem⟩, rfl⟩
  · rw [datum.transport_left_eq_lift_toHom]
    rintro _ ⟨testPoint, rfl⟩
    apply invariant
    have membership := point_mem ⟨testPoint, rfl⟩
    rwa [← pullback.lift_fst point.left secondMap
      (by rw [← Category.assoc, Over.w point]; exact equality), Scheme.Hom.comp_apply] at membership

theorem isInvariant_top : datum.IsInvariant ⊤ := fun _ _ _ _ _ _ ↦ by simp

theorem IsInvariant.inf {firstOpen secondOpen : representation.left.Opens}
    (firstInvariant : datum.IsInvariant firstOpen)
    (secondInvariant : datum.IsInvariant secondOpen) :
    datum.IsInvariant (firstOpen ⊓ secondOpen) := fun _ firstMap secondMap equality point point_mem ↦
  Set.subset_inter
    (firstInvariant firstMap secondMap equality point (point_mem.trans Set.inter_subset_left))
    (secondInvariant firstMap secondMap equality point (point_mem.trans Set.inter_subset_right))

variable {datum}

/-- Restrict point transport to an invariant open subscheme. -/
def restrictTransport {openSubset : representation.left.Opens}
    (invariant : datum.IsInvariant openSubset) {test : Scheme.{u}}
    (firstMap secondMap : test ⟶ source)
    (equality : firstMap ≫ baseMap = secondMap ≫ baseMap)
    (point : Over.mk firstMap ⟶ Over.mk (openSubset.ι ≫ representation.hom)) : test ⟶ openSubset :=
  IsOpenImmersion.lift openSubset.ι
    (datum.transport firstMap secondMap equality
      (Over.homMk (point.left ≫ openSubset.ι) (by simpa using Over.w point))).left (by
        rw [Scheme.Opens.range_ι]
        refine invariant _ _ _ _ ?_
        rintro _ ⟨testPoint, rfl⟩
        exact (point.left testPoint).2)

@[reassoc (attr := simp)]
theorem restrictTransport_ι {openSubset : representation.left.Opens}
    (invariant : datum.IsInvariant openSubset) {test : Scheme.{u}}
    (firstMap secondMap : test ⟶ source)
    (equality : firstMap ≫ baseMap = secondMap ≫ baseMap)
    (point : Over.mk firstMap ⟶ Over.mk (openSubset.ι ≫ representation.hom)) :
    restrictTransport invariant firstMap secondMap equality point ≫ openSubset.ι =
      (datum.transport firstMap secondMap equality
        (Over.homMk (point.left ≫ openSubset.ι) (by simpa using Over.w point))).left :=
  IsOpenImmersion.lift_fac _ _ _

/-- Restricted transport is still a point over the target base map. -/
def restrictTransportHom {openSubset : representation.left.Opens}
    (invariant : datum.IsInvariant openSubset) {test : Scheme.{u}}
    (firstMap secondMap : test ⟶ source)
    (equality : firstMap ≫ baseMap = secondMap ≫ baseMap)
    (point : Over.mk firstMap ⟶ Over.mk (openSubset.ι ≫ representation.hom)) :
    Over.mk secondMap ⟶ Over.mk (openSubset.ι ≫ representation.hom) :=
  Over.homMk (restrictTransport invariant firstMap secondMap equality point) (by
    simp only [Over.mk_hom]
    rw [← Category.assoc, restrictTransport_ι]
    exact Over.w (datum.transport _ _ _ _))

@[reassoc (attr := simp)]
theorem restrictTransportHom_left_ι {openSubset : representation.left.Opens}
    (invariant : datum.IsInvariant openSubset) {test : Scheme.{u}}
    (firstMap secondMap : test ⟶ source)
    (equality : firstMap ≫ baseMap = secondMap ≫ baseMap)
    (point : Over.mk firstMap ⟶ Over.mk (openSubset.ι ≫ representation.hom)) :
    (restrictTransportHom invariant firstMap secondMap equality point).left ≫ openSubset.ι =
      (datum.transport firstMap secondMap equality
        (Over.homMk (point.left ≫ openSubset.ι) (by simpa using Over.w point))).left :=
  restrictTransport_ι invariant firstMap secondMap equality point

variable (datum) in
/-- Restrict a scheme descent datum to an invariant open subscheme. -/
def restrict (openSubset : representation.left.Opens) (invariant : datum.IsInvariant openSubset) :
    DescentDatum baseMap (Over.mk (openSubset.ι ≫ representation.hom)) where
  transport := restrictTransportHom invariant
  transport_homMk_comp comparison firstMap secondMap equality point := by
    refine Over.OverMorphism.ext ((cancel_mono openSubset.ι).mp ?_)
    refine (restrictTransportHom_left_ι invariant _ _ _ _).trans
      ((datum.transport_left_comp comparison firstMap secondMap equality
        (Over.homMk (point.left ≫ openSubset.ι) (by simpa using Over.w point))
        _ rfl rfl _ (by simp)).trans ?_)
    simp only [Over.comp_left, Category.assoc, restrictTransportHom_left_ι, Over.homMk_left]
  transport_self basePoint point := by
    refine Over.OverMorphism.ext ((cancel_mono openSubset.ι).mp ?_)
    refine (restrictTransportHom_left_ι invariant _ _ _ _).trans ?_
    rw [datum.transport_self]
    rfl
  transport_transport firstMap secondMap thirdMap first_eq second_eq point := by
    refine Over.OverMorphism.ext ((cancel_mono openSubset.ι).mp ?_)
    refine (restrictTransportHom_left_ι invariant _ _ _ _).trans ?_
    refine (datum.transport_left_congr second_eq second_eq _
      (datum.transport firstMap secondMap first_eq
        (Over.homMk (point.left ≫ openSubset.ι) (by simpa using Over.w point)))
      rfl rfl (restrictTransportHom_left_ι invariant firstMap secondMap first_eq point)).trans ?_
    rw [datum.transport_transport, restrictTransportHom_left_ι]

@[reassoc (attr := simp)]
theorem restrict_transport_left_ι (openSubset : representation.left.Opens)
    (invariant : datum.IsInvariant openSubset) {test : Scheme.{u}}
    (firstMap secondMap : test ⟶ source)
    (equality : firstMap ≫ baseMap = secondMap ≫ baseMap)
    (point : Over.mk firstMap ⟶ Over.mk (openSubset.ι ≫ representation.hom)) :
    ((datum.restrict openSubset invariant).transport firstMap secondMap equality point).left ≫
        openSubset.ι =
      (datum.transport firstMap secondMap equality
        (Over.homMk (point.left ≫ openSubset.ι) (by simpa using Over.w point))).left :=
  restrictTransportHom_left_ι invariant firstMap secondMap equality point

end CategoryTheory.Over.DescentDatum
