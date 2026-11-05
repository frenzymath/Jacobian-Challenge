import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Sheaves under a homeomorphism

Direct image along a homeomorphism is an equivalence. Its inverse-image
adjunction is therefore an adjoint equivalence as well.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf

variable (C : Type v) [Category.{w} C] {X Y : TopCat.{u}}

/-- Direct images along the two directions of a homeomorphism are inverse. -/
def pushforwardEquivalence (e : X ≅ Y) : X.Sheaf C ≌ Y.Sheaf C :=
  letI : (Opens.map e.hom).IsContinuous
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) := inferInstance
  letI : (Opens.map e.inv).IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) := inferInstance
  letI : (Opens.mapMapIso e).functor.IsContinuous
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) := by
    change (Opens.map e.hom).IsContinuous _ _
    infer_instance
  letI : (Opens.mapMapIso e).inverse.IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) := by
    change (Opens.map e.inv).IsContinuous _ _
    infer_instance
  CategoryTheory.Equivalence.mk (pushforward C e.hom) (pushforward C e.inv)
    ((Functor.sheafPushforwardContinuousComp'
      (Opens.mapMapIso e).counitIso C (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) ≪≫
      Functor.sheafPushforwardContinuousId C (Opens.grothendieckTopology X)).symm)
    (Functor.sheafPushforwardContinuousComp'
      (Opens.mapMapIso e).unitIso.symm C (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) ≪≫
      Functor.sheafPushforwardContinuousId C (Opens.grothendieckTopology Y))

instance (f : X ⟶ Y) [IsIso f] : (pushforward C f).IsEquivalence :=
  (pushforwardEquivalence C (asIso f)).isEquivalence_functor

end TopCat.Sheaf
