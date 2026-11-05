import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Restrict
import Jacobian.AlgebraicGeometry.Modules.ProjectionFormula

/-!
# Projection formula for higher direct images of line bundles

Tensoring by a line bundle is an exact autoequivalence. Deriving the natural
projection formula therefore commutes with tensoring by a line bundle from
the base, in every degree.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}}

/-- Twisting by a line bundle from the base commutes with higher direct images. -/
def higherDirectImageTensorObjPullbackIso [HasInjectiveResolutions X.Modules]
    (f : X ⟶ Y) (ℱ : X.Modules) (𝒩 : Y.Modules) [𝒩.IsInvertible] (q : ℕ) :
    (higherDirectImage f q).obj (ℱ ⊗ (pullback f).obj 𝒩) ≅ (higherDirectImage f q).obj ℱ ⊗ 𝒩 := by
  have := Functor.additive_of_preserves_binary_products (tensorRight ((pullback f).obj 𝒩))
  have := Functor.additive_of_preserves_binary_products (tensorRight 𝒩)
  exact (Functor.compRightDerivedObjIso (tensorRight ((pullback f).obj 𝒩)) (pushforward f)
    (fun _ _ ↦ Functor.rightAcyclic_of_injective _) q ℱ).symm ≪≫
    Functor.rightDerivedObjIsoOfIso (invertibleProjectionIso f 𝒩).symm q ℱ ≪≫
    Functor.rightDerivedCompObjIso (pushforward f) (tensorRight 𝒩) q ℱ

end AlgebraicGeometry.Scheme.Modules
