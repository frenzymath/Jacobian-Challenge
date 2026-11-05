import Jacobian.AlgebraicGeometry.Picard.RepresentedPullback

/-!
# The contravariant functor of represented degree-zero Picard groups

Any family of tensor-compatible representations determines a functor on curves.
Its object action is exactly the supplied family of commutative groups, and its
maps classify pullback of line bundles. No existence of representations is used.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.PicardTensorCompatible

variable {baseField : Type u} [Field baseField]
  (groups : Curve baseField → CommGrp (Over (Spec (.of baseField))))
  (representations : ∀ curve : Curve baseField,
    (picardFunctorDegree curve.carrier.hom 0).obj.RepresentableBy (groups curve).X)
  (compatibilities : ∀ curve : Curve baseField,
    PicardTensorCompatible curve.carrier.hom (groups curve) (representations curve))

/-- Tensor-compatible representing groups form a contravariant functor on curves. -/
def representedFunctor : (Curve baseField)ᵒᵖ ⥤ CommGrp (Over (Spec (.of baseField))) where
  obj curve := groups curve.unop
  map morphism := representedPullback (compatibilities _) (compatibilities _) morphism.unop
  map_id curve := representedPullback_id (compatibilities curve.unop)
  map_comp firstMap secondMap := by
    simpa only [unop_comp] using representedPullback_comp
      (compatibilities _) (compatibilities _) (compatibilities _)
      secondMap.unop firstMap.unop

/-- The functor retains the supplied group, not a separately induced structure. -/
@[simp]
theorem representedFunctor_obj (curve : (Curve baseField)ᵒᵖ) :
    (representedFunctor groups representations compatibilities).obj curve = groups curve.unop :=
  rfl

/-- Its arrow action is the line-bundle pullback characterized by the representations. -/
@[simp]
theorem representedFunctor_map {source target : (Curve baseField)ᵒᵖ}
    (morphism : source ⟶ target) :
    (representedFunctor groups representations compatibilities).map morphism =
      representedPullback (compatibilities target.unop) (compatibilities source.unop)
        morphism.unop :=
  rfl

end AlgebraicGeometry.PicardTensorCompatible
