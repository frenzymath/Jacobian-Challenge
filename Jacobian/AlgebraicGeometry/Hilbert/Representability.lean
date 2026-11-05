import Jacobian.AlgebraicGeometry.Hilbert.AffineSpace
import Jacobian.AlgebraicGeometry.Hilbert.Sheaf
import Jacobian.AlgebraicGeometry.Sites.Representability

/-!
# Representability of the Hilbert functor of affine space

The quotient-basis charts cover the finite-flat Hilbert functor by representable
open subfunctors. Effective descent glues these charts into a scheme.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- The Hilbert functor of finite flat degree-`rank` subschemes of affine space
over an affine base is representable. -/
theorem isRepresentable_hilbertPresheaf_affineSpace
    (indeterminates : Type u) (base : Scheme.{u}) [IsAffine base] (rank : ℕ) :
    (hilbertPresheaf (𝔸(indeterminates; base) ↘ base) rank).IsRepresentable := by
  refine Scheme.LocalRepresentability.isRepresentable_of_isSheaf_over_of_isAffine _
    (isSheaf_zariskiTopology_hilbertPresheaf _ rank)
    (fun family ↦ Hilbert.basisChart family)
    (fun family ↦ Hilbert.basisChartPoint family)
    (fun family test _ firstMap secondMap equality ↦
      Hilbert.basisChartPoint_injective family test equality)
    (fun family test _ point ↦ Hilbert.exists_opens_basisChartPoint family test point)
    (fun test _ point testPoint ↦ Hilbert.exists_basisChartPoint test point testPoint)

end AlgebraicGeometry
