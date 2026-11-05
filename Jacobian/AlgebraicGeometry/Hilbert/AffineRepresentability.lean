import Jacobian.AlgebraicGeometry.Hilbert.ClosedImmersion
import Jacobian.AlgebraicGeometry.Hilbert.Representability

/-!
# Representability of Hilbert functors of affine schemes

Every morphism between affine schemes admits a closed immersion into an affine
space over the base. The containment equations realize its Hilbert functor as
a closed subfunctor of the affine-space Hilbert functor.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The finite-flat Hilbert functor of a morphism between affine schemes is representable. -/
theorem isRepresentable_hilbertPresheaf_of_isAffine (f : X ⟶ S) [IsAffine X] [IsAffine S]
    (d : ℕ) : (hilbertPresheaf f d).IsRepresentable := by
  let i : X ⟶ 𝔸(Γ(X, ⊤); S) := AffineSpace.homOfVector f id
  have : IsClosedImmersion i := .of_surjective_of_isAffine i fun a ↦
    ⟨AffineSpace.coord S a, AffineSpace.homOfVector_appTop_coord f id a⟩
  rw [← AffineSpace.homOfVector_over f id]
  exact isRepresentable_hilbertPresheaf_of_isClosedImmersion i _ d
    (isRepresentable_hilbertPresheaf_affineSpace _ S d)


end AlgebraicGeometry
