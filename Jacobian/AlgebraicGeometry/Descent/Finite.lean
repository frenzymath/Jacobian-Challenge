import Jacobian.AlgebraicGeometry.Descent.AffineLocal
import Jacobian.AlgebraicGeometry.Descent.Gluing
import Jacobian.AlgebraicGeometry.Descent.InvariantAffineOpen

/-!
# Effective finite-flat descent of schemes

A scheme whose finite sets lie in affine open subschemes admits effective descent
along a surjective finite flat morphism locally of finite presentation. Invariant
affine neighbourhoods reduce the construction to affine descent, and the local
descents glue.
-/

universe schemeUniverse

open CategoryTheory Limits

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {source base : Scheme.{schemeUniverse}} {baseMap : source ⟶ base}

theorem isEffective_of_isFinite [IsFinite baseMap] [Flat baseMap]
    [LocallyOfFinitePresentation baseMap] [Surjective baseMap] {representation : Over source}
    (finite_affine : ∀ finiteSet : Set representation.left, finiteSet.Finite →
      ∃ openSubset : representation.left.Opens, IsAffineOpen openSubset ∧ finiteSet ⊆ openSubset)
    (datum : DescentDatum baseMap representation) : datum.IsEffective := by
  refine isEffective_of_forall_exists_mem fun point ↦ ?_
  obtain ⟨openSubset, point_mem, invariant, affineOpen, baseOpen, affineBase, overBase⟩ :=
    datum.exists_isInvariant_isAffineOpen finite_affine point
  exact ⟨openSubset, invariant, point_mem,
    datum.isEffective_restrict_of_isAffineOpen invariant affineOpen affineBase overBase⟩

end CategoryTheory.Over.DescentDatum
