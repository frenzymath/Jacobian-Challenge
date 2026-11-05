import Jacobian.AlgebraicGeometry.Morphisms.Immersion

/-!
# Affine preimages under immersions

An immersion is closed over its coborder range. The preimage of an affine open
contained in that range is therefore affine.
-/

universe schemeUniverse

namespace AlgebraicGeometry

lemma Scheme.Hom.isAffineOpen_preimage_of_le_coborderRange
    {source target : Scheme.{schemeUniverse}} (immersion : source ⟶ target)
    [IsImmersion immersion] {opens : target.Opens} (affine : IsAffineOpen opens)
    (inclusion : opens ≤ immersion.coborderRange) :
    IsAffineOpen (immersion ⁻¹ᵁ opens) := by
  have pulledBack := (affine.preimage_of_isOpenImmersion immersion.coborderRange.ι
    (by rwa [Scheme.Opens.opensRange_ι])).preimage immersion.liftCoborder
  rwa [← Scheme.Hom.comp_preimage, Scheme.Hom.liftCoborder_ι] at pulledBack

end AlgebraicGeometry
