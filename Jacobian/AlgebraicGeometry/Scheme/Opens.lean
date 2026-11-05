import Mathlib.AlgebraicGeometry.Scheme

/-!
# Inverse images of scheme opens
-/

universe u

namespace AlgebraicGeometry.Scheme.Hom

lemma preimage_iInf {sourceScheme targetScheme : Scheme.{u}}
    (morphism : sourceScheme ⟶ targetScheme) {indexType : Type*} [Finite indexType]
    (opensFamily : indexType → targetScheme.Opens) :
    morphism ⁻¹ᵁ ⨅ index, opensFamily index = ⨅ index, morphism ⁻¹ᵁ opensFamily index := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_preimage, TopologicalSpace.Opens.coe_iInf, Set.preimage_iInter]

end AlgebraicGeometry.Scheme.Hom
