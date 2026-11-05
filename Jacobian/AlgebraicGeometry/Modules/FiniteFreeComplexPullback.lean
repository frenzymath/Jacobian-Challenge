import Jacobian.AlgebraicGeometry.Modules.FiniteFreeComplex
import Jacobian.AlgebraicGeometry.Modules.Free

/-!
# Pullback of bounded finite free complexes

Pullback preserves the bounds and finite free terms of a complex of module
sheaves.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback preserves a finite free complex and its bounds. -/
theorem IsFiniteFreeComplex.pullback_complex {sourceScheme targetScheme : Scheme.{u}}
    {complex : CochainComplex targetScheme.Modules ℤ} {bound : ℕ}
    (finiteFree : IsFiniteFreeComplex complex bound) (baseChange : sourceScheme ⟶ targetScheme) :
    IsFiniteFreeComplex (((Modules.pullback baseChange).mapHomologicalComplex _).obj complex) bound := by
  letI := finiteFree.isStrictlyGE
  letI := finiteFree.isStrictlyLE
  refine ⟨?_, ?_, fun degree ↦ ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro degree negative
    exact (Modules.pullback baseChange).map_isZero
      (complex.isZero_of_isStrictlyGE 0 degree negative)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro degree aboveBound
    exact (Modules.pullback baseChange).map_isZero
      (complex.isZero_of_isStrictlyLE bound degree aboveBound)
  · obtain ⟨rank, ⟨trivialization⟩⟩ := finiteFree.exists_iso_free degree
    exact ⟨rank, ⟨(Modules.pullback baseChange).mapIso trivialization ≪≫ pullbackFreeIso baseChange _⟩⟩

end AlgebraicGeometry.Scheme.Modules
