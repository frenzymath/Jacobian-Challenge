import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Dimensions of homology

Homology of a short complex with finite-dimensional middle term is finite-dimensional. Its dimension is the dimension of the middle term minus the ranks of the two differentials.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

section FiniteDimensional

open Module

namespace CategoryTheory.ShortComplex

variable {K : Type*} [Field K] (S : ShortComplex (ModuleCat K)) [FiniteDimensional K S.X₂]

/-- The homology of a short complex of vector spaces with finite dimensional `X₂` is finite
dimensional. -/
instance finiteDimensional_homology : FiniteDimensional K S.homology :=
  let e : (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) ≃ₗ[K] S.homology :=
    S.moduleCatHomologyIso.toLinearEquiv.symm
  Module.Finite.equiv e

/-- `dim H(S) + rank g + rank f = dim X₂` for a short complex `S` of vector spaces with
`X₂` finite dimensional. -/
theorem finrank_homology_add_finrank_range_add_finrank_range :
    finrank K S.homology + finrank K (LinearMap.range S.g.hom) +
      finrank K (LinearMap.range S.f.hom) = finrank K S.X₂ := by
  rw [S.moduleCatHomologyIso.toLinearEquiv.finrank_eq]
  change finrank K (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) + _ + _ = _
  have h₁ := Submodule.finrank_quotient_add_finrank (LinearMap.range S.moduleCatToCycles)
  have h₂ : finrank K (LinearMap.range S.moduleCatToCycles) =
      finrank K (LinearMap.range S.f.hom) := by
    have hle : LinearMap.range S.f.hom ≤ LinearMap.ker S.g.hom := by
      rintro _ ⟨x, rfl⟩
      exact congr($(S.zero) x)
    have hf (x : S.X₁) : S.f.hom x ∈ LinearMap.ker S.g.hom :=
      hle (LinearMap.mem_range_self S.f.hom x)
    change finrank K (LinearMap.range
      (S.f.hom.codRestrict (LinearMap.ker S.g.hom) hf)) = _
    rw [LinearMap.range_codRestrict]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have h₃ := LinearMap.finrank_range_add_finrank_ker S.g.hom
  omega

end CategoryTheory.ShortComplex

end FiniteDimensional
