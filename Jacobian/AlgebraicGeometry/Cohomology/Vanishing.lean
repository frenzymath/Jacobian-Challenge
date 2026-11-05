import Jacobian.AlgebraicGeometry.Cohomology.LongExact

/-!
# Vanishing and exact sequences

Finite coproducts preserve cohomological vanishing. In a short exact sequence,
vanishing in the middle and in the next degree on the left implies vanishing
on the right.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{u}}

/-- Finite coproducts preserve vanishing in a fixed cohomological degree. -/
lemma subsingleton_H_sigma {indexType : Type u} [Finite indexType]
    (modules : indexType → scheme.Modules) (degree : ℕ)
    (vanishing : ∀ index, Subsingleton ((modules index).H degree)) :
    Subsingleton ((∐ modules).H degree) := by
  obtain ⟨count, ⟨indexEquiv⟩⟩ := Finite.exists_equiv_fin indexType
  suffices vanishingReindexed : ∀ reindexedModules : Fin count → scheme.Modules,
      (∀ index, Subsingleton ((reindexedModules index).H degree)) →
        Subsingleton ((∐ reindexedModules).H degree) by
    letI := vanishingReindexed (modules ∘ indexEquiv.symm)
      (fun index ↦ vanishing (indexEquiv.symm index))
    exact (H.mapLinearEquiv (Sigma.reindex indexEquiv.symm modules).symm degree).toEquiv.subsingleton
  intro reindexedModules componentVanishing
  letI : HasFiniteBiproducts scheme.Modules := HasFiniteBiproducts.of_hasFiniteCoproducts
  haveI : Subsingleton ((⨁ reindexedModules).H degree) :=
    subsingleton_of_forall_eq 0 fun cohomologyClass ↦ by
      have decomposition : H.map (∑ index,
          biproduct.π reindexedModules index ≫ biproduct.ι reindexedModules index)
          degree cohomologyClass = cohomologyClass := by
        rw [biproduct.total]
        exact H.map_id_apply _ _ cohomologyClass
      rw [← decomposition, H.map_sum_apply]
      refine Finset.sum_eq_zero fun index _ ↦ ?_
      rw [H.map_comp_apply]
      letI := componentVanishing index
      rw [Subsingleton.elim (H.map (biproduct.π reindexedModules index) degree cohomologyClass) 0,
        map_zero]
  exact (H.mapLinearEquiv (biproduct.isoCoproduct reindexedModules).symm degree).toEquiv.subsingleton

/-- The long exact sequence propagates vanishing to the third coefficient sheaf. -/
lemma subsingleton_H_X₃_of_shortExact {sequence : ShortComplex scheme.Modules}
    (shortExact : sequence.ShortExact) (degree : ℕ)
    (middleVanishing : Subsingleton (sequence.X₂.H degree))
    (leftVanishing : Subsingleton (sequence.X₁.H (degree + 1))) :
    Subsingleton (sequence.X₃.H degree) := by
  letI := middleVanishing
  letI := leftVanishing
  refine subsingleton_of_forall_eq 0 fun cohomologyClass ↦ ?_
  have membership : cohomologyClass ∈ (H.δ shortExact degree).ker :=
    Subsingleton.elim _ _
  rw [H.ker_δ_eq_range_map_g shortExact degree] at membership
  obtain ⟨preimageClass, rfl⟩ := membership
  rw [Subsingleton.elim preimageClass 0, map_zero]

end AlgebraicGeometry.Scheme.Modules
