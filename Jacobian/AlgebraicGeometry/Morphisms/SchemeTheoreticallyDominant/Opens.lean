import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Scheme-theoretically dense open subschemes

An open that is scheme-theoretically dense remains dense in every intermediate open.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {ambientScheme : Scheme.{u}}

/-- A scheme-theoretically dense open remains dense in any intermediate open. -/
theorem IsSchemeTheoreticallyDominant.homOfLE {smallerOpen largerOpen : ambientScheme.Opens} (inclusion : smallerOpen ≤ largerOpen)
    [QuasiCompact smallerOpen.ι] [IsSchemeTheoreticallyDominant smallerOpen.ι] :
    IsSchemeTheoreticallyDominant (ambientScheme.homOfLE inclusion) := by
  have dense_inclusion : IsSchemeTheoreticallyDominant (ambientScheme.homOfLE (inf_le_right : smallerOpen ⊓ largerOpen ≤ largerOpen)) :=
    .of_isPullback (isPullback_opens_inf smallerOpen largerOpen)
  have factorization : ambientScheme.homOfLE inclusion =
      (ambientScheme.isoOfEq (inf_eq_left.mpr inclusion)).inv ≫ ambientScheme.homOfLE (inf_le_right : smallerOpen ⊓ largerOpen ≤ largerOpen) := by
    rw [← cancel_mono largerOpen.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι,
      Scheme.isoOfEq_inv_ι]
  rw [factorization]
  infer_instance

end AlgebraicGeometry
