import Jacobian.AlgebraicGeometry.Curve.Cohomology
import Jacobian.AlgebraicGeometry.IdealSheaf.Section
import Jacobian.AlgebraicGeometry.IdealSheaf.RelativeCartierPullback
import Jacobian.AlgebraicGeometry.Morphisms.FiniteRank
import Jacobian.AlgebraicGeometry.Picard.DegreeCartier

/-!
# Degree of section divisors

An effective Cartier divisor on a smooth proper curve whose closed subscheme
is isomorphic to the ground field has degree one. This remains true after
arbitrary field-valued base change of a relative section divisor.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {baseField : Type u} [Field baseField]

/-- A Cartier divisor consisting of one rational point has degree one. -/
theorem IsInvertible.degree_dual_toModules_eq_one (curve : Curve baseField)
    {ideal : curve.carrier.left.IdealSheafData} (invertible : ideal.IsInvertible)
    [IsIso (ideal.subschemeι ≫ curve.carrier.hom)] :
    letI : curve.carrier.left.Over (Spec (.of baseField)) := ⟨curve.carrier.hom⟩
    ideal.toModulesᵛ.degree baseField = 1 := by
  letI : curve.carrier.left.Over (Spec (.of baseField)) := ⟨curve.carrier.hom⟩
  letI : IsIso (ideal.subschemeι ≫ (curve.carrier.left ↘ Spec (.of baseField))) := by
    change IsIso (ideal.subschemeι ≫ curve.carrier.hom)
    infer_instance
  letI : ideal.toModules.IsInvertible := invertible.isInvertible_toModules
  letI : (ideal.twist (Modules.unit curve.carrier.left)).IsInvertible :=
    invertible.isInvertible_twist _
  letI (degree : ℕ) : Module.Finite baseField ((Modules.unit curve.carrier.left).H degree) :=
    curve.hasFiniteH _ degree
  letI (degree : ℕ) :
      Module.Finite baseField ((ideal.twist (Modules.unit curve.carrier.left)).H degree) :=
    curve.hasFiniteH _ degree
  have increment := invertible.degree_twist_eq_add_finrank (k := baseField)
    (Modules.unit curve.carrier.left) 1
    (fun degree bound ↦ curve.subsingleton_H _ bound)
    (fun degree bound ↦ curve.subsingleton_H _ bound)
  have rank_one : (ideal.subschemeι ≫ curve.carrier.hom).finrankΓ = 1 := by
    calc
      _ = (ideal.subschemeι ≫ curve.carrier.hom).finrank
          (IsLocalRing.closedPoint baseField) :=
        (Scheme.Hom.finrank_eq_finrankΓ_of_field (ideal.subschemeι ≫ curve.carrier.hom)
          (IsLocalRing.closedPoint baseField)).symm
      _ = 1 := by
        rw [Scheme.Hom.finrank_eq_one_of_isIso (ideal.subschemeι ≫ curve.carrier.hom)]
        rfl
  rw [Modules.degree_unit] at increment
  change (ideal.twist (Modules.unit curve.carrier.left)).degree baseField =
    0 + ((ideal.subschemeι ≫ curve.carrier.hom).finrankΓ : ℤ) at increment
  have twist_degree : (ideal.twist (Modules.unit curve.carrier.left)).degree baseField = 1 := by
    simpa only [rank_one, Nat.cast_one, zero_add] using increment
  exact (Modules.degree_congr baseField (λ_ ideal.toModulesᵛ)).symm.trans twist_degree

/-- A relative Cartier section has degree one on every field-valued base change. -/
theorem IsRelativeEffectiveCartier.degree_pullback_dual_toModules_eq_one
    {source baseScheme : Scheme.{u}} (projection : source ⟶ baseScheme)
    {ideal : source.IdealSheafData} (relative : ideal.IsRelativeEffectiveCartier projection)
    [IsIso (ideal.subschemeι ≫ projection)] (curve : Curve baseField)
    (fiberMap : curve.carrier.left ⟶ source) (fieldPoint : Spec (.of baseField) ⟶ baseScheme)
    (square : IsPullback fiberMap curve.carrier.hom projection fieldPoint) :
    letI : curve.carrier.left.Over (Spec (.of baseField)) := ⟨curve.carrier.hom⟩
    ((Modules.pullback fiberMap).obj ideal.toModulesᵛ).degree baseField = 1 := by
  letI : curve.carrier.left.Over (Spec (.of baseField)) := ⟨curve.carrier.hom⟩
  have pulledInvertible : (ideal.comap fiberMap).IsInvertible :=
    relative.1.comap_of_isPullback relative.2 square
  have divisorSquare := (ideal.isPullback_comap fiberMap).flip.paste_vert square
  letI : IsIso ((ideal.comap fiberMap).subschemeι ≫ curve.carrier.hom) :=
    divisorSquare.isIso_snd_of_isIso
  obtain ⟨comparison⟩ :=
    relative.1.nonempty_pullback_dual_toModules_iso fiberMap pulledInvertible
  exact (Modules.degree_congr baseField comparison).trans
    (IsInvertible.degree_dual_toModules_eq_one curve pulledInvertible)

end AlgebraicGeometry.Scheme.IdealSheafData
