import Jacobian.AlgebraicGeometry.IdealSheaf.Twist
import Jacobian.AlgebraicGeometry.Modules.ZeroLocus

/-!
# Effective divisors of nonzero line-bundle sections

On an integral scheme, a nonzero section of a line bundle gives an effective
Cartier divisor. The line bundle is the dual of the divisor's ideal sheaf.
The construction first tensors the section with the dual line bundle, then
uses the native zero ideal of the resulting map to the structure sheaf.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) [M.IsInvertible]

/-- A section of a line bundle, viewed as a functional on its dual. -/
def dualFunctionalOfSection (sectionMap : unit X ⟶ M) : Mᵛ ⟶ unit X :=
  (ρ_ Mᵛ).inv ≫ (tensorLeft Mᵛ).map sectionMap ≫
    ((β_ Mᵛ M) ≪≫ tensorObjDualIsoUnit M).hom

/-- Tensoring by the dual line bundle detects nonzero sections. -/
theorem dualFunctionalOfSection_ne_zero (sectionMap : unit X ⟶ M)
    (nonzero : sectionMap ≠ 0) : dualFunctionalOfSection M sectionMap ≠ 0 := by
  intro zeroFunctional
  have zeroTensor : (tensorLeft Mᵛ).map sectionMap = 0 := by
    apply (cancel_epi (ρ_ Mᵛ).inv).mp
    apply (cancel_mono ((β_ Mᵛ M) ≪≫ tensorObjDualIsoUnit M).hom).mp
    simpa only [dualFunctionalOfSection, Category.assoc, comp_zero, zero_comp]
      using zeroFunctional
  apply nonzero
  apply (tensorLeft Mᵛ).map_injective
  simpa only [Functor.map_zero] using zeroTensor

/-- A nonzero section on an integral scheme presents its line bundle as the
dual of an effective Cartier ideal. -/
theorem exists_effectiveCartier_of_nonzero_section [IsIntegral X]
    (sectionMap : unit X ⟶ M) (nonzero : sectionMap ≠ 0) :
    ∃ J : X.IdealSheafData, ∃ hJ : J.IsInvertible, Nonempty (M ≅ J.toModulesᵛ) := by
  let functional := dualFunctionalOfSection M sectionMap
  have nonzeroFunctional : functional ≠ 0 :=
    dualFunctionalOfSection_ne_zero M sectionMap nonzero
  let J := functional.zeroLocus
  have hJ : J.IsInvertible := functional.isInvertible_zeroLocus nonzeroFunctional
  letI := hJ.isInvertible_toModules
  obtain ⟨idealComparison, _⟩ := functional.exists_iso_toModules_zeroLocus hJ
  let pairing : J.toModules ⊗ M ≅ 𝟙_ X.Modules :=
    whiskerRightIso idealComparison.symm M ≪≫ β_ Mᵛ M ≪≫ tensorObjDualIsoUnit M
  exact ⟨J, hJ, ⟨(tensorLeft J.toModules).preimageIso
    (pairing ≪≫ (tensorObjDualIsoUnit J.toModules).symm)⟩⟩

end AlgebraicGeometry.Scheme.Modules
