import Jacobian.AlgebraicGeometry.Cohomology.Sections
import Jacobian.AlgebraicGeometry.IdealSheaf.CanonicalSection

/-!
# Nonzero sections defining effective Cartier divisors

An effective Cartier divisor on a nonempty scheme has nonempty complement.
Its canonical section, transported to any isomorphic divisor line bundle,
is therefore nonzero, as is its zeroth cohomology class.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory
open scoped nonZeroDivisors AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {sourceScheme : Scheme.{u}} [Nonempty sourceScheme]

/-- Any line bundle isomorphic to a Cartier divisor line has a nonzero section
whose zero ideal is precisely that divisor, with nonzero zeroth cohomology class. -/
theorem IsInvertible.exists_nonzero_section_of_iso {ideal : sourceScheme.IdealSheafData}
    (cartier : ideal.IsInvertible) (lineBundle : sourceScheme.Modules)
    [lineBundle.IsInvertible] :
    letI := cartier.isInvertible_toModules
    (ideal.toModulesᵛ ≅ lineBundle) →
      ∃ sectionMap : Modules.unit sourceScheme ⟶ lineBundle,
        sectionMap.zeroLocus = ideal ∧ sectionMap ≠ 0 ∧
          Modules.H.unitHomAddEquiv lineBundle sectionMap ≠ 0 := by
  letI := cartier.isInvertible_toModules
  intro comparison
  obtain ⟨canonicalSection, canonical_zeroLocus⟩ := cartier.exists_zeroLocus_eq
  let sectionMap := canonicalSection ≫ comparison.hom
  have arrowComparison : Arrow.mk canonicalSection ≅ Arrow.mk sectionMap :=
    Arrow.isoMk (Iso.refl _) comparison (by simp [sectionMap])
  have zeroLocus_eq : sectionMap.zeroLocus = ideal :=
    (Modules.Hom.zeroLocus_eq_of_arrowIso canonicalSection sectionMap arrowComparison).symm.trans
      canonical_zeroLocus
  have ideal_nonzero : ideal ≠ ⊥ := by
    obtain ⟨point, point_outside⟩ := cartier.exists_notMem_support
    intro vanishing
    exact point_outside (by rw [vanishing, support_bot]; trivial)
  have section_nonzero : sectionMap ≠ 0 := by
    intro vanishing
    exact ideal_nonzero (zeroLocus_eq.symm.trans
      ((Modules.Hom.zeroLocus_eq_bot_iff sectionMap).mpr vanishing))
  refine ⟨sectionMap, zeroLocus_eq, section_nonzero, ?_⟩
  intro vanishing
  apply section_nonzero
  exact (Modules.H.unitHomAddEquiv lineBundle).injective
    (vanishing.trans (map_zero (Modules.H.unitHomAddEquiv lineBundle)).symm)

end AlgebraicGeometry.Scheme.IdealSheafData
