import Jacobian.AlgebraicGeometry.Cohomology.Affine.Vanishing
import Jacobian.AlgebraicGeometry.ProjectiveLine.Charts
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# The cohomological bound from a map to the projective line

The two standard affine charts of the projective line pull back to an affine cover under any
affine morphism. Consequently quasi-coherent cohomology of its source vanishes in degrees at
least two. In particular this applies to finite maps from proper curves.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A scheme affine over the projective line has no quasi-coherent cohomology above degree one. -/
theorem subsingleton_H_of_affine_hom_projectiveLine {k : Type u} [Field k]
    {X : Scheme.{u}} (morphism : X ⟶ projectiveLine k) [IsAffineHom morphism]
    (M : X.Modules) [M.IsQuasicoherent] (degree : ℕ) (higher : 2 ≤ degree) :
    Subsingleton (M.H degree) := by
  have : IsSeparated (terminal.from (projectiveLine k)) := by
    rw [← terminal.comp_from (projectiveLineToSpec k)]
    infer_instance
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from morphism]
    infer_instance
  let chart (coordinate : Fin 2) := morphism ⁻¹ᵁ ProjectiveLine.chart k coordinate
  have affine (coordinate : Fin 2) : IsAffineOpen (chart coordinate) := by
    exact (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      (MvPolynomial.X coordinate) (MvPolynomial.isHomogeneous_X _ _) (by decide)).preimage morphism
  have covering : (Finset.univ : Finset (Fin 2)).sup chart = ⊤ := by
    simpa only [Finset.sup_univ_eq_iSup] using
      morphism.iSup_preimage_eq_top (ProjectiveLine.iSup_chart_eq_top k)
  exact subsingleton_H_of_card_le (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty
    chart (fun coordinate _ ↦ affine coordinate) covering _
    (cechAcyclicOnAffines_of_isQuasicoherent M) (by simpa using higher)

end AlgebraicGeometry.Scheme.Modules
