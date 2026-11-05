import Jacobian.AlgebraicGeometry.ProjectiveLine.Basic
import Jacobian.RingTheory.MvPolynomial.HomogeneousCharts
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Standard affine charts of the projective line

The two standard opens of the projective line are spectra of polynomial rings
in one variable. They cover the existing projective-line construction, and its
structure morphism is proper.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

variable (baseField : Type u) [Field baseField]

/-- The standard open on which the chosen homogeneous coordinate is nonzero. -/
def chart (coordinate : Fin 2) : (projectiveLine baseField).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
    (MvPolynomial.X coordinate)

/-- The two standard coordinate opens cover the projective line. -/
theorem iSup_chart_eq_top : ⨆ coordinate, chart baseField coordinate = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [MvPolynomial.toIdeal_irrelevant_homogeneousSubmodule]

/-- A standard projective-line chart is the spectrum of a polynomial ring in
the other coordinate. -/
def chartSpecIso (coordinate : Fin 2) :
    (chart baseField coordinate).toScheme ≅
      Spec (.of (MvPolynomial {index : Fin 2 // index ≠ coordinate} baseField)) :=
  Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
    (MvPolynomial.X coordinate)
    (show MvPolynomial.X coordinate ∈ MvPolynomial.homogeneousSubmodule (Fin 2) baseField 1 from
      MvPolynomial.isHomogeneous_X _ _) (by decide) ≪≫
      (Scheme.Spec.mapIso
        (MvPolynomial.homogeneousLocalizationAwayXEquiv baseField coordinate).toRingEquiv.toCommRingCatIso.op).symm

/-- The open immersion of the affine coordinate chart into the projective line. -/
def chartMorphism (coordinate : Fin 2) :
    Spec (.of (MvPolynomial {index : Fin 2 // index ≠ coordinate} baseField)) ⟶
      projectiveLine baseField :=
  (chartSpecIso baseField coordinate).inv ≫ (chart baseField coordinate).ι

instance chartMorphism_isOpenImmersion (coordinate : Fin 2) :
    IsOpenImmersion (chartMorphism baseField coordinate) := by
  dsimp [chartMorphism]
  infer_instance

/-- Projective-line charts have the usual polynomial structure morphism. -/
theorem chartMorphism_toSpec (coordinate : Fin 2) :
    chartMorphism baseField coordinate ≫ projectiveLineToSpec baseField =
      Spec.map (CommRingCat.ofHom
        (algebraMap baseField (MvPolynomial {index : Fin 2 // index ≠ coordinate} baseField))) := by
  simp only [chartMorphism, chartSpecIso, chart, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Iso.op_hom, RingEquiv.toCommRingCatIso_hom,
    Scheme.Spec_map, Quiver.Hom.unop_op,
    Category.assoc, Proj.basicOpenIsoSpec_inv_ι_assoc]
  rw [projectiveLineToSpec, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun coefficient ↦ ?_)
  change MvPolynomial.homogeneousLocalizationAwayXEquiv baseField coordinate
    (algebraMap baseField _ coefficient) = MvPolynomial.C coefficient
  exact MvPolynomial.homogeneousLocalizationAwayXEquiv_algebraMap
    baseField coordinate coefficient

/-- The structure morphism of the projective line is proper. -/
instance isProper_toSpec : IsProper (projectiveLineToSpec baseField) := by
  have coefficient_iso : IsIso (CommRingCat.ofHom
      (algebraMap baseField (MvPolynomial.homogeneousSubmodule (Fin 2) baseField 0))) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) baseField).bijective
  dsimp [projectiveLineToSpec]
  infer_instance

end AlgebraicGeometry.ProjectiveLine
