import Jacobian.AlgebraicGeometry.ProjectiveLine.Charts
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.StructureMap
import Jacobian.AlgebraicGeometry.Modules.DifferentialsSections
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Polynomial basic opens of the projective line

The two standard affine charts have polynomial rings as their rings of sections.
Their polynomial basic opens form a basis, with sections given by localization.
These are the affine opens used to construct traces along finite curve maps.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory TopologicalSpace Opposite Polynomial

namespace AlgebraicGeometry.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev coordinateComplementUnique (coordinate : Fin 2) :
    Unique {index : Fin 2 // index ≠ coordinate} where
  default := ⟨coordinate.rev, by fin_cases coordinate <;> decide⟩
  uniq := by
    rintro ⟨index, distinct⟩
    apply Subtype.ext
    fin_cases coordinate <;> fin_cases index
    all_goals first | exact False.elim (distinct rfl) | rfl

attribute [local instance] coordinateComplementUnique

variable (baseField : Type u) [Field baseField]

/-- Polynomials in the other homogeneous coordinate describe a standard chart. -/
def polyEquivChart (coordinate : Fin 2) :
    baseField[X] ≃+* Γ(projectiveLine baseField, chart baseField coordinate) :=
  (MvPolynomial.uniqueAlgEquiv baseField {index : Fin 2 // index ≠ coordinate}).symm.toRingEquiv.trans
    ((MvPolynomial.homogeneousLocalizationAwayXEquiv baseField coordinate).symm.toRingEquiv.trans
      (Iso.commRingCatIsoToRingEquiv
        (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
          (MvPolynomial.X coordinate) (MvPolynomial.isHomogeneous_X _ _) (by decide))))

/-- Constants in the polynomial chart are the pullbacks of base-field constants. -/
lemma polyEquivChart_C (coordinate : Fin 2) (coefficient : baseField) :
    polyEquivChart baseField coordinate (C coefficient) =
      (projectiveLineToSpec baseField).specStructureMap (chart baseField coordinate) coefficient := by
  have structureEquation :
      (Scheme.ΓSpecIso (.of baseField)).inv ≫ (projectiveLineToSpec baseField).appTop ≫
          (projectiveLine baseField).presheaf.map
            (homOfLE (le_top : chart baseField coordinate ≤ ⊤)).op =
        CommRingCat.ofHom (algebraMap baseField
          (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
            (MvPolynomial.X coordinate))) ≫ Proj.awayToSection _ _ := by
    change (Scheme.ΓSpecIso (.of baseField)).inv ≫
        (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) baseField) ≫
          Spec.map (CommRingCat.ofHom (algebraMap baseField
            (MvPolynomial.homogeneousSubmodule (Fin 2) baseField 0)))).appTop ≫
        (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)).presheaf.map
          (homOfLE (le_top : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
            (MvPolynomial.X coordinate) ≤ ⊤)).op = _
    rw [Scheme.Hom.comp_appTop]
    simp only [Category.assoc]
    rw [← Scheme.ΓSpecIso_inv_naturality_assoc,
      Proj.toSpecZero_appTop_res (MvPolynomial.homogeneousSubmodule (Fin 2) baseField)
        (MvPolynomial.X coordinate) (MvPolynomial.isHomogeneous_X baseField coordinate) (by decide)]
    rfl
  change Proj.awayToSection _ _
    ((MvPolynomial.homogeneousLocalizationAwayXEquiv baseField coordinate).symm
      ((MvPolynomial.uniqueAlgEquiv baseField
        {index : Fin 2 // index ≠ coordinate}).symm (C coefficient))) = _
  have polynomialConstant :
      (MvPolynomial.uniqueAlgEquiv baseField
        {index : Fin 2 // index ≠ coordinate}).symm (C coefficient) =
          MvPolynomial.C coefficient :=
    AlgEquiv.commutes _ coefficient
  rw [polynomialConstant]
  change Proj.awayToSection _ _
    ((MvPolynomial.homogeneousLocalizationAwayXEquiv baseField coordinate).symm
      (algebraMap baseField (MvPolynomial {index : Fin 2 // index ≠ coordinate} baseField)
        coefficient)) = _
  rw [AlgEquiv.commutes]
  exact (congrArg (fun ringMap : CommRingCat.of baseField ⟶
    Γ(projectiveLine baseField, chart baseField coordinate) ↦ ringMap coefficient)
      structureEquation).symm

/-- The basic open where a polynomial in an affine chart does not vanish. -/
abbrev chartBasicOpen (coordinate : Fin 2) (polynomial : baseField[X]) :
    (projectiveLine baseField).Opens :=
  (projectiveLine baseField).basicOpen (polyEquivChart baseField coordinate polynomial)

lemma chartBasicOpen_le (coordinate : Fin 2) (polynomial : baseField[X]) :
    chartBasicOpen baseField coordinate polynomial ≤ chart baseField coordinate :=
  (projectiveLine baseField).basicOpen_le _

lemma isAffineOpen_chart (coordinate : Fin 2) : IsAffineOpen (chart baseField coordinate) := by
  exact Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X _ _) (by decide)

lemma isAffineOpen_chartBasicOpen (coordinate : Fin 2) (polynomial : baseField[X]) :
    IsAffineOpen (chartBasicOpen baseField coordinate polynomial) :=
  (isAffineOpen_chart baseField coordinate).basicOpen _

/-- The polynomial ring maps into the sections on its chart basic open. -/
def polyToChartBasicOpen (coordinate : Fin 2) (polynomial : baseField[X]) :
    baseField[X] →+* Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial) :=
  ((projectiveLine baseField).presheaf.map
    (homOfLE (chartBasicOpen_le baseField coordinate polynomial)).op).hom.comp
      (polyEquivChart baseField coordinate).toRingHom

/-- The polynomial-localization map respects the field structure map. -/
lemma polyToChartBasicOpen_C (coordinate : Fin 2) (polynomial : baseField[X])
    (coefficient : baseField) :
    polyToChartBasicOpen baseField coordinate polynomial (C coefficient) =
      (projectiveLineToSpec baseField).specStructureMap
        (chartBasicOpen baseField coordinate polynomial) coefficient := by
  rw [polyToChartBasicOpen, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, polyEquivChart_C]
  exact congrArg (fun ringMap : CommRingCat.of baseField ⟶
    Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial) ↦
      ringMap coefficient)
        ((projectiveLineToSpec baseField).specStructureMap_map
          (chartBasicOpen_le baseField coordinate polynomial))

/-- Sections on a polynomial basic open are the corresponding localization. -/
theorem isLocalization_chartBasicOpen (coordinate : Fin 2) (polynomial : baseField[X]) :
    letI := (polyToChartBasicOpen baseField coordinate polynomial).toAlgebra
    IsLocalization.Away polynomial
      Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial) := by
  have := (isAffineOpen_chart baseField coordinate).isLocalization_basicOpen
    (polyEquivChart baseField coordinate polynomial)
  have localization := IsLocalization.isLocalization_of_base_ringEquiv
    (Submonoid.powers (polyEquivChart baseField coordinate polynomial))
    Γ(projectiveLine baseField, chartBasicOpen baseField coordinate polynomial)
    (polyEquivChart baseField coordinate).symm
  rw [Submonoid.map_powers, RingEquiv.symm_apply_apply] at localization
  exact localization

/-- Nonzero polynomial basic opens in the two affine charts form an open basis. -/
theorem isBasis_chartBasicOpen :
    Opens.IsBasis (Set.range fun index : (Σ _ : Fin 2, {polynomial : baseField[X] // polynomial ≠ 0}) ↦
      chartBasicOpen baseField index.1 index.2.1) := by
  refine Opens.isBasis_iff_nbhd.2 fun {openSubset point} membership ↦ ?_
  obtain ⟨coordinate, chartMembership⟩ := Opens.mem_iSup.mp
    ((iSup_chart_eq_top baseField).ge (Set.mem_univ point))
  obtain ⟨sectionValue, contained, basicMembership⟩ :=
    (isAffineOpen_chart baseField coordinate).exists_basicOpen_le ⟨point, membership⟩ chartMembership
  obtain ⟨polynomial, rfl⟩ := (polyEquivChart baseField coordinate).surjective sectionValue
  refine ⟨chartBasicOpen baseField coordinate polynomial,
    ⟨⟨coordinate, polynomial, fun zeroPolynomial ↦ ?_⟩, rfl⟩, basicMembership, contained⟩
  rw [zeroPolynomial, map_zero, Scheme.basicOpen_zero] at basicMembership
  exact basicMembership

end AlgebraicGeometry.ProjectiveLine
