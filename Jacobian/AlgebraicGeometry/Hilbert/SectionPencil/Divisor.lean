import Jacobian.AlgebraicGeometry.Curve.DivisorDegree
import Jacobian.AlgebraicGeometry.Hilbert.RelativeDivisorOperations
import Jacobian.AlgebraicGeometry.Modules.RelativeZeroLocus
import Jacobian.AlgebraicGeometry.Modules.ZeroLocusTensor

/-!
# Hilbert divisors cut out by sections

A fibrewise nonzero section on a proper smooth family of geometrically integral
curves cuts out a finite flat relative divisor. Its rank is the degree of the
line bundle on the residue fibre. Constant degree therefore gives an actual
point of the Hilbert presheaf, with its defining ideal preserved by base change.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.SectionPencil

variable {source base : Scheme.{u}}

/-- Pullback of a section, including the identification of the structure module. -/
def pullbackSectionHom {test : Scheme.{u}} (morphism : test ⟶ source)
    {lineBundle : source.Modules} (sectionMap : unit source ⟶ lineBundle) :
    unit test ⟶ (Scheme.Modules.pullback morphism).obj lineBundle :=
  (pullbackObjUnitIso morphism).inv ≫ (Scheme.Modules.pullback morphism).map sectionMap

/-- The ideal of a pulled-back section is the pulled-back ideal, even for
nonflat base changes. -/
theorem pullbackSectionHom_zeroLocus {test : Scheme.{u}} (morphism : test ⟶ source)
    {lineBundle : source.Modules} [lineBundle.IsInvertible]
    (sectionMap : unit source ⟶ lineBundle) :
    (pullbackSectionHom morphism sectionMap).zeroLocus = sectionMap.zeroLocus.comap morphism := by
  letI : (unit test).IsInvertible := Scheme.Modules.isInvertible_unit test
  let comparison : Arrow.mk ((Scheme.Modules.pullback morphism).map sectionMap) ≅
      Arrow.mk (pullbackSectionHom morphism sectionMap) :=
    Arrow.isoMk' _ _ (pullbackObjUnitIso morphism) (Iso.refl _)
      (by simp only [pullbackSectionHom, Iso.hom_inv_id_assoc, Iso.refl_hom,
        Category.comp_id])
  exact (Hom.zeroLocus_eq_of_arrowIso ((Scheme.Modules.pullback morphism).map sectionMap)
    (pullbackSectionHom morphism sectionMap) comparison).symm.trans
      (Hom.comap_zeroLocus morphism sectionMap).symm

/-- The degree of a line bundle on a literal residue-field fibre. -/
def fibreDegree (structureMap : source ⟶ base) (lineBundle : source.Modules)
    (point : base) : ℤ :=
  letI := structureMap.fiberOverSpecResidueField point
  ((Scheme.Modules.pullback (structureMap.fiberι point)).obj lineBundle).degree
    (base.residueField point)

/-- A fibrewise nonzero section defines a finite flat relative Cartier divisor. -/
private theorem zeroLocus_isFiniteLocallyFree (structureMap : source ⟶ base)
    [SmoothOfRelativeDimension 1 structureMap] [IsProper structureMap]
    [GeometricallyIntegral structureMap] (lineBundle : source.Modules)
    [lineBundle.IsInvertible] (sectionMap : unit source ⟶ lineBundle)
    (nonzeroFibres : ∀ point : base,
      (Scheme.Modules.pullback (structureMap.fiberι point)).map sectionMap ≠ 0) :
    sectionMap.zeroLocus.IsInvertible ∧
      IsFinite (sectionMap.zeroLocus.subschemeι ≫ structureMap) ∧
        Flat (sectionMap.zeroLocus.subschemeι ≫ structureMap) ∧
          LocallyOfFinitePresentation (sectionMap.zeroLocus.subschemeι ≫ structureMap) := by
  exact sectionMap.isInvertible_zeroLocus_and_isFinite structureMap
    (fun point ↦ inferInstance) nonzeroFibres

/-- The divisor line of a fibrewise nonzero section is the original line bundle. -/
theorem nonempty_iso_dual_zeroLocus {lineBundle : source.Modules}
    [lineBundle.IsInvertible] (sectionMap : unit source ⟶ lineBundle)
    (regular : sectionMap.zeroLocus.IsInvertible) :
    Nonempty (lineBundle ≅ sectionMap.zeroLocus.toModulesᵛ) := by
  obtain ⟨comparison⟩ := sectionMap.nonempty_iso_dual_toModules_tensorObj
    regular
  exact ⟨comparison ≪≫ ρ_ _⟩

private theorem finrankΓ_eq_degree_of_zeroLocus
    {baseField : Type u} [Field baseField] {curve : Scheme.{u}}
    [curve.Over (Spec (.of baseField))]
    [IsProper (curve ↘ Spec (.of baseField))]
    [SmoothOfRelativeDimension 1 (curve ↘ Spec (.of baseField))]
    [GeometricallyIrreducible (curve ↘ Spec (.of baseField))]
    (sectionSource lineBundle : curve.Modules)
    [sectionSource.IsInvertible] [lineBundle.IsInvertible]
    (sourceIso : sectionSource ≅ unit curve) (sectionMap : sectionSource ⟶ lineBundle)
    (divisor : curve.IdealSheafData) (zeroEquality : sectionMap.zeroLocus = divisor)
    (regular : divisor.IsInvertible)
    [IsFinite (divisor.subschemeι ≫ (curve ↘ Spec (.of baseField)))] :
    ((divisor.subschemeι ≫ (curve ↘ Spec (.of baseField))).finrankΓ : ℤ) =
      lineBundle.degree baseField := by
  obtain ⟨comparison⟩ := sectionMap.nonempty_iso_dual_toModules_tensorObj
    (by rw [zeroEquality]; exact regular)
  rw [zeroEquality] at comparison
  let lineComparison : lineBundle ≅ divisor.toModulesᵛ := comparison ≪≫
    whiskerLeftIso divisor.toModulesᵛ sourceIso ≪≫ ρ_ divisor.toModulesᵛ
  have divisorDegree : divisor.toModulesᵛ.degree baseField =
      ((divisor.subschemeι ≫ (curve ↘ Spec (.of baseField))).finrankΓ : ℤ) :=
    regular.degree_dual_toModules
  exact divisorDegree.symm.trans (Scheme.Modules.degree_congr baseField lineComparison).symm

/-- The finite-flat rank of the zero scheme equals the degree on the same fibre. -/
theorem zeroLocus_finrank (structureMap : source ⟶ base)
    [SmoothOfRelativeDimension 1 structureMap] [IsProper structureMap]
    [GeometricallyIntegral structureMap] (lineBundle : source.Modules)
    [lineBundle.IsInvertible] (sectionMap : unit source ⟶ lineBundle)
    (nonzeroFibres : ∀ point : base,
      (Scheme.Modules.pullback (structureMap.fiberι point)).map sectionMap ≠ 0)
    (point : base) :
    ((sectionMap.zeroLocus.subschemeι ≫ structureMap).finrank point : ℤ) =
      fibreDegree structureMap lineBundle point := by
  obtain ⟨_, finite, flat, _⟩ :=
    zeroLocus_isFiniteLocallyFree structureMap lineBundle sectionMap nonzeroFibres
  haveI : IsFinite (sectionMap.zeroLocus.subschemeι ≫ structureMap) := finite
  haveI : Flat (sectionMap.zeroLocus.subschemeι ≫ structureMap) := flat
  let divisor := sectionMap.zeroLocus
  let fibreMap := structureMap.fiberι point
  let residueField : Type u := base.residueField point
  letI := structureMap.fiberOverSpecResidueField point
  have smoothAlong : MorphismProperty.IsStableUnderBaseChangeAlong
      (@SmoothOfRelativeDimension.{u} 1) (base.fromSpecResidueField point) :=
    { of_isPullback := fun square smoothProjection =>
        @MorphismProperty.IsStableUnderBaseChange.of_isPullback
          Scheme.{u} inferInstance (@SmoothOfRelativeDimension.{u} 1)
          (smoothOfRelativeDimension_isStableUnderBaseChange.{u} 1)
          _ _ _ _ _ _ _ _ square smoothProjection }
  haveI : SmoothOfRelativeDimension 1 (structureMap.fiber point ↘ Spec (.of residueField)) :=
    @MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback
      Scheme.{u} inferInstance (@SmoothOfRelativeDimension.{u} 1)
      (Spec (base.residueField point)) base (base.fromSpecResidueField point) smoothAlong
      source (structureMap.fiber point)
      (Limits.pullback.fst structureMap (base.fromSpecResidueField point))
      (Limits.pullback.snd structureMap (base.fromSpecResidueField point)) structureMap
      (IsPullback.of_hasPullback structureMap (base.fromSpecResidueField point)) inferInstance
  haveI : IsProper (structureMap.fiber point ↘ Spec (.of residueField)) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI : GeometricallyIntegral (structureMap.fiber point ↘ Spec (.of residueField)) :=
    MorphismProperty.pullback_snd (P := @GeometricallyIntegral) _ _ inferInstance
  haveI : ((Scheme.Modules.pullback fibreMap).obj (unit source)).IsInvertible :=
    Scheme.Modules.isInvertible_pullback fibreMap (unit source)
  haveI : ((Scheme.Modules.pullback fibreMap).obj lineBundle).IsInvertible :=
    Scheme.Modules.isInvertible_pullback fibreMap lineBundle
  have regularFibre : (divisor.comap fibreMap).IsInvertible := by
    dsimp only [divisor, fibreMap]
    rw [Hom.comap_zeroLocus]
    exact Hom.isInvertible_zeroLocus (nonzeroFibres point)
  have rankEquality : (divisor.subschemeι ≫ structureMap).finrank point =
      ((divisor.comap fibreMap).subschemeι ≫
        structureMap.fiberToSpecResidueField point).finrankΓ :=
    divisor.finrank_subschemeι_comp_eq_finrankΓ structureMap point
  haveI : IsFinite ((divisor.comap fibreMap).subschemeι ≫
      (structureMap.fiber point ↘ Spec (.of residueField))) := by
    change IsFinite ((divisor.comap fibreMap).subschemeι ≫
      structureMap.fiberToSpecResidueField point)
    exact divisor.isFinite_comap_fiberι structureMap point
  have zeroEquality :
      ((Scheme.Modules.pullback fibreMap).map sectionMap).zeroLocus =
        divisor.comap fibreMap :=
    (Hom.comap_zeroLocus fibreMap sectionMap).symm
  have degreeEquality : (((divisor.comap fibreMap).subschemeι ≫
      structureMap.fiberToSpecResidueField point).finrankΓ : ℤ) =
      ((Scheme.Modules.pullback fibreMap).obj lineBundle).degree residueField :=
    finrankΓ_eq_degree_of_zeroLocus (baseField := residueField)
      (curve := structureMap.fiber point)
      ((Scheme.Modules.pullback fibreMap).obj (unit source))
      ((Scheme.Modules.pullback fibreMap).obj lineBundle) (pullbackObjUnitIso fibreMap)
      ((Scheme.Modules.pullback fibreMap).map sectionMap) (divisor.comap fibreMap)
      zeroEquality regularFibre
  change ((divisor.subschemeι ≫ structureMap).finrank point : ℤ) =
    ((Scheme.Modules.pullback fibreMap).obj lineBundle).degree residueField
  exact (congrArg (fun rank : ℕ => (rank : ℤ)) rankEquality).trans degreeEquality

/-- A fibrewise nonzero, constant-degree section determines an actual Hilbert
point, without assuming representability of the Hilbert presheaf. -/
def hilbertPoint (structureMap : source ⟶ base)
    [SmoothOfRelativeDimension 1 structureMap] [IsProper structureMap]
    [GeometricallyIntegral structureMap] (degree : ℕ) (parameter : Over base)
    (lineBundle : (Limits.pullback structureMap parameter.hom).Modules)
    [lineBundle.IsInvertible]
    (sectionMap : unit (Limits.pullback structureMap parameter.hom) ⟶ lineBundle)
    (nonzeroFibres : ∀ point : parameter.left,
      (Scheme.Modules.pullback
        ((Limits.pullback.snd structureMap parameter.hom).fiberι point)).map sectionMap ≠ 0)
    (constantDegree : ∀ point : parameter.left,
      fibreDegree (Limits.pullback.snd structureMap parameter.hom) lineBundle point = degree) :
    (hilbertPresheaf structureMap degree).obj (op parameter) := by
  refine ⟨sectionMap.zeroLocus, ?_⟩
  letI : SmoothOfRelativeDimension 1 (Limits.pullback.snd structureMap parameter.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback structureMap parameter.hom) inferInstance
  letI : IsProper (Limits.pullback.snd structureMap parameter.hom) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  letI : GeometricallyIntegral (Limits.pullback.snd structureMap parameter.hom) :=
    MorphismProperty.pullback_snd (P := @GeometricallyIntegral) _ _ inferInstance
  obtain ⟨_, finite, flat, finitePresentation⟩ :=
    zeroLocus_isFiniteLocallyFree (Limits.pullback.snd structureMap parameter.hom)
      lineBundle sectionMap nonzeroFibres
  refine ⟨finite, flat, finitePresentation, fun point ↦ ?_⟩
  have rankEquality := zeroLocus_finrank (Limits.pullback.snd structureMap parameter.hom)
    lineBundle sectionMap nonzeroFibres point
  rw [constantDegree point] at rankEquality
  exact_mod_cast rankEquality

/-- Base change of the constructed Hilbert point has the literal ideal of the
pulled-back section; no nonvanishing or degree proof has to be supplied again. -/
theorem hilbertPoint_map_val (structureMap : source ⟶ base)
    [SmoothOfRelativeDimension 1 structureMap] [IsProper structureMap]
    [GeometricallyIntegral structureMap] (degree : ℕ) {parameter smallerParameter : Over base}
    (restriction : smallerParameter ⟶ parameter)
    (lineBundle : (Limits.pullback structureMap parameter.hom).Modules)
    [lineBundle.IsInvertible]
    (sectionMap : unit (Limits.pullback structureMap parameter.hom) ⟶ lineBundle)
    (nonzeroFibres : ∀ point : parameter.left,
      (Scheme.Modules.pullback
        ((Limits.pullback.snd structureMap parameter.hom).fiberι point)).map sectionMap ≠ 0)
    (constantDegree : ∀ point : parameter.left,
      fibreDegree (Limits.pullback.snd structureMap parameter.hom) lineBundle point = degree) :
    ((hilbertPresheaf structureMap degree).map restriction.op
      (hilbertPoint structureMap degree parameter lineBundle sectionMap
        nonzeroFibres constantDegree)).1 =
      (pullbackSectionHom (baseChangeMap structureMap restriction) sectionMap).zeroLocus := by
  change sectionMap.zeroLocus.comap (baseChangeMap structureMap restriction) = _
  exact (pullbackSectionHom_zeroLocus (baseChangeMap structureMap restriction) sectionMap).symm

end AlgebraicGeometry.SectionPencil
