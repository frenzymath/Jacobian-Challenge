import Jacobian.AlgebraicGeometry.Modules.ClearDenominators
import Jacobian.AlgebraicGeometry.Modules.Coherent
import Jacobian.AlgebraicGeometry.Modules.Coproducts
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Twist
import Jacobian.AlgebraicGeometry.ProjectiveSpace.TwistSections
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.ZeroLocus

/-!
# Finite presentations by negative twists

Over a Noetherian coefficient ring, every coherent sheaf on polynomial
projective space is a quotient of a finite sum of negative twists with coherent
kernel. Finite affine generators extend after clearing denominators of the
coordinate sections of the degree-one twist. Sections on a coordinate chart
lift along a morphism from a negative twist.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Proj

open Scheme.Modules MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (coordinates : Type v) (coefficients : Type (max u v)) [CommRing coefficients] [IsNoetherianRing coefficients] [Finite coordinates]

/-- A section of a quasi-coherent sheaf on a coordinate chart lifts along a
morphism from a negative twist. -/
theorem exists_hom_twist_app_eq
    (moduleSheaf : (projectiveSpaceOverAffine.{u, v} coordinates coefficients).Modules)
    [moduleSheaf.IsQuasicoherent] (coordinate : coordinates)
    (sectionValue : Γ(moduleSheaf, standardOpen.{u, v} coordinates coefficients coordinate)) :
    ∃ (exponent : ℕ)
      (componentMap : twist (homogeneousSubmodule coordinates coefficients)
        (-(exponent : ℤ)) ⟶ moduleSheaf)
      (localPreimage : Γ(twist (homogeneousSubmodule coordinates coefficients)
        (-(exponent : ℤ)), standardOpen.{u, v} coordinates coefficients coordinate)),
      componentMap.app (standardOpen.{u, v} coordinates coefficients coordinate) localPreimage =
        sectionValue := by
  letI (degree : ℤ) : (twist (homogeneousSubmodule coordinates coefficients) degree).IsInvertible :=
    isInvertible_twist_homogeneousSubmodule.{u, v} coordinates coefficients degree
  let coordinateSection :=
    unitToTwist.{max u v} (grading := homogeneousSubmodule coordinates coefficients)
      (formDegree := 1) (homogeneousElement := X coordinate)
      (isHomogeneous_X coefficients coordinate)
  let coordinateOpen :
      (projectiveSpaceOverAffine.{u, v} coordinates coefficients).Opens :=
    (Hom.zeroLocus.{max u v} (X := projectiveSpaceOverAffine.{u, v} coordinates coefficients)
      coordinateSection).support.compl
  have coordinateOpen_eq :
      coordinateOpen = standardOpen.{u, v} coordinates coefficients coordinate :=
    compl_support_zeroLocus_unitToTwist.{max u v}
      (exists_mem_basicOpen_homogeneousSubmodule.{u, v} coordinates coefficients)
      (isHomogeneous_X coefficients coordinate)
  revert sectionValue
  rw [← coordinateOpen_eq]
  intro sectionValue
  letI : CompactSpace (projectiveSpaceOverAffine.{u, v} coordinates coefficients) :=
    QuasiCompact.compactSpace_of_compactSpace
      (projectiveSpaceOverAffineToSpec.{u, v} coordinates coefficients)
  have restrictionData := exists_tensorPowSection_eq_restrict.{max u v}
    (scheme := projectiveSpaceOverAffine.{u, v} coordinates coefficients)
    (structureMap := projectiveSpaceOverAffineToSpec.{u, v} coordinates coefficients)
    (lineSection := coordinateSection)
    (moduleSheaf := moduleSheaf) (localSection := sectionValue)
  obtain ⟨exponent, extendedSection, restrictionEquation⟩ := restrictionData
  obtain ⟨comparison⟩ := nonempty_tensorPow_twist_one_tensor_neg_iso.{max u v}
    (homogeneousSubmodule coordinates coefficients)
    (exists_mem_basicOpen_homogeneousSubmodule.{u, v} coordinates coefficients) exponent
  exact ⟨exponent, exists_hom_app_eq_of_tensorPowSection.{max u v}
    (scheme := projectiveSpaceOverAffine.{u, v} coordinates coefficients) coordinateSection
    (isFreeGenerator_app_one_of_le _ le_rfl) exponent comparison sectionValue
      extendedSection restrictionEquation⟩

/-- Finite generators on the coordinate charts can be chosen together with maps from
negative twists lifting each generator. -/
private theorem exists_standardOpen_twist_generators
    (moduleSheaf : (projectiveSpaceOverAffine.{u, v} coordinates coefficients).Modules)
    [moduleSheaf.IsFinitePresentation] [moduleSheaf.IsQuasicoherent]
    (chartAffine : ∀ coordinate,
      IsAffineOpen (standardOpen.{u, v} coordinates coefficients coordinate)) :
    ∃ (generatorCount : coordinates → ℕ)
      (sectionValue : ∀ coordinate, Fin (generatorCount coordinate) →
        Γ(moduleSheaf, standardOpen.{u, v} coordinates coefficients coordinate)),
      (∀ coordinate, Submodule.span
        Γ(projectiveSpaceOverAffine.{u, v} coordinates coefficients,
          standardOpen.{u, v} coordinates coefficients coordinate)
        (Set.range (sectionValue coordinate)) = ⊤) ∧
      ∃ (exponent : (Σ coordinate : coordinates,
          ULift.{max u v} (Fin (generatorCount coordinate))) → ℕ)
        (componentMap : ∀ generatorIndex,
          twist (homogeneousSubmodule coordinates coefficients)
            (-(exponent generatorIndex : ℤ)) ⟶ moduleSheaf)
        (localPreimage : ∀ generatorIndex,
          Γ(twist (homogeneousSubmodule coordinates coefficients)
            (-(exponent generatorIndex : ℤ)),
            standardOpen.{u, v} coordinates coefficients generatorIndex.1)),
        ∀ generatorIndex, (componentMap generatorIndex).app
          (standardOpen.{u, v} coordinates coefficients generatorIndex.1)
          (localPreimage generatorIndex) =
            sectionValue generatorIndex.1 generatorIndex.2.down := by
  choose generatorCount sectionValue ht using fun coordinate : coordinates ↦
    letI := finitePresentation_sections_of_isFinitePresentation.{max u v}
      (scheme := projectiveSpaceOverAffine.{u, v} coordinates coefficients) moduleSheaf
      (openSubset := standardOpen.{u, v} coordinates coefficients coordinate)
      (chartAffine coordinate)
    Module.Finite.exists_fin
      (R := Γ(projectiveSpaceOverAffine.{u, v} coordinates coefficients,
        standardOpen.{u, v} coordinates coefficients coordinate))
      (M := Γ(moduleSheaf, standardOpen.{u, v} coordinates coefficients coordinate))
  choose exponent componentMap localPreimage hw using fun (generatorIndex : Σ coordinate : coordinates,
      ULift.{max u v} (Fin (generatorCount coordinate))) ↦
    exists_hom_twist_app_eq.{u, v} coordinates coefficients moduleSheaf generatorIndex.1
      (sectionValue generatorIndex.1 generatorIndex.2.down)
  exact ⟨generatorCount, sectionValue, ht, exponent, componentMap, localPreimage, hw⟩

set_option maxHeartbeats 400000 in
/-- A coherent sheaf on projective space is a quotient of finitely many negative
twists, and its kernel is coherent. -/
theorem exists_epi_sigma_twist (moduleSheaf : (projectiveSpaceOverAffine coordinates coefficients).Modules)
    [moduleSheaf.IsFinitePresentation] :
    ∃ (indexType : Type (max u v)) (_ : Finite indexType) (generator : indexType → ℕ)
      (componentMap : (∐ fun generatorIndex ↦ twist (homogeneousSubmodule coordinates coefficients) (-(generator generatorIndex : ℤ))) ⟶ moduleSheaf),
      Epi componentMap ∧ (kernel componentMap).IsQuasicoherent ∧ (kernel componentMap).IsFinitePresentation := by
  letI (degree : ℤ) : (twist (homogeneousSubmodule coordinates coefficients) degree).IsInvertible :=
    isInvertible_twist_homogeneousSubmodule.{u, v} coordinates coefficients degree
  letI : SheafOfModules.IsQuasicoherent
      (R := (projectiveSpaceOverAffine coordinates coefficients).ringCatSheaf) moduleSheaf :=
    { nonempty_quasicoherentData :=
        ⟨(SheafOfModules.IsFinitePresentation.exists_quasicoherentData moduleSheaf).choose⟩ }
  letI (degree : ℤ) : SheafOfModules.IsQuasicoherent
      (R := (projectiveSpaceOverAffine coordinates coefficients).ringCatSheaf)
      (twist (homogeneousSubmodule coordinates coefficients) degree) := by
    obtain ⟨generators, generatorProperties⟩ :=
      (isInvertible_twist_homogeneousSubmodule.{u, v}
        coordinates coefficients degree).exists_isInvertibleData
    haveI := generatorProperties.toIsLocallyFreeData
    exact { nonempty_quasicoherentData := ⟨generators.quasiCoherentData⟩ }
  letI : Fintype coordinates := Fintype.ofFinite coordinates
  have chartAffine (coordinate : coordinates) :
      IsAffineOpen (standardOpen.{u, v} coordinates coefficients coordinate) := by
    change IsAffineOpen (basicOpen (homogeneousSubmodule coordinates coefficients) (X coordinate))
    exact isAffineOpen_basicOpen.{max u v} (homogeneousSubmodule coordinates coefficients)
      (X coordinate) (isHomogeneous_X coefficients coordinate) one_pos
  have chartCover : ⨆ coordinate, standardOpen.{u, v} coordinates coefficients coordinate = ⊤ := by
    change (⨆ coordinate, basicOpen (homogeneousSubmodule coordinates coefficients)
      (X coordinate)) = ⊤
    exact iSup_basicOpen_eq_top'.{max u v} (homogeneousSubmodule coordinates coefficients)
      (X : coordinates → MvPolynomial coordinates coefficients)
      (fun coordinate ↦ ⟨1, isHomogeneous_X coefficients coordinate⟩)
      (adjoin_range_X_eq_top coordinates coefficients)
  obtain ⟨generatorCount, sectionValue, ht, exponent, componentMap, localPreimage, hw⟩ :=
    exists_standardOpen_twist_generators.{u, v}
      coordinates coefficients moduleSheaf chartAffine
  let twistFamily : (Σ coordinate : coordinates, ULift.{max u v} (Fin (generatorCount coordinate))) →
      (projectiveSpaceOverAffine.{u, v} coordinates coefficients).Modules :=
    fun generatorIndex ↦ twist (homogeneousSubmodule coordinates coefficients)
      (-(exponent generatorIndex : ℤ))
  let coordinateOpens : coordinates →
      (projectiveSpaceOverAffine.{u, v} coordinates coefficients).Opens :=
    standardOpen.{u, v} coordinates coefficients
  have componentImagesSpan (coordinate : coordinates) :
      Submodule.span Γ(projectiveSpaceOverAffine.{u, v} coordinates coefficients,
        coordinateOpens coordinate)
        (⋃ generatorIndex : (Σ coordinate : coordinates, ULift.{max u v} (Fin (generatorCount coordinate))),
          Set.range ((componentMap generatorIndex).app (coordinateOpens coordinate))) = ⊤ := by
    refine eq_top_iff.mpr ((ht coordinate).ge.trans (Submodule.span_mono ?_))
    rintro generatorSection ⟨generatorIndex, rfl⟩
    exact Set.mem_iUnion.mpr ⟨⟨coordinate, ⟨generatorIndex⟩⟩,
      localPreimage ⟨coordinate, ⟨generatorIndex⟩⟩, hw ⟨coordinate, ⟨generatorIndex⟩⟩⟩
  have epimorphism : Epi (Sigma.desc componentMap) :=
    epi_sigma_desc_of_span_eq_top
      (scheme := projectiveSpaceOverAffine.{u, v} coordinates coefficients)
      (indexType := Σ coordinate : coordinates, ULift.{max u v} (Fin (generatorCount coordinate)))
      (family := twistFamily) (targetSheaf := moduleSheaf) (componentMap := componentMap)
      (coverIndex := coordinates) (openSubset := coordinateOpens)
      (affine := chartAffine) (cover := chartCover) (spans := componentImagesSpan)
  refine ⟨Σ coordinate : coordinates, ULift.{max u v} (Fin (generatorCount coordinate)), inferInstance,
    exponent, Sigma.desc componentMap, epimorphism, ?_, ?_⟩
  · letI := isQuasicoherent_sigma
      (fun generatorIndex ↦ twist (homogeneousSubmodule coordinates coefficients) (-(exponent generatorIndex : ℤ)))
    exact isQuasicoherent_kernel _
  · letI : IsLocallyNoetherian (projectiveSpaceOverAffine coordinates coefficients) :=
      LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOverAffineToSpec coordinates coefficients)
    letI := isFinitePresentation_sigma
      (fun generatorIndex ↦ twist (homogeneousSubmodule coordinates coefficients) (-(exponent generatorIndex : ℤ)))
    exact isFinitePresentation_kernel _

end AlgebraicGeometry.Proj
