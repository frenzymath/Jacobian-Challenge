import Jacobian.AlgebraicGeometry.Curve.Cohomology
import Jacobian.AlgebraicGeometry.IdealSheaf.Curve
import Jacobian.AlgebraicGeometry.Modules.ZeroLocus
import Jacobian.AlgebraicGeometry.Picard.Degree
import Jacobian.AlgebraicGeometry.Picard.DegreeCartier

/-!
# Degree and tensor products on smooth proper curves

Cohomological degree is additive under tensor products of line bundles. Twisting
by a nonempty effective Cartier divisor eventually produces a nonzero section.
Such a section presents its line bundle as a Cartier twist of the structure
sheaf, and the Cartier Euler increments cancel in the tensor-additivity defect.
The same presentation shows that a line bundle with a nonzero section has
nonnegative degree, so negative-degree line bundles have vanishing zeroth
cohomology.
No rational point or algebraic closure of the ground field is needed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

private def tensorEulerDefect (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (firstLine secondLine : X.Modules) : ℤ :=
  (firstLine ⊗ secondLine).eulerChar k - firstLine.eulerChar k -
    secondLine.eulerChar k + (unit X).eulerChar k

private theorem tensorEulerDefect_iso_right (firstLine : X.Modules)
    {secondLine otherLine : X.Modules} (comparison : secondLine ≅ otherLine) :
    tensorEulerDefect k firstLine secondLine = tensorEulerDefect k firstLine otherLine := by
  unfold tensorEulerDefect
  rw [eulerChar_congr k (whiskerLeftIso firstLine comparison), eulerChar_congr k comparison]

private theorem tensorEulerDefect_unit (firstLine : X.Modules) :
    tensorEulerDefect k firstLine (unit X) = 0 := by
  unfold tensorEulerDefect
  have unitEuler : (firstLine ⊗ unit X).eulerChar k = firstLine.eulerChar k :=
    eulerChar_congr k (ρ_ firstLine)
  rw [unitEuler]
  omega

private theorem exists_iso_twist_unit_of_nonzero_section [IsIntegral X]
    (lineBundle : X.Modules) [lineBundle.IsInvertible]
    (sectionMap : unit X ⟶ lineBundle) (nonzeroSection : sectionMap ≠ 0) :
    ∃ ideal : X.IdealSheafData, ideal.IsInvertible ∧
      Nonempty (lineBundle ≅ ideal.twist (unit X)) := by
  let tensorFunctor := tensorLeft lineBundleᵛ
  let sourceIso : lineBundleᵛ ⊗ unit X ≅ lineBundleᵛ := ρ_ _
  let targetIso : lineBundleᵛ ⊗ lineBundle ≅ unit X :=
    β_ _ _ ≪≫ tensorObjDualIsoUnit lineBundle
  let functional : lineBundleᵛ ⟶ unit X :=
    sourceIso.inv ≫ tensorFunctor.map sectionMap ≫ targetIso.hom
  have nonzeroFunctional : functional ≠ 0 := by
    intro zeroFunctional
    have zeroTensor : tensorFunctor.map sectionMap = 0 := by
      have evaluated := congrArg
        (fun morphism ↦ sourceIso.hom ≫ morphism ≫ targetIso.inv) zeroFunctional
      simpa [functional, Category.assoc] using evaluated
    apply nonzeroSection
    apply tensorFunctor.map_injective
    simpa using zeroTensor
  let ideal := functional.zeroLocus
  have invertible : ideal.IsInvertible := functional.isInvertible_zeroLocus nonzeroFunctional
  letI := invertible.isInvertible_toModules
  obtain ⟨idealIso, _⟩ := functional.exists_iso_toModules_zeroLocus invertible
  let inverseIso : ideal.toModules ⊗ lineBundle ≅ unit X :=
    whiskerRightIso idealIso.symm _ ≪≫ targetIso
  let lineIso : lineBundle ≅ ideal.toModulesᵛ :=
    (tensorLeft ideal.toModules).preimageIso
      (inverseIso ≪≫ (tensorObjDualIsoUnit ideal.toModules).symm)
  exact ⟨ideal, invertible, ⟨lineIso ≪≫ (λ_ ideal.toModulesᵛ).symm⟩⟩

variable [IsProper (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [GeometricallyIrreducible (X ↘ Spec (.of k))]

private theorem finite_cohomology (moduleSheaf : X.Modules)
    [moduleSheaf.IsFinitePresentation] (degree : ℕ) : Module.Finite k (moduleSheaf.H degree) := by
  let curve : Curve k :=
    { carrier := Over.mk (X ↘ Spec (.of k))
      isProper := inferInstanceAs (IsProper (X ↘ Spec (.of k)))
      smoothOfRelativeDimension := inferInstanceAs (SmoothOfRelativeDimension 1 (X ↘ Spec (.of k)))
      geometricallyIrreducible := inferInstanceAs (GeometricallyIrreducible (X ↘ Spec (.of k))) }
  exact curve.hasFiniteH moduleSheaf degree

include k in
private theorem cohomology_vanishing (moduleSheaf : X.Modules)
    [moduleSheaf.IsQuasicoherent] (degree : ℕ) (bound : 1 < degree) :
    Subsingleton (moduleSheaf.H degree) := by
  let curve : Curve k :=
    { carrier := Over.mk (X ↘ Spec (.of k))
      isProper := inferInstanceAs (IsProper (X ↘ Spec (.of k)))
      smoothOfRelativeDimension := inferInstanceAs (SmoothOfRelativeDimension 1 (X ↘ Spec (.of k)))
      geometricallyIrreducible := inferInstanceAs (GeometricallyIrreducible (X ↘ Spec (.of k))) }
  exact curve.subsingleton_H moduleSheaf bound

private theorem eulerChar_twist (ideal : X.IdealSheafData) (invertible : ideal.IsInvertible)
    (lineBundle : X.Modules) [lineBundle.IsInvertible] :
    letI := ((ΓSpecIso (.of k)).inv ≫
      (ideal.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    (ideal.twist lineBundle).eulerChar k = lineBundle.eulerChar k +
      (Module.finrank k Γ(ideal.subscheme, ⊤) : ℤ) := by
  letI := invertible.isFinite_subschemeι_comp (X ↘ Spec (.of k))
  letI := invertible.isInvertible_twist lineBundle
  letI (degree : ℕ) : Module.Finite k (lineBundle.H degree) :=
    finite_cohomology (k := k) lineBundle degree
  letI (degree : ℕ) : Module.Finite k ((ideal.twist lineBundle).H degree) :=
    finite_cohomology (k := k) (ideal.twist lineBundle) degree
  exact invertible.eulerChar_twist_eq_add_finrank lineBundle 1
    (cohomology_vanishing (k := k) lineBundle)
    (cohomology_vanishing (k := k) (ideal.twist lineBundle))

private theorem tensorEulerDefect_twist (ideal : X.IdealSheafData)
    (invertible : ideal.IsInvertible) (firstLine secondLine : X.Modules)
    [firstLine.IsInvertible] [secondLine.IsInvertible] :
    tensorEulerDefect k firstLine (ideal.twist secondLine) =
      tensorEulerDefect k firstLine secondLine := by
  have tensorIncrement := eulerChar_twist (k := k) ideal invertible (firstLine ⊗ secondLine)
  have lineIncrement := eulerChar_twist (k := k) ideal invertible secondLine
  have comparison := eulerChar_congr k (ideal.tensorTwistIso firstLine secondLine)
  unfold tensorEulerDefect
  linarith

private def iteratedTwist (ideal : X.IdealSheafData) (lineBundle : X.Modules) : ℕ → X.Modules
  | 0 => lineBundle
  | count + 1 => ideal.twist (iteratedTwist ideal lineBundle count)

private theorem isInvertible_iteratedTwist (ideal : X.IdealSheafData)
    (invertible : ideal.IsInvertible) (lineBundle : X.Modules) [lineBundle.IsInvertible]
    (count : ℕ) : (iteratedTwist ideal lineBundle count).IsInvertible := by
  induction count with
  | zero => exact inferInstanceAs lineBundle.IsInvertible
  | succ count inductionHypothesis =>
    letI := inductionHypothesis
    exact invertible.isInvertible_twist (iteratedTwist ideal lineBundle count)

private theorem eulerChar_iteratedTwist (ideal : X.IdealSheafData)
    (invertible : ideal.IsInvertible) (lineBundle : X.Modules) [lineBundle.IsInvertible]
    (count : ℕ) :
    letI := ((ΓSpecIso (.of k)).inv ≫
      (ideal.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
    (iteratedTwist ideal lineBundle count).eulerChar k = lineBundle.eulerChar k +
      count * (Module.finrank k Γ(ideal.subscheme, ⊤) : ℤ) := by
  induction count with
  | zero => simp [iteratedTwist]
  | succ count inductionHypothesis =>
    letI := isInvertible_iteratedTwist ideal invertible lineBundle count
    change (ideal.twist (iteratedTwist ideal lineBundle count)).eulerChar k = _
    rw [eulerChar_twist (k := k) ideal invertible, inductionHypothesis]
    push_cast
    ring

include k in
private theorem exists_nonzero_section_iteratedTwist (ideal : X.IdealSheafData)
    (invertible : ideal.IsInvertible) (nonemptySupport : (ideal.support : Set X).Nonempty)
    (lineBundle : X.Modules) [lineBundle.IsInvertible] :
    ∃ count : ℕ, ∃ sectionMap : unit X ⟶ iteratedTwist ideal lineBundle count,
      sectionMap ≠ 0 := by
  letI := invertible.isFinite_subschemeι_comp (X ↘ Spec (.of k))
  letI : ideal.subscheme.Over (Spec (.of k)) := ⟨ideal.subschemeι ≫ (X ↘ Spec (.of k))⟩
  letI := (globalSectionsRingHom k (X := ideal.subscheme)).toAlgebra
  letI : Nonempty ideal.subscheme := by
    obtain ⟨point, membership⟩ := nonemptySupport
    rw [← IdealSheafData.range_subschemeι] at membership
    obtain ⟨point, _⟩ := membership
    exact ⟨point⟩
  letI : Nonempty (⊤ : ideal.subscheme.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  have finiteSections := (ideal.subschemeι ≫ (X ↘ Spec (.of k))).finite_appTop.comp
    (RingHom.Finite.of_surjective (ΓSpecIso (.of k)).inv.hom
      (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of k)).inv).2)
  letI : Module.Finite k Γ(ideal.subscheme, ⊤) := finiteSections
  have positiveLength : 0 < Module.finrank k Γ(ideal.subscheme, ⊤) := Module.finrank_pos
  let count := (1 - lineBundle.eulerChar k).toNat
  letI := isInvertible_iteratedTwist ideal invertible lineBundle count
  refine ⟨count, exists_nonzero_section_of_eulerChar_pos (k := k) _
    (cohomology_vanishing (k := k) _) ?_⟩
  rw [eulerChar_iteratedTwist (k := k) ideal invertible]
  have bound : 1 - lineBundle.eulerChar k ≤ (count : ℤ) := Int.self_le_toNat _
  have lengthBound : (count : ℤ) ≤ count * (Module.finrank k Γ(ideal.subscheme, ⊤) : ℤ) := by
    exact_mod_cast Nat.le_mul_of_pos_right count positiveLength
  omega

private theorem tensorEulerDefect_of_nonzero_section [IsIntegral X]
    (firstLine secondLine : X.Modules) [firstLine.IsInvertible] [secondLine.IsInvertible]
    (sectionMap : unit X ⟶ secondLine) (nonzeroSection : sectionMap ≠ 0) :
    tensorEulerDefect k firstLine secondLine = 0 := by
  obtain ⟨ideal, invertible, ⟨comparison⟩⟩ :=
    exists_iso_twist_unit_of_nonzero_section secondLine sectionMap nonzeroSection
  rw [tensorEulerDefect_iso_right firstLine comparison,
    tensorEulerDefect_twist ideal invertible, tensorEulerDefect_unit]

/-- A nonzero section of a line bundle on a smooth proper curve forces its
degree to be nonnegative: the degree is the length of its effective divisor. -/
theorem degree_nonneg_of_nonzero_section (lineBundle : X.Modules) [lineBundle.IsInvertible]
    (sectionMap : unit X ⟶ lineBundle) (nonzeroSection : sectionMap ≠ 0) :
    0 ≤ lineBundle.degree k := by
  letI : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  letI : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (X ↘ Spec (.of k))
  obtain ⟨ideal, invertible, ⟨comparison⟩⟩ :=
    exists_iso_twist_unit_of_nonzero_section lineBundle sectionMap nonzeroSection
  letI := ((ΓSpecIso (.of k)).inv ≫
    (ideal.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  have increment := eulerChar_twist (k := k) ideal invertible (unit X)
  have comparisonEuler := eulerChar_congr k comparison
  unfold degree
  have nonnegative : 0 ≤ (Module.finrank k Γ(ideal.subscheme, ⊤) : ℤ) := by
    positivity
  calc
    0 ≤ (Module.finrank k Γ(ideal.subscheme, ⊤) : ℤ) := nonnegative
    _ = lineBundle.eulerChar k - (unit X).eulerChar k := by
      rw [comparisonEuler, increment]
      ring

/-- Every section morphism into a negative-degree line bundle is zero. -/
theorem section_eq_zero_of_degree_neg (lineBundle : X.Modules) [lineBundle.IsInvertible]
    (negativeDegree : lineBundle.degree k < 0) (sectionMap : unit X ⟶ lineBundle) :
    sectionMap = 0 := by
  by_contra nonzeroSection
  have nonnegative := degree_nonneg_of_nonzero_section (k := k)
    lineBundle sectionMap nonzeroSection
  omega

/-- Negative-degree line bundles have no nonzero global sections. -/
theorem subsingleton_globalSections_of_degree_neg (lineBundle : X.Modules)
    [lineBundle.IsInvertible] (negativeDegree : lineBundle.degree k < 0) :
    Subsingleton Γ(lineBundle, ⊤) := by
  have zeroSection (sectionValue : Γ(lineBundle, ⊤)) : sectionValue = 0 := by
    have zeroMap := section_eq_zero_of_degree_neg (k := k) lineBundle negativeDegree
      ((unitHomAddEquiv lineBundle).symm sectionValue)
    apply (unitHomAddEquiv lineBundle).symm.injective
    simpa only [unitHomAddEquiv_symm_apply, map_zero] using zeroMap
  exact ⟨fun firstSection secondSection ↦
    (zeroSection firstSection).trans (zeroSection secondSection).symm⟩

/-- Zeroth cohomology of a negative-degree line bundle vanishes. -/
theorem subsingleton_H_zero_of_degree_neg (lineBundle : X.Modules) [lineBundle.IsInvertible]
    (negativeDegree : lineBundle.degree k < 0) : Subsingleton (lineBundle.H 0) := by
  letI := subsingleton_globalSections_of_degree_neg (k := k) lineBundle negativeDegree
  exact (H.zeroLinearEquiv lineBundle).injective.subsingleton

/-- The zeroth cohomological dimension of a negative-degree line bundle is zero. -/
theorem finrankH_zero_eq_zero_of_degree_neg (lineBundle : X.Modules) [lineBundle.IsInvertible]
    (negativeDegree : lineBundle.degree k < 0) : lineBundle.finrankH k 0 = 0 := by
  letI := subsingleton_H_zero_of_degree_neg (k := k) lineBundle negativeDegree
  simp only [finrankH, Module.finrank_zero_of_subsingleton]

/-- Degree is additive under tensor products of line bundles on a smooth proper
geometrically irreducible curve over any field. -/
theorem degree_tensorObj (firstLine secondLine : X.Modules)
    [firstLine.IsInvertible] [secondLine.IsInvertible] :
    (firstLine ⊗ secondLine).degree k = firstLine.degree k + secondLine.degree k := by
  letI : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  letI : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (X ↘ Spec (.of k))
  obtain ⟨ideal, invertible, nonemptySupport⟩ :=
    exists_nonempty_effectiveCartierDivisor (X ↘ Spec (.of k))
  obtain ⟨count, sectionMap, nonzeroSection⟩ :=
    exists_nonzero_section_iteratedTwist (k := k) ideal invertible nonemptySupport secondLine
  have twistInvariant (count : ℕ) :
      tensorEulerDefect k firstLine (iteratedTwist ideal secondLine count) =
        tensorEulerDefect k firstLine secondLine := by
    induction count with
    | zero => rfl
    | succ count inductionHypothesis =>
      letI := isInvertible_iteratedTwist ideal invertible secondLine count
      change tensorEulerDefect k firstLine (ideal.twist _) = _
      rw [tensorEulerDefect_twist (k := k) ideal invertible, inductionHypothesis]
  letI := isInvertible_iteratedTwist ideal invertible secondLine count
  have zeroDefect := tensorEulerDefect_of_nonzero_section (k := k) firstLine
    (iteratedTwist ideal secondLine count) sectionMap nonzeroSection
  rw [twistInvariant] at zeroDefect
  unfold tensorEulerDefect at zeroDefect
  unfold degree
  linarith

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Pic

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [GeometricallyIrreducible (X ↘ Spec (.of k))]

/-- Tensor product adds the degrees of Picard classes. -/
@[simp]
theorem degree_mul (firstClass secondClass : X.Pic) :
    degree k (firstClass * secondClass) = degree k firstClass + degree k secondClass := by
  rw [mul_def, degree_mk, Modules.degree_tensorObj]
  rfl

/-- Cohomological degree as a homomorphism from the Picard group. -/
def degreeHom : X.Pic →* Multiplicative ℤ where
  toFun := fun picardClass ↦ Multiplicative.ofAdd (degree k picardClass)
  map_one' := by simp [one_eq_mk_unit]
  map_mul' firstClass secondClass := by
    exact congrArg Multiplicative.ofAdd (degree_mul firstClass secondClass)

/-- Dualizing a line bundle negates its degree. -/
@[simp]
theorem degree_inv (picardClass : X.Pic) : degree k picardClass⁻¹ = -degree k picardClass :=
  congrArg Multiplicative.toAdd ((degreeHom (k := k)).map_inv picardClass)

end AlgebraicGeometry.Scheme.Pic
