import Jacobian.AlgebraicGeometry.Cohomology.FieldExtension
import Jacobian.AlgebraicGeometry.Curve.Cohomology
import Jacobian.AlgebraicGeometry.IdealSheaf.Curve
import Jacobian.AlgebraicGeometry.Modules.ZeroLocusTensor
import Jacobian.AlgebraicGeometry.Picard.AbelMap
import Jacobian.AlgebraicGeometry.Picard.DegreeBaseChange
import Jacobian.AlgebraicGeometry.Picard.DegreeCartier
import Jacobian.AlgebraicGeometry.Sites.FppfGeometricPoints

/-!
# Effectivity in degree equal to the genus

On a smooth proper geometrically irreducible curve, every line-bundle class
of degree equal to the genus has a nonzero section. Its zero divisor realizes
the class in the degree-genus Hilbert functor. This construction works after
any extension of the ground field, without a rational point on the curve.
Over an algebraically closed extension this also gives every degree-genus
section of the Picard sheaf as the image of the Abel map.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe curveUniverse

open CategoryTheory Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme

variable {baseField : Type curveUniverse} [Field baseField]
  {source : Scheme.{curveUniverse}} [source.Over (Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
  [IsProper (source ↘ Spec (.of baseField))]
  [GeometricallyIrreducible (source ↘ Spec (.of baseField))]

/-- Every degree-genus Picard class over a field extension is the Abel class
of an effective divisor of that degree. -/
theorem exists_abelClass_eq (extensionField : Type curveUniverse) [Field extensionField]
    [Algebra baseField extensionField]
    (picardClass : (picardSubfunctorDegree (source ↘ Spec (.of baseField))
      (source.arithmeticGenus baseField)).toFunctor.obj
        (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))))) :
    ∃ divisor : (hilbertPresheaf (source ↘ Spec (.of baseField))
        (source.arithmeticGenus baseField)).obj
          (op (Over.mk (Spec.map (CommRingCat.ofHom
            (algebraMap baseField extensionField))))),
      abelClass (source ↘ Spec (.of baseField)) divisor = picardClass.1 := by
  let structureMap := source ↘ Spec (.of baseField)
  let parameter := Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap baseField extensionField)))
  let baseChanged := pullback structureMap parameter.hom
  let projection : baseChanged ⟶ Spec (.of extensionField) :=
    pullback.snd structureMap parameter.hom
  letI : baseChanged.Over (Spec (.of extensionField)) := ⟨projection⟩
  have cartesian := IsPullback.of_hasPullback structureMap parameter.hom
  have : Smooth structureMap := SmoothOfRelativeDimension.smooth 1 structureMap
  have : GeometricallyIntegral structureMap := inferInstance
  have : SmoothOfRelativeDimension 1 projection :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback cartesian
      (inferInstanceAs (SmoothOfRelativeDimension 1 structureMap))
  have : IsProper projection := IsProper.isStableUnderBaseChange.of_isPullback cartesian
    (inferInstanceAs (IsProper structureMap))
  have : GeometricallyIntegral projection := MorphismProperty.of_isPullback cartesian
    (inferInstanceAs (GeometricallyIntegral structureMap))
  have : IsProper (baseChanged ↘ Spec (.of extensionField)) := by
    change IsProper projection
    infer_instance
  have : GeometricallyIntegral (baseChanged ↘ Spec (.of extensionField)) := by
    change GeometricallyIntegral projection
    infer_instance
  have : Subsingleton (Spec (.of extensionField)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum extensionField))
  have : IsIntegral baseChanged := GeometricallyIntegral.isIntegral_of_subsingleton projection
  let extensionCurve : Curve extensionField :=
    { carrier := Over.mk projection
      isProper := inferInstanceAs (IsProper projection)
      smoothOfRelativeDimension := inferInstanceAs (SmoothOfRelativeDimension 1 projection)
      geometricallyIrreducible := inferInstanceAs (GeometricallyIrreducible projection) }
  let lineSheaf : baseChanged.Modules := (fromSkeleton _).obj picardClass.1.val
  have : lineSheaf.IsInvertible := picardClass.1.isInvertible
  have lineDegree : lineSheaf.degree extensionField = source.arithmeticGenus baseField := by
    have degreeAtPoint := picardClass.2 extensionField (𝟙 parameter)
    rw [picardFibreDegree] at degreeAtPoint
    rw [baseChangeMap_id _ parameter, Pic.map_id] at degreeAtPoint
    exact degreeAtPoint
  have genusEquality : baseChanged.arithmeticGenus extensionField =
      source.arithmeticGenus baseField := arithmeticGenus_pullback extensionField
  have unitEuler : Modules.eulerChar extensionField (SheafOfModules.unit baseChanged.ringCatSheaf) =
      1 - (baseChanged.arithmeticGenus extensionField : ℤ) :=
    Modules.eulerChar_unit_eq_one_sub_genus (k := extensionField) (X := baseChanged)
      (fun degree larger ↦ extensionCurve.subsingleton_H _ larger)
  have positiveEuler : 0 < lineSheaf.eulerChar extensionField := by
    change lineSheaf.eulerChar extensionField -
      Modules.eulerChar extensionField (SheafOfModules.unit baseChanged.ringCatSheaf) =
        (source.arithmeticGenus baseField : ℤ) at lineDegree
    rw [unitEuler, genusEquality] at lineDegree
    omega
  obtain ⟨sectionMap, nonzero⟩ := Modules.exists_nonzero_section_of_eulerChar_pos
    (k := extensionField) lineSheaf
    (fun degree larger ↦ extensionCurve.subsingleton_H _ larger) positiveEuler
  let divisor := sectionMap.zeroLocus
  have regular : divisor.IsInvertible := Modules.Hom.isInvertible_zeroLocus nonzero
  have : divisor.toModules.IsInvertible := regular.isInvertible_toModules
  have : divisor.toModulesᵛ.IsInvertible := regular.isInvertible_dual_toModules
  obtain ⟨tensorComparison⟩ :=
    Modules.Hom.nonempty_iso_dual_toModules_tensorObj sectionMap regular
  let lineComparison : lineSheaf ≅ divisor.toModulesᵛ := tensorComparison ≪≫ ρ_ _
  have : IsFinite (divisor.subschemeι ≫ projection) :=
    regular.isFinite_subschemeι_comp projection
  have : IsFinite (divisor.subschemeι ≫ baseChanged ↘ Spec (.of extensionField)) := by
    change IsFinite (divisor.subschemeι ≫ projection)
    infer_instance
  have : (divisor.twist (Modules.unit baseChanged)).IsInvertible :=
    regular.isInvertible_twist _
  have (degree : ℕ) : Module.Finite extensionField ((Modules.unit baseChanged).H degree) :=
    extensionCurve.hasFiniteH _ degree
  have (degree : ℕ) :
      Module.Finite extensionField ((divisor.twist (Modules.unit baseChanged)).H degree) :=
    extensionCurve.hasFiniteH _ degree
  have increment := regular.degree_twist_eq_add_finrank (k := extensionField)
    (Modules.unit baseChanged) 1
    (fun degree larger ↦ extensionCurve.subsingleton_H _ larger)
    (fun degree larger ↦ extensionCurve.subsingleton_H _ larger)
  rw [Modules.degree_unit] at increment
  change (𝟙_ baseChanged.Modules ⊗ divisor.toModulesᵛ).degree extensionField =
    0 + ((divisor.subschemeι ≫ projection).finrankΓ : ℤ) at increment
  have divisorDegree : divisor.toModulesᵛ.degree extensionField =
      ((divisor.subschemeι ≫ projection).finrankΓ : ℤ) :=
    (Modules.degree_congr extensionField (λ_ divisor.toModulesᵛ)).symm.trans
      (by simpa only [zero_add] using increment)
  have finiteRank : (divisor.subschemeι ≫ projection).finrankΓ =
      source.arithmeticGenus baseField := by
    have degreeEquality := divisorDegree.symm.trans
      ((Modules.degree_congr extensionField lineComparison).symm.trans lineDegree)
    exact_mod_cast degreeEquality
  have : Flat (divisor.subschemeι ≫ projection) := inferInstance
  have : LocallyOfFinitePresentation (divisor.subschemeι ≫ projection) := inferInstance
  refine ⟨⟨divisor, inferInstance, inferInstance, inferInstance, fun point ↦ ?_⟩, ?_⟩
  · exact (Scheme.Hom.finrank_eq_finrankΓ_of_field
      (divisor.subschemeι ≫ projection) point).trans finiteRank
  · exact Pic.eq_iff_nonempty_iso.2
      ⟨abelClassIso (source ↘ Spec (.of baseField)) _ ≪≫ lineComparison.symm⟩

/-- Every degree-genus section of the Picard sheaf over an algebraically
closed field extension is in the image of the Abel map. -/
theorem exists_hilbertToPicard_eq_of_degree_genus
    (extensionField : Type curveUniverse) [Field extensionField]
    [Algebra baseField extensionField] [IsAlgClosed extensionField]
    (picardSection : (picardFunctorDegree (source ↘ Spec (.of baseField))
      (source.arithmeticGenus baseField)).obj.obj
        (op (Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap baseField extensionField)))))) :
    ∃ divisor : (hilbertPresheaf (source ↘ Spec (.of baseField))
        (source.arithmeticGenus baseField)).obj
          (op (Over.mk (Spec.map (CommRingCat.ofHom
            (algebraMap baseField extensionField))))),
      (hilbertToPicard (source ↘ Spec (.of baseField))
        (source.arithmeticGenus baseField)).app _ ⟨divisor⟩ =
          (picardFunctorDegreeι (source ↘ Spec (.of baseField))
            (source.arithmeticGenus baseField)).hom.app _ picardSection := by
  obtain ⟨representative, representative_eq⟩ :=
    surjective_toSheafify_app_of_isAlgClosed
      (picardSubfunctorDegree (source ↘ Spec (.of baseField))
        (source.arithmeticGenus baseField)).toFunctor picardSection
  obtain ⟨divisor, divisor_eq⟩ := exists_abelClass_eq extensionField representative
  refine ⟨divisor, ?_⟩
  change (toPicardFunctor (source ↘ Spec (.of baseField))).app _
    (abelClass (source ↘ Spec (.of baseField)) divisor) = _
  rw [divisor_eq, ← representative_eq]
  exact (picardFunctorDegreeι_app_toSheafify (source ↘ Spec (.of baseField))
    (source.arithmeticGenus baseField) representative).symm

end AlgebraicGeometry
