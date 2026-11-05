import Jacobian.AlgebraicGeometry.Picard.Poincare
import Jacobian.AlgebraicGeometry.Picard.DegreeTranslation
import Jacobian.AlgebraicGeometry.PointedCurve.Divisor
import Jacobian.AlgebraicGeometry.Modules.PositiveFamilyCohomology
import Jacobian.AlgebraicGeometry.Modules.LocallyFreeAffine
import Mathlib.LinearAlgebra.StdBasis

/-!
# Positive twists of the Poincaré line bundle

The inverse of the marked-point ideal has degree one. Tensoring the normalized
Poincaré bundle with its nth power therefore gives a line bundle of fibre degree
n. For n = 2g + 1, Riemann--Roch gives fibre cohomology of rank g + 2 in degree
zero, universally after arbitrary base change. In particular the actual
underived pushforward has an affine local basis at every parameter point.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.PointedCurve

open Scheme

variable {baseField : Type u} [Field baseField] (curve : PointedCurve baseField)

local instance positivePoincareCurveOver : curve.curve.carrier.left.Over (Spec (.of baseField)) :=
  ⟨curve.curve.carrier.hom⟩

local instance positivePoincareCurveProper :
    IsProper (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  curve.curve.isProper

local instance positivePoincareCurveSmoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  curve.curve.smoothOfRelativeDimension

local instance positivePoincareCurveSmooth :
    Smooth (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  SmoothOfRelativeDimension.smooth 1 (curve.curve.carrier.left ↘ Spec (.of baseField))

local instance positivePoincareCurveGeometricallyIrreducible :
    GeometricallyIrreducible (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  curve.curve.geometricallyIrreducible

local instance positivePoincareCurveGeometricallyIntegral :
    GeometricallyIntegral (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  Smooth.geometricallyIntegral (curve.curve.carrier.left ↘ Spec (.of baseField))

private theorem point_over : curve.point.left ≫ curve.curve.carrier.hom = 𝟙 _ := by
  simpa using Over.w curve.point

variable {representative : Over (Spec (.of baseField))}
  (representation : (picardFunctorDegree curve.curve.carrier.hom 0).obj.RepresentableBy
    representative)

local instance positivePoincareProductInvertible :
    (show (pullback curve.curve.carrier.hom representative.hom).Modules from
      poincareLineBundle (source := curve.curve.carrier.left)
        curve.point.left (point_over curve) representation).IsInvertible := by
  change (poincareLineBundle (source := curve.curve.carrier.left)
    curve.point.left (point_over curve) representation).IsInvertible
  exact isInvertible_poincareLineBundle (source := curve.curve.carrier.left)
    curve.point.left (point_over curve) representation

/-- The universal positive line bundle is an actual tensor product with the
pullback of the inverse marked-point ideal class. -/
def positivePoincareLineBundle (exponent : ℕ) :
    (pullback curve.curve.carrier.hom representative.hom).Modules :=
  (show (pullback curve.curve.carrier.hom representative.hom).Modules from
    poincareLineBundle (source := curve.curve.carrier.left)
      curve.point.left (point_over curve) representation) ⊗
    (Modules.pullback (pullback.fst curve.curve.carrier.hom representative.hom)).obj
      ((fromSkeleton curve.curve.carrier.left.Modules).obj
        ((curve.pointIdealClass ^ exponent)⁻¹).val)

instance isInvertible_positivePoincareLineBundle (exponent : ℕ) :
    (curve.positivePoincareLineBundle representation exponent).IsInvertible := by
  dsimp only [positivePoincareLineBundle]
  infer_instance

/-- The sign of the twist is opposite to the negative class used by the
translated Abel map. -/
theorem positivePoincareLineBundle_class (exponent : ℕ) :
    Pic.mk (curve.positivePoincareLineBundle representation exponent) =
      Pic.mk (show (pullback curve.curve.carrier.hom representative.hom).Modules from
        poincareLineBundle (source := curve.curve.carrier.left)
          curve.point.left (point_over curve) representation) *
        Pic.map (pullback.fst curve.curve.carrier.hom representative.hom)
          (curve.pointIdealClass ^ exponent)⁻¹ := by
  dsimp only [positivePoincareLineBundle]
  rw [Pic.mk_tensorObj, ← Pic.map_mk, Pic.mk_fromSkeleton]

/-- The constructed positive line has fibre degree n on every field-valued
point of every parameter scheme. -/
theorem positivePoincareLineBundle_mem (exponent : ℕ) :
    Pic.mk (curve.positivePoincareLineBundle representation exponent) ∈
      (picardSubfunctorDegree curve.curve.carrier.hom (exponent : ℤ)).obj
        (op representative) := by
  have twistDegree : Pic.degreeHom (k := baseField) (curve.pointIdealClass ^ exponent)⁻¹ =
      Multiplicative.ofAdd (exponent : ℤ) := by
    apply Multiplicative.toAdd.injective
    change Pic.degree baseField (curve.pointIdealClass ^ exponent)⁻¹ = (exponent : ℤ)
    rw [Pic.degree_inv, curve.degree_pointIdealClass_pow]
    omega
  rw [positivePoincareLineBundle_class]
  have normalizedDegree := @poincareLineBundle_mem baseField _ curve.curve.carrier.left
    (positivePoincareCurveOver (curve := curve))
    (positivePoincareCurveProper (curve := curve))
    (positivePoincareCurveGeometricallyIntegral (curve := curve))
    curve.point.left (point_over curve) representative representation
  have translatedDegree := @mul_map_fst_mem_picardSubfunctorDegree
    baseField _ curve.curve.carrier.left (positivePoincareCurveOver (curve := curve))
    (positivePoincareCurveProper (curve := curve))
    (positivePoincareCurveSmoothOfRelativeDimension (curve := curve))
    (positivePoincareCurveGeometricallyIrreducible (curve := curve))
    representative 0 (exponent : ℤ) (curve.pointIdealClass ^ exponent)⁻¹ twistDegree
    _ normalizedDegree
  change Pic.mk (show (pullback curve.curve.carrier.hom representative.hom).Modules from
      poincareLineBundle (source := curve.curve.carrier.left)
        curve.point.left (point_over curve) representation) *
      Pic.map (pullback.fst curve.curve.carrier.hom representative.hom)
        (curve.pointIdealClass ^ exponent)⁻¹ ∈
    (picardSubfunctorDegree curve.curve.carrier.hom (0 + (exponent : ℤ))).obj
      (op representative) at translatedDegree
  simpa only [zero_add] using translatedDegree

/-- The same degree is computed on each literal residue-field fibre. -/
theorem degree_fibre_positivePoincareLineBundle (exponent : ℕ) (point : representative.left) :
    let projection := pullback.snd curve.curve.carrier.hom representative.hom
    letI := projection.fiberOverSpecResidueField point
    ((Modules.pullback (projection.fiberι point)).obj
      (curve.positivePoincareLineBundle representation exponent)).degree
        (representative.left.residueField point) = (exponent : ℤ) := by
  let projection := pullback.snd curve.curve.carrier.hom representative.hom
  letI := projection.fiberOverSpecResidueField point
  let lineBundle := curve.positivePoincareLineBundle representation exponent
  have constantDegree := (mem_picardSubfunctorDegree_iff curve.curve.carrier.hom
    (Pic.mk lineBundle) (exponent : ℤ)).mp
      (curve.positivePoincareLineBundle_mem representation exponent) point
  have comparison := picardPresheafDegree_eq_degree curve.curve.carrier.hom
    (Pic.mk lineBundle) point
  have sameDegree := Modules.degree_congr (representative.left.residueField point)
    ((Modules.pullback (projection.fiberι point)).mapIso (Pic.mkIso lineBundle))
  exact sameDegree.symm.trans (comparison.symm.trans constantDegree)

private theorem arithmeticGenus_residueFibre (point : representative.left) :
    let projection := pullback.snd curve.curve.carrier.hom representative.hom
    letI := projection.fiberOverSpecResidueField point
    (projection.fiber point).arithmeticGenus (representative.left.residueField point) =
      curve.curve.carrier.left.arithmeticGenus baseField := by
  let projection := pullback.snd curve.curve.carrier.hom representative.hom
  letI := projection.fiberOverSpecResidueField point
  let unitSheaf : curve.curve.carrier.left.Modules :=
    SheafOfModules.unit curve.curve.carrier.left.ringCatSheaf
  calc
    (projection.fiber point).arithmeticGenus (representative.left.residueField point) =
        Modules.hFiber (SheafOfModules.unit (pullback curve.curve.carrier.hom
          representative.hom).ringCatSheaf) projection 1 point :=
      (Modules.finrankH_congr (representative.left.residueField point)
        (Modules.pullbackObjUnitIso (projection.fiberι point)) 1).symm
    _ = Modules.hFiber
        ((Modules.pullback (pullback.fst curve.curve.carrier.hom representative.hom)).obj
          unitSheaf) projection 1 point :=
      (Modules.hFiber_congr (Modules.pullbackObjUnitIso _ ) projection 1 point).symm
    _ = Modules.hFiber unitSheaf curve.curve.carrier.hom 1 (representative.hom point) :=
      Modules.hFiber_pullback_of_isPullback curve.curve.carrier.hom unitSheaf
        representative.hom (pullback.fst _ _) projection
        (IsPullback.of_hasPullback _ _) 1 point
    _ = curve.curve.carrier.left.arithmeticGenus baseField :=
      Modules.hFiber_eq_finrankH curve.curve.carrier.hom unitSheaf 1 _

private theorem positivePoincareLineBundle_fibre_bound (point : representative.left) :
    let projection := pullback.snd curve.curve.carrier.hom representative.hom
    letI := projection.fiberOverSpecResidueField point
    2 * ((projection.fiber point).arithmeticGenus (representative.left.residueField point) : ℤ) -
        2 < ((Modules.pullback (projection.fiberι point)).obj
          (curve.positivePoincareLineBundle representation
            (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))).degree
              (representative.left.residueField point) := by
  dsimp only
  rw [degree_fibre_positivePoincareLineBundle, arithmeticGenus_residueFibre]
  omega

/-- The positive universal line has exactly g+2 sections on each residue fibre. -/
theorem hFiber_zero_positivePoincareLineBundle (point : representative.left) :
    (curve.positivePoincareLineBundle representation
      (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)).hFiber
        (pullback.snd curve.curve.carrier.hom representative.hom) 0 point =
      curve.curve.carrier.left.arithmeticGenus baseField + 2 := by
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd curve.curve.carrier.hom representative.hom) :=
    MorphismProperty.pullback_snd _ _ curve.curve.smoothOfRelativeDimension
  have dimensions := Modules.hFiber_zero_eq_degree_add_one_sub_genus
    (pullback.snd curve.curve.carrier.hom representative.hom)
    (curve.positivePoincareLineBundle representation
      (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)) point
    (positivePoincareLineBundle_fibre_bound curve representation point)
  rw [degree_fibre_positivePoincareLineBundle, arithmeticGenus_residueFibre] at dimensions
  omega

/-- Universally, the constructed positive Poincaré line has finite locally free
direct image of rank g+2 in degree zero and no positive higher direct images. -/
theorem isFiniteLocallyFreeInDegree_positivePoincareLineBundle
    {changedBase changedSource : Scheme.{u}}
    (baseChange : changedBase ⟶ representative.left)
    (sourceChange : changedSource ⟶ pullback curve.curve.carrier.hom representative.hom)
    (changedFamily : changedSource ⟶ changedBase)
    [HasInjectiveResolutions changedSource.Modules]
    (square : IsPullback sourceChange changedFamily
      (pullback.snd curve.curve.carrier.hom representative.hom) baseChange) :
    Modules.IsFiniteLocallyFreeInDegree
      (fun degree ↦ (Modules.higherDirectImage changedFamily degree).obj
        ((Modules.pullback sourceChange).obj (curve.positivePoincareLineBundle representation
          (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))))
      0 (curve.curve.carrier.left.arithmeticGenus baseField + 2) := by
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1
      (pullback.snd curve.curve.carrier.hom representative.hom) :=
    MorphismProperty.pullback_snd _ _ curve.curve.smoothOfRelativeDimension
  exact Modules.isFiniteLocallyFreeInDegree_of_positive_fibres
    (pullback.snd curve.curve.carrier.hom representative.hom) _ _
    (positivePoincareLineBundle_fibre_bound curve representation)
    (curve.hFiber_zero_positivePoincareLineBundle representation)
    baseChange sourceChange changedFamily square

/-- The actual underived pushforward, not a supplied locally free replacement,
has rank g+2. -/
theorem isFiniteLocallyFreeOfRank_pushforward_positivePoincareLineBundle :
    ((Modules.pushforward (pullback.snd curve.curve.carrier.hom representative.hom)).obj
      (curve.positivePoincareLineBundle representation
        (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))).IsFiniteLocallyFreeOfRank
      (curve.curve.carrier.left.arithmeticGenus baseField + 2) := by
  have := Modules.isGrothendieckAbelian
    (pullback curve.curve.carrier.hom representative.hom)
  let projection := pullback.snd curve.curve.carrier.hom representative.hom
  let lineBundle := curve.positivePoincareLineBundle representation
    (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)
  have concentration := curve.isFiniteLocallyFreeInDegree_positivePoincareLineBundle
    representation (𝟙 _) (𝟙 _) projection
      (IsPullback.of_horiz_isIso ⟨by simp only [projection, Category.id_comp, Category.comp_id]⟩)
  letI := concentration.isFiniteLocallyFreeOfRank
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    (((Modules.higherDirectImage projection 0).mapIso
      ((Modules.pullbackId _).app lineBundle)) ≪≫
      (Functor.rightDerivedZeroIsoSelf (Modules.pushforward projection)).app lineBundle)

/-- An affine neighbourhood and basis of sections are constructed at every
point; no local-basis or section certificate is an input. -/
theorem exists_affine_basis_pushforward_positivePoincareLineBundle
    (point : representative.left) :
    ∃ openSubset : representative.left.Opens, IsAffineOpen openSubset ∧ point ∈ openSubset ∧
      Nonempty (Module.Basis
        (ULift.{u} (Fin (curve.curve.carrier.left.arithmeticGenus baseField + 2)))
        Γ(representative.left, openSubset)
        Γ((Modules.pushforward (pullback.snd curve.curve.carrier.hom representative.hom)).obj
          (curve.positivePoincareLineBundle representation
            (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)), openSubset)) := by
  classical
  let directImage :=
    (Modules.pushforward (pullback.snd curve.curve.carrier.hom representative.hom)).obj
      (curve.positivePoincareLineBundle representation
        (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))
  letI := curve.isFiniteLocallyFreeOfRank_pushforward_positivePoincareLineBundle representation
  obtain ⟨index, localOpen, cover, trivialization⟩ :=
    Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free directImage
      (r := curve.curve.carrier.left.arithmeticGenus baseField + 2)
  obtain ⟨localIndex, membership⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (cover.ge (Set.mem_univ point) : point ∈ ⨆ localIndex, localOpen localIndex)
  obtain ⟨openSubset, affine, point_mem, inclusion⟩ :=
    exists_isAffineOpen_mem_and_subset membership
  let coordinates := Modules.sectionsLinearEquivOfOverIsoFree
    ((Modules.overIsoFreeEquiv directImage (localOpen localIndex)
      (ULift.{u} (Fin (curve.curve.carrier.left.arithmeticGenus baseField + 2)))).symm
      (trivialization localIndex).some) inclusion
  exact ⟨openSubset, affine, point_mem,
    ⟨(Pi.basisFun Γ(representative.left, openSubset) _).map coordinates.symm⟩⟩

end AlgebraicGeometry.PointedCurve
