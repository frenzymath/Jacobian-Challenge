import Jacobian.AlgebraicGeometry.Hilbert.TranslatedAbelMap.LocalSections.Divisors
import Jacobian.AlgebraicGeometry.Modules.AffineSections
import Jacobian.AlgebraicGeometry.Modules.HomSection
import Jacobian.AlgebraicGeometry.Modules.MatrixComplex
import Jacobian.AlgebraicGeometry.Modules.PrimitiveSection

/-!
# Affine local sections of the translated Abel map

For a pointed smooth proper geometrically irreducible curve of genus `g`, the
degree-`2g+1` translated Abel map admits a section on an affine neighbourhood of
each point of the degree-zero Picard representative. A local basis of the
positive Poincaré direct image supplies a primitive section. Its actual zero
divisor gives the Hilbert-valued section, and the equality with the inclusion
holds on the whole chart, without a reducedness assumption.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Hilbert

open Scheme

private def restrictedSection {source target : Scheme.{u}} (morphism : target ⟶ source)
    (moduleSheaf : source.Modules) {openSubset : source.Opens}
    (sectionValue : Γ(moduleSheaf, openSubset)) (image : ⊤ ≤ morphism ⁻¹ᵁ openSubset) :
    Modules.unit target ⟶ (Modules.pullback morphism).obj moduleSheaf :=
  Modules.homOfGlobalSection _
    (((Modules.pullback morphism).obj moduleSheaf).presheaf.map (homOfLE image).op
      (Modules.pullbackSection morphism sectionValue))

private theorem pullback_restrictedSection_ne_zero
    {source target furtherTarget : Scheme.{u}} (morphism : target ⟶ source)
    (furtherMorphism : furtherTarget ⟶ target) (moduleSheaf : source.Modules)
    {openSubset : source.Opens} (sectionValue : Γ(moduleSheaf, openSubset))
    (image : ⊤ ≤ morphism ⁻¹ᵁ openSubset)
    (nonzero : Modules.pullbackSection (furtherMorphism ≫ morphism) sectionValue ≠ 0) :
    (Modules.pullback furtherMorphism).map
      (restrictedSection morphism moduleSheaf sectionValue image) ≠ 0 := by
  let pulledModule := (Modules.pullback morphism).obj moduleSheaf
  let globalSection := pulledModule.presheaf.map (homOfLE image).op
    (Modules.pullbackSection morphism sectionValue)
  intro zeroMap
  have pulledSection_zero : Modules.pullbackSection furtherMorphism globalSection = 0 := by
    rw [← Modules.homOfGlobalSection_app_top_one pulledModule globalSection,
      Modules.pullbackSection_app_one]
    change Modules.Hom.app ((Modules.pullbackObjUnitIso furtherMorphism).inv ≫
      (Modules.pullback furtherMorphism).map
        (restrictedSection morphism moduleSheaf sectionValue image)) _ _ = 0
    rw [zeroMap, comp_zero, Modules.Hom.zero_app]
    rfl
  dsimp only [globalSection] at pulledSection_zero
  rw [Modules.pullbackSection_map] at pulledSection_zero
  have image_eq : morphism ⁻¹ᵁ openSubset = ⊤ := top_unique image
  have inclusion_eq : homOfLE (furtherMorphism.preimage_mono image) =
      eqToHom (congrArg (fun subset ↦ furtherMorphism ⁻¹ᵁ subset) image_eq).symm :=
    Subsingleton.elim _ _
  haveI : IsIso (homOfLE (furtherMorphism.preimage_mono image)) := by
    rw [inclusion_eq]
    infer_instance
  have iterated_zero : Modules.pullbackSection furtherMorphism
      (Modules.pullbackSection morphism sectionValue) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      (((Modules.pullback furtherMorphism).obj pulledModule).presheaf.map
        (homOfLE (furtherMorphism.preimage_mono image)).op)).1
    simpa only [map_zero] using pulledSection_zero
  have composition := Modules.pullbackSection_pullbackSection furtherMorphism morphism
    sectionValue
  have compatibility := congrArg
    (fun value ↦ Modules.Hom.app ((Modules.pullbackComp furtherMorphism morphism).hom.app
      moduleSheaf) ((furtherMorphism ≫ morphism) ⁻¹ᵁ openSubset) value) composition
  rw [iterated_zero, map_zero, Modules.natIso_hom_app_inv_app] at compatibility
  exact nonzero compatibility.symm

private def openParameter {base : Scheme.{u}} (parameter : Over base)
    (openSubset : parameter.left.Opens) : Over base :=
  Over.mk (openSubset.ι ≫ parameter.hom)

private def openParameterInclusion {base : Scheme.{u}} (parameter : Over base)
    (openSubset : parameter.left.Opens) : openParameter parameter openSubset ⟶ parameter :=
  Over.homMk openSubset.ι

private theorem productOpen_preimage {source base : Scheme.{u}}
    (structureMap : source ⟶ base) (parameter : Over base)
    (openSubset : parameter.left.Opens) :
    ⊤ ≤ baseChangeMap structureMap (openParameterInclusion parameter openSubset) ⁻¹ᵁ
      (pullback.snd structureMap parameter.hom ⁻¹ᵁ openSubset) := by
  have square : baseChangeMap structureMap (openParameterInclusion parameter openSubset) ≫
      pullback.snd structureMap parameter.hom =
        pullback.snd structureMap (openParameter parameter openSubset).hom ≫ openSubset.ι :=
    (isPullback_baseChangeMap structureMap
      (openParameterInclusion parameter openSubset)).w
  rw [← Scheme.Hom.comp_preimage, square, Scheme.Hom.comp_preimage,
    openSubset.ι_preimage_self, Scheme.Hom.preimage_top]

variable {baseField : Type u} [Field baseField] (curve : PointedCurve baseField)

local instance localSectionsCurveOver : curve.curve.carrier.left.Over
    (Spec (.of baseField)) := ⟨curve.curve.carrier.hom⟩

local instance localSectionsCurveProper :
    IsProper (curve.curve.carrier.left ↘ Spec (.of baseField)) := curve.curve.isProper

local instance localSectionsCurveSmoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  curve.curve.smoothOfRelativeDimension

local instance localSectionsCurveSmooth :
    Smooth (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  SmoothOfRelativeDimension.smooth 1 _

local instance localSectionsCurveGeometricallyIrreducible :
    GeometricallyIrreducible (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  curve.curve.geometricallyIrreducible

local instance localSectionsCurveGeometricallyIntegral :
    GeometricallyIntegral (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  Smooth.geometricallyIntegral _

private theorem markedTwistDegree (degree : ℕ) :
    Pic.degreeHom (k := baseField) (curve.pointIdealClass ^ degree) =
      Multiplicative.ofAdd (-(degree : ℤ)) := by
  change Multiplicative.ofAdd (Pic.degree baseField (curve.pointIdealClass ^ degree)) = _
  exact congrArg Multiplicative.ofAdd (curve.degree_pointIdealClass_pow degree)

variable {representative : Over (Spec (.of baseField))}
  (representation : (picardFunctorDegree curve.curve.carrier.hom 0).obj.RepresentableBy
    representative)

private def chartSection {openSubset : representative.left.Opens}
    (basis : Module.Basis
      (ULift.{u} (Fin (curve.curve.carrier.left.arithmeticGenus baseField + 2)))
      Γ(representative.left, openSubset)
      Γ((Modules.pushforward (pullback.snd curve.curve.carrier.hom representative.hom)).obj
        (curve.positivePoincareLineBundle representation
          (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)), openSubset))
    (basisIndex : ULift.{u} (Fin (curve.curve.carrier.left.arithmeticGenus baseField + 2))) :
    Modules.unit (pullback curve.curve.carrier.hom
      (openParameter representative openSubset).hom) ⟶
      (Modules.pullback (baseChangeMap curve.curve.carrier.hom
        (openParameterInclusion representative openSubset))).obj
          (curve.positivePoincareLineBundle representation
            (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)) :=
  restrictedSection
    (baseChangeMap curve.curve.carrier.hom (openParameterInclusion representative openSubset))
    (curve.positivePoincareLineBundle representation
      (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))
    (openSubset := pullback.snd curve.curve.carrier.hom representative.hom ⁻¹ᵁ openSubset)
    (basis basisIndex) (productOpen_preimage curve.curve.carrier.hom representative openSubset)

private theorem chartSection_after_affine_ne_zero {openSubset : representative.left.Opens}
    (affine : IsAffineOpen openSubset)
    (basis : Module.Basis
      (ULift.{u} (Fin (curve.curve.carrier.left.arithmeticGenus baseField + 2)))
      Γ(representative.left, openSubset)
      Γ((Modules.pushforward (pullback.snd curve.curve.carrier.hom representative.hom)).obj
        (curve.positivePoincareLineBundle representation
          (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)), openSubset))
    (basisIndex : ULift.{u} (Fin (curve.curve.carrier.left.arithmeticGenus baseField + 2)))
    {parameter : Over (Spec (.of baseField))}
    (parameterMap : parameter ⟶ openParameter representative openSubset)
    [IsAffine parameter.left] [Nontrivial Γ(parameter.left, ⊤)] :
    (Modules.pullback (baseChangeMap curve.curve.carrier.hom parameterMap)).map
      (chartSection curve representation basis basisIndex) ≠ 0 := by
  apply pullback_restrictedSection_ne_zero
  rw [← baseChangeMap_comp]
  have resolutions (parameter : Over (Spec (.of baseField))) :
      HasInjectiveResolutions (pullback curve.curve.carrier.hom parameter.hom).Modules := by
    have := Modules.isGrothendieckAbelian (pullback curve.curve.carrier.hom parameter.hom)
    infer_instance
  letI := resolutions
  apply Modules.pullback_basis_section_ne_zero curve.curve.carrier.hom
    (curve.positivePoincareLineBundle representation
      (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))
    (fun furtherParameter furtherChange ↦
      (curve.isFiniteLocallyFreeInDegree_positivePoincareLineBundle representation
        furtherChange.left (baseChangeMap curve.curve.carrier.hom furtherChange)
        (pullback.snd curve.curve.carrier.hom furtherParameter.hom)
        (isPullback_baseChangeMap curve.curve.carrier.hom furtherChange)).isZero 1 (by decide))
    affine basis basisIndex (parameterMap ≫ openParameterInclusion representative openSubset)
  change ⊤ ≤ (parameterMap.left ≫ openSubset.ι) ⁻¹ᵁ openSubset
  rw [Scheme.Hom.comp_preimage, openSubset.ι_preimage_self, Scheme.Hom.preimage_top]

private theorem chartSection_residue_ne_zero {openSubset : representative.left.Opens}
    (affine : IsAffineOpen openSubset)
    (basis : Module.Basis
      (ULift.{u} (Fin (curve.curve.carrier.left.arithmeticGenus baseField + 2)))
      Γ(representative.left, openSubset)
      Γ((Modules.pushforward (pullback.snd curve.curve.carrier.hom representative.hom)).obj
        (curve.positivePoincareLineBundle representation
          (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)), openSubset))
    (basisIndex : ULift.{u} (Fin (curve.curve.carrier.left.arithmeticGenus baseField + 2)))
    (point : (openParameter representative openSubset).left) :
    (Modules.pullback ((pullback.snd curve.curve.carrier.hom
      (openParameter representative openSubset).hom).fiberι point)).map
        (chartSection curve representation basis basisIndex) ≠ 0 := by
  let chart := openParameter representative openSubset
  let residueParameter : Over (Spec (.of baseField)) :=
    Over.mk (chart.left.fromSpecResidueField point ≫ chart.hom)
  let residueMap : residueParameter ⟶ chart := Over.homMk (chart.left.fromSpecResidueField point)
  haveI : IsAffine residueParameter.left := inferInstanceAs (IsAffine (Spec _))
  haveI : Nontrivial Γ(residueParameter.left, ⊤) :=
    (Scheme.ΓSpecIso (chart.left.residueField point)).commRingCatIsoToRingEquiv.nontrivial
  have nonzero := chartSection_after_affine_ne_zero curve representation affine basis basisIndex
    residueMap
  let projection := pullback.snd curve.curve.carrier.hom chart.hom
  let fibreChange := baseChangeMap curve.curve.carrier.hom residueMap
  let residueProjection := pullback.snd curve.curve.carrier.hom residueParameter.hom
  have square : fibreChange ≫ projection = residueProjection ≫ residueMap.left :=
    (isPullback_baseChangeMap curve.curve.carrier.hom residueMap).w
  let fibreMap : pullback curve.curve.carrier.hom residueParameter.hom ⟶ projection.fiber point :=
    pullback.lift fibreChange residueProjection square
  have projection_eq : fibreMap ≫ projection.fiberι point = fibreChange := pullback.lift_fst ..
  let comparison := Modules.pullbackComp fibreMap (projection.fiberι point) ≪≫
    Modules.pullbackCongr projection_eq
  intro zeroMap
  have pulled_zero : (Modules.pullback fibreMap).map
      ((Modules.pullback (projection.fiberι point)).map
        (chartSection curve representation basis basisIndex)) = 0 := by
    rw [zeroMap, Functor.map_zero]
  have compatibility := comparison.hom.naturality
    (chartSection curve representation basis basisIndex)
  apply nonzero
  apply (cancel_epi (comparison.hom.app (Modules.unit
    (pullback curve.curve.carrier.hom chart.hom)))).mp
  calc
    _ = (Modules.pullback fibreMap).map
        ((Modules.pullback (projection.fiberι point)).map
          (chartSection curve representation basis basisIndex)) ≫ comparison.hom.app _ :=
      compatibility.symm
    _ = 0 := by rw [pulled_zero, zero_comp]
    _ = _ := by rw [comp_zero]

private theorem chartLine_fibreDegree (openSubset : representative.left.Opens)
    (point : (openParameter representative openSubset).left) :
    SectionPencil.fibreDegree
      (pullback.snd curve.curve.carrier.hom (openParameter representative openSubset).hom)
      ((Modules.pullback (baseChangeMap curve.curve.carrier.hom
        (openParameterInclusion representative openSubset))).obj
          (curve.positivePoincareLineBundle representation
            (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))) point =
      (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1 : ℕ) := by
  let degree := 2 * curve.curve.carrier.left.arithmeticGenus baseField + 1
  let chart := openParameter representative openSubset
  let projection := pullback.snd curve.curve.carrier.hom chart.hom
  let lineBundle := (Modules.pullback (baseChangeMap curve.curve.carrier.hom
    (openParameterInclusion representative openSubset))).obj
      (curve.positivePoincareLineBundle representation degree)
  letI := projection.fiberOverSpecResidueField point
  have membership := (picardSubfunctorDegree curve.curve.carrier.hom (degree : ℤ)).map
    (openParameterInclusion representative openSubset).op
    (curve.positivePoincareLineBundle_mem representation degree)
  change Pic.map (baseChangeMap curve.curve.carrier.hom
    (openParameterInclusion representative openSubset))
      (Pic.mk (curve.positivePoincareLineBundle representation degree)) ∈
    (picardSubfunctorDegree curve.curve.carrier.hom (degree : ℤ)).obj (op chart) at membership
  rw [Pic.map_mk] at membership
  have constantDegree := (mem_picardSubfunctorDegree_iff curve.curve.carrier.hom
    (Pic.mk lineBundle) (degree : ℤ)).mp membership point
  have comparison := picardPresheafDegree_eq_degree curve.curve.carrier.hom
    (Pic.mk lineBundle) point
  have sameDegree := Modules.degree_congr (chart.left.residueField point)
    ((Modules.pullback (projection.fiberι point)).mapIso (Pic.mkIso lineBundle))
  exact sameDegree.symm.trans (comparison.symm.trans constantDegree)

/-- The actual marked translated Abel map in degree `2g+1` has affine Zariski
local sections. The positive line, local basis, section and Hilbert divisor are
constructed, and the right-inverse equation holds on the whole affine chart. -/
theorem translatedAbelMap_has_affine_local_sections
    {hilbertScheme : Over (Spec (.of baseField))}
    (hilbertRepresentation : (hilbertPresheaf curve.curve.carrier.hom
      (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)).RepresentableBy hilbertScheme)
    (point : representative.left) :
    ∃ openSubset : representative.left.Opens, IsAffineOpen openSubset ∧ point ∈ openSubset ∧
      ∃ sectionMap : Over.mk (openSubset.ι ≫ representative.hom) ⟶ hilbertScheme,
        sectionMap ≫ translatedAbelMap curve.curve
          (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1)
          (curve.pointIdealClass ^ (2 * curve.curve.carrier.left.arithmeticGenus baseField + 1))
          (markedTwistDegree curve _) hilbertRepresentation representation =
            Over.homMk openSubset.ι := by
  classical
  letI : Smooth curve.curve.carrier.hom :=
    SmoothOfRelativeDimension.smooth 1 curve.curve.carrier.hom
  letI : GeometricallyIntegral curve.curve.carrier.hom :=
    Smooth.geometricallyIntegral curve.curve.carrier.hom
  let degree := 2 * curve.curve.carrier.left.arithmeticGenus baseField + 1
  obtain ⟨openSubset, affine, point_mem, ⟨basis⟩⟩ :=
    curve.exists_affine_basis_pushforward_positivePoincareLineBundle representation point
  let basisIndex : ULift.{u} (Fin (curve.curve.carrier.left.arithmeticGenus baseField + 2)) :=
    ⟨⟨0, by omega⟩⟩
  let chart := openParameter representative openSubset
  let lineBundle := (Modules.pullback (baseChangeMap curve.curve.carrier.hom
    (openParameterInclusion representative openSubset))).obj
      (curve.positivePoincareLineBundle representation degree)
  let sectionMap := chartSection curve representation basis basisIndex
  have nonzero := chartSection_residue_ne_zero curve representation affine basis basisIndex
  have constantDegree := chartLine_fibreDegree curve representation openSubset
  let divisor := SectionPencil.hilbertPoint curve.curve.carrier.hom degree chart lineBundle
    sectionMap nonzero constantDegree
  let divisorMap : chart ⟶ hilbertScheme := hilbertRepresentation.homEquiv.symm divisor
  refine ⟨openSubset, affine, point_mem, divisorMap, ?_⟩
  change (divisorMap ≫ translatedAbelMap curve.curve degree
      (curve.pointIdealClass ^ degree) (markedTwistDegree curve degree)
      hilbertRepresentation representation : chart ⟶ representative) =
    openParameterInclusion representative openSubset
  apply representation.homEquiv.injective
  apply injective_picardFunctorDegreeι_app curve.curve.carrier.hom 0 chart
  calc
    _ = (toPicardFunctor curve.curve.carrier.hom).app (op chart)
        (abelClass curve.curve.carrier.hom (hilbertRepresentation.homEquiv divisorMap) *
          Pic.map (pullback.fst curve.curve.carrier.hom chart.hom)
            (curve.pointIdealClass ^ degree)) :=
      translatedAbelMap_classifies curve.curve degree (curve.pointIdealClass ^ degree)
        (markedTwistDegree curve degree) (parameter := chart)
        hilbertRepresentation representation divisorMap
    _ = _ := by
      dsimp only [divisorMap]
      rw [Equiv.apply_symm_apply, SectionPencil.abelClass_hilbertPoint]
      exact curve.positivePoincareLineBundle_pullback_translated_classifies representation
        (openParameterInclusion representative openSubset) degree

end AlgebraicGeometry.Hilbert
