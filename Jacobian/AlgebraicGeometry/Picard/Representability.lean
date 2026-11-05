import Jacobian.AlgebraicGeometry.Group.Representability
import Jacobian.AlgebraicGeometry.Hilbert.CurveGeometry
import Jacobian.AlgebraicGeometry.Picard.ChartRepresentability
import Jacobian.AlgebraicGeometry.Picard.RationalPoint
import Jacobian.AlgebraicGeometry.Picard.RepresentableGroup
import Jacobian.AlgebraicGeometry.Picard.TranslationCover

/-!
# The Picard scheme over a separably closed field

The relative Picard sheaf of a smooth proper geometrically integral curve over a
separably closed field is represented by a commutative group scheme. A rational
section identifies the Picard sheaf with normalized classes. The cohomology
chart is represented by an open of the genus Hilbert scheme, and its translates
cover field-valued points. The group representability criterion then applies.

The group law on the resulting representative classifies tensor product of
invertible sheaves. Neither a rational section nor a chart representative is
required as input to the existence theorem.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory Opposite TopologicalSpace
open scoped AlgebraicGeometry.Scheme.Modules MonObj

namespace AlgebraicGeometry

open Scheme

private lemma hom_ext_of_restrictAdjunction_unit {scheme : Scheme.{u}}
    {Index : Type*} (cover : Index → scheme.Opens)
    (covers : ∀ point : scheme, ∃ index, point ∈ cover index)
    {sourceModule targetModule : scheme.Modules} {firstMap secondMap : sourceModule ⟶ targetModule}
    (restrictionEquality : ∀ index,
      firstMap ≫ (Modules.restrictAdjunction (cover index).ι).unit.app targetModule =
        secondMap ≫ (Modules.restrictAdjunction (cover index).ι).unit.app targetModule) :
    firstMap = secondMap := by
  refine Modules.hom_ext _ _ fun openSubset ↦ ?_
  ext sectionValue
  let sheaf : TopCat.Sheaf AddCommGrpCat.{u} scheme :=
    ⟨targetModule.presheaf, targetModule.isSheaf⟩
  refine sheaf.eq_of_locally_eq'
    (fun index ↦ (cover index).ι ''ᵁ ((cover index).ι ⁻¹ᵁ openSubset)) openSubset
    (fun index ↦ homOfLE ((cover index).ι.image_preimage_le openSubset))
    (fun point membership ↦ ?_) _ _ fun index ↦ ?_
  · obtain ⟨index, chartMembership⟩ := covers point
    refine Opens.mem_iSup.mpr ⟨index, ?_⟩
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact ⟨chartMembership, membership⟩
  · exact congr(((($(restrictionEquality index)).app openSubset).hom sectionValue))

private theorem small_picard (scheme : Scheme.{u}) : Small.{u} scheme.Pic := by
  classical
  letI := Modules.isGrothendieckAbelian scheme
  let productModule : scheme.Modules := ∏ᶜ fun openSubset : scheme.Opens ↦
    (Modules.pushforward openSubset.ι).obj (SheafOfModules.unit openSubset.toScheme.ringCatSheaf)
  let embedding (moduleSheaf : scheme.Modules) : moduleSheaf ⟶ productModule :=
    Pi.lift fun openSubset ↦
      if trivialization : Nonempty (moduleSheaf.restrict openSubset.ι ≅
          SheafOfModules.unit openSubset.toScheme.ringCatSheaf) then
        (Modules.restrictAdjunction openSubset.ι).unit.app moduleSheaf ≫
          ((Modules.pushforward openSubset.ι).mapIso trivialization.some).hom
      else 0
  have embedding_mono (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible] :
      Mono (embedding moduleSheaf) := by
    refine ⟨fun firstMap secondMap equality ↦ hom_ext_of_restrictAdjunction_unit
      (fun chart : {openSubset : scheme.Opens // Nonempty (moduleSheaf.restrict openSubset.ι ≅
        SheafOfModules.unit openSubset.toScheme.ringCatSheaf)} ↦ chart.1)
      (fun point ↦ ?_) fun chart ↦ ?_⟩
    · obtain ⟨openSubset, membership, ⟨trivialization⟩⟩ :=
        Modules.exists_mem_over_iso_unit moduleSheaf point
      exact ⟨⟨openSubset, ⟨(Modules.restrictFunctorIsoPullback openSubset.ι).app moduleSheaf ≪≫
        Modules.pullbackIotaUnitIsoOfOverIso trivialization⟩⟩, membership⟩
    · have componentEquality := equality =≫ Pi.π _ chart.1
      simp only [Category.assoc, Pi.lift_π, embedding, dif_pos chart.2] at componentEquality
      rw [← Category.assoc, ← Category.assoc] at componentEquality
      exact (cancel_mono _).mp componentEquality
  let classSubobject (lineClass : scheme.Pic) : Subobject productModule :=
    letI := embedding_mono ((fromSkeleton scheme.Modules).obj lineClass.val)
    Subobject.mk (embedding ((fromSkeleton scheme.Modules).obj lineClass.val))
  refine small_of_injective (f := classSubobject) fun firstClass secondClass equality ↦ ?_
  rw [Pic.eq_iff_nonempty_iso]
  letI := embedding_mono ((fromSkeleton scheme.Modules).obj firstClass.val)
  letI := embedding_mono ((fromSkeleton scheme.Modules).obj secondClass.val)
  exact ⟨Subobject.isoOfMkEqMk _ _ equality⟩

variable {baseField : Type u} [Field baseField] [IsSepClosed baseField]
  {sourceScheme : Scheme.{u}}

private theorem exists_representableBy_picardFunctor_of_section
    (projection : sourceScheme ⟶ Spec (.of baseField))
    [SmoothOfRelativeDimension 1 projection] [IsProper projection]
    [GeometricallyIntegral projection]
    (sectionMap : Spec (.of baseField) ⟶ sourceScheme)
    (sectionEquation : sectionMap ≫ projection = 𝟙 _) :
    ∃ representing : Over (Spec (.of baseField)),
      Nonempty ((picardFunctor projection).obj.RepresentableBy representing) := by
  letI : sourceScheme.Over (Spec (.of baseField)) := ⟨projection⟩
  letI : IsProper (sourceScheme ↘ Spec (.of baseField)) :=
    inferInstanceAs (IsProper projection)
  letI : SmoothOfRelativeDimension 1 (sourceScheme ↘ Spec (.of baseField)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 projection)
  letI : GeometricallyIntegral (sourceScheme ↘ Spec (.of baseField)) :=
    inferInstanceAs (GeometricallyIntegral projection)
  letI : ∀ parameter : Over (Spec (.of baseField)),
      HasInjectiveResolutions (pullback (sourceScheme ↘ Spec (.of baseField))
        parameter.hom).Modules := fun parameter ↦ by
    letI := Modules.isGrothendieckAbelian
      (pullback (sourceScheme ↘ Spec (.of baseField)) parameter.hom)
    infer_instance
  let normalizedGroup := picardFunctorNormalizedGrp projection sectionMap sectionEquation
  let chart := picardFunctorInvertibleDirectImage projection sectionMap sectionEquation
  obtain ⟨hilbertScheme, hilbertProjection, _, _, _, ⟨hilbertRepresentation⟩⟩ :=
    hilbertPresheaf_curve_representable projection (sourceScheme.arithmeticGenus baseField)
  obtain ⟨chartScheme, chartInclusion, _, ⟨chartRepresentation⟩⟩ :=
    isRepresentable_picardFunctorInvertibleDirectImage sectionMap sectionEquation
      (Over.mk hilbertProjection) hilbertRepresentation
  have smallValues (parameter : (Over (Spec (.of baseField)))ᵒᵖ) :
      Small.{u} ((normalizedGroup ⋙ forget GrpCat.{u + 1}).obj parameter) := by
    letI := small_picard (pullback projection parameter.unop.hom)
    exact small_subtype _ _
  obtain ⟨representing, _, ⟨representation⟩⟩ :=
    isRepresentable_of_representable_open_subfunctor normalizedGroup chart smallValues
      (isSheaf_zariski_picardFunctorNormalized projection sectionMap sectionEquation
        isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral)
      chartRepresentation.isRepresentable
      (isOpenImmersion_picardFunctorInvertibleDirectImage_ι projection sectionMap sectionEquation)
      (exists_mul_mem_picardFunctorInvertibleDirectImage sectionMap sectionEquation)
  exact ⟨representing,
    ⟨representation.ofIso (normalizedPicardIso sectionMap sectionEquation)⟩⟩

/-- The full relative Picard sheaf of a smooth proper geometrically integral
curve over a separably closed field has a scheme representative. -/
theorem exists_representableBy_picardFunctor
    (projection : sourceScheme ⟶ Spec (.of baseField))
    [SmoothOfRelativeDimension 1 projection] [IsProper projection]
    [GeometricallyIntegral projection] :
    ∃ representing : Over (Spec (.of baseField)),
      Nonempty ((picardFunctor projection).obj.RepresentableBy representing) := by
  letI : Smooth projection := SmoothOfRelativeDimension.smooth 1 projection
  letI : IsIntegral sourceScheme := GeometricallyIntegral.isIntegral_of_subsingleton projection
  obtain ⟨sectionMap, sectionEquation⟩ := projection.exists_section_of_isSepClosed
  exact exists_representableBy_picardFunctor_of_section projection sectionMap sectionEquation

/-- The Picard sheaf of a smooth proper geometrically integral curve over a
separably closed field is represented by a commutative group scheme whose
multiplication classifies tensor products of invertible sheaves. -/
theorem isRepresentable_picardFunctor
    (projection : sourceScheme ⟶ Spec (.of baseField))
    [SmoothOfRelativeDimension 1 projection] [IsProper projection]
    [GeometricallyIntegral projection] :
    ∃ (representing : Over (Spec (.of baseField))) (groupStructure : CommGrpObj representing)
      (representation : (picardFunctor projection).obj.RepresentableBy representing),
      letI := groupStructure
      ∀ (parameter : Over (Spec (.of baseField)))
        (firstClass secondClass : (pullback projection parameter.hom).Pic),
        representation.homEquiv.symm
            ((toPicardFunctor projection).app (op parameter) (firstClass * secondClass)) =
          representation.homEquiv.symm ((toPicardFunctor projection).app (op parameter) firstClass) *
            representation.homEquiv.symm
              ((toPicardFunctor projection).app (op parameter) secondClass) := by
  obtain ⟨representing, ⟨representation⟩⟩ := exists_representableBy_picardFunctor projection
  refine ⟨representing, picardFunctorCommGrpObj projection representation, representation, ?_⟩
  exact fun parameter firstClass secondClass ↦
    homEquiv_symm_toPicardFunctor_mul projection representation firstClass secondClass

end AlgebraicGeometry
