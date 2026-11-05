import Jacobian.AlgebraicGeometry.ProjectiveLine.RelativeCoordinates
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Scaling on the relative projective line

The intersection of the two standard charts parametrizes multiplicative scaling.
The chart maps glue because the two affine coordinates are reciprocal. Scaling
fixes zero, specializes to the identity at one, and the orbit of `[1:1]` is the
dense chart intersection.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry.ProjectiveSpace
open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProjectiveLine

/-- The common locus of the two standard charts of the relative projective line. -/
def relativeOverlap (base : Scheme.{u}) : ℙ((ULift.{u} (Fin 2)); base).Opens :=
  standardOpen (ULift.{u} (Fin 2)) base ⟨0⟩ ⊓ standardOpen (ULift.{u} (Fin 2)) base ⟨1⟩

lemma relativeOverlap_le_standardOpen (base : Scheme.{u}) (coordinate : ULift.{u} (Fin 2)) :
    relativeOverlap base ≤ standardOpen (ULift.{u} (Fin 2)) base coordinate := by
  rcases coordinate with ⟨coordinate⟩
  fin_cases coordinate
  · exact inf_le_left
  · exact inf_le_right

variable (baseField : Type u) [Field baseField]

/-- The structure morphism of the multiplicative parameter space. -/
def overlapToBase : (relativeOverlap (Spec (.of baseField))).toScheme ⟶ (Spec (.of baseField)) :=
  (relativeOverlap (Spec (.of baseField))).ι ≫ (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField))

/-- The scaling parameter, in the coordinate of the indicated chart. -/
def scalingCoordinate (coordinate : ULift.{u} (Fin 2)) : Γ((relativeOverlap (Spec (.of baseField))).toScheme, ⊤) :=
  (((relativeLine (Spec (.of baseField)))).homOfLE
    (relativeOverlap_le_standardOpen (Spec (.of baseField)) coordinate)).appTop
      (relativeChartCoordinate (Spec (.of baseField)) coordinate)

lemma scalingCoordinate_mul (first second : ULift.{u} (Fin 2)) (distinct : first ≠ second) :
    scalingCoordinate baseField first * scalingCoordinate baseField second = 1 := by
  apply relativeChartCoordinate_mul first second distinct
    (((relativeLine (Spec (.of baseField)))).homOfLE (relativeOverlap_le_standardOpen (Spec (.of baseField)) first))
    (((relativeLine (Spec (.of baseField)))).homOfLE (relativeOverlap_le_standardOpen (Spec (.of baseField)) second))
  simp only [Scheme.homOfLE_ι]

/-- The zero section `[0:1]`. -/
def zeroPoint : (Spec (.of baseField)) ⟶ (relativeLine (Spec (.of baseField))) :=
  normalized (𝟙 (Spec (.of baseField))) ⟨1⟩ 0

/-- The zero section as a point of the relative projective line over its field. -/
def zeroPointOver : 𝟙_ (Over (Spec (.of baseField))) ⟶ relativeLineOver baseField :=
  Over.homMk (zeroPoint baseField) (by simp [zeroPoint])

/-- The point `[1:1]`, lying in both standard charts. -/
def onePoint : (Spec (.of baseField)) ⟶ (relativeLine (Spec (.of baseField))) :=
  normalized (𝟙 (Spec (.of baseField))) ⟨1⟩ 1

lemma onePoint_eq (coordinate : ULift.{u} (Fin 2)) :
    onePoint baseField = normalized (𝟙 (Spec (.of baseField))) coordinate 1 := by
  unfold onePoint normalized
  congr 1
  funext index
  simp [normalizedSections]

private lemma onePoint_mem_chart (coordinate : ULift.{u} (Fin 2)) (point : (Spec (.of baseField))) :
    onePoint baseField point ∈ standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate := by
  rw [onePoint_eq baseField coordinate]
  change point ∈ normalized (𝟙 (Spec (.of baseField))) coordinate 1 ⁻¹ᵁ
    standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate
  rw [normalized, homOfSections_preimage_standardOpen]
  simp [normalizedSections, Scheme.basicOpen_of_isUnit _ isUnit_one]

/-- The unit parameter of multiplicative scaling. -/
def scalingUnit : (Spec (.of baseField)) ⟶ (relativeOverlap (Spec (.of baseField))).toScheme :=
  IsOpenImmersion.lift (relativeOverlap (Spec (.of baseField))).ι (onePoint baseField) (by
    rintro _ ⟨point, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ⟨onePoint_mem_chart baseField ⟨0⟩ point, onePoint_mem_chart baseField ⟨1⟩ point⟩)

@[reassoc (attr := simp)]
lemma scalingUnit_ι :
    scalingUnit baseField ≫ (relativeOverlap (Spec (.of baseField))).ι = onePoint baseField :=
  IsOpenImmersion.lift_fac ..

@[reassoc (attr := simp)]
lemma scalingUnit_over : scalingUnit baseField ≫ overlapToBase baseField = 𝟙 (Spec (.of baseField)) := by
  rw [overlapToBase, scalingUnit_ι_assoc, onePoint, normalized_over]

lemma scalingUnit_coordinate (coordinate : ULift.{u} (Fin 2)) :
    (scalingUnit baseField).appTop (scalingCoordinate baseField coordinate) = 1 := by
  have chartEquation : scalingUnit baseField ≫ ((relativeLine (Spec (.of baseField)))).homOfLE
      (relativeOverlap_le_standardOpen (Spec (.of baseField)) coordinate) =
      relativeChartPoint (𝟙 (Spec (.of baseField))) coordinate 1 := by
    apply (cancel_mono (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate).ι).mp
    simp [onePoint_eq baseField coordinate]
  rw [scalingCoordinate, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    chartEquation, relativeChartPoint_coordinate]

instance relativeOverlap_nonempty : Nonempty (relativeOverlap (Spec (.of baseField))).toScheme :=
  Nonempty.map (scalingUnit baseField) inferInstance

instance relativeOverlap_isIntegral : IsIntegral (relativeOverlap (Spec (.of baseField))).toScheme :=
  isIntegral_of_isOpenImmersion (relativeOverlap (Spec (.of baseField))).ι

instance relativeOverlap_isLocallyNoetherian : IsLocallyNoetherian (relativeOverlap (Spec (.of baseField))).toScheme := by
  letI : LocallyOfFiniteType (overlapToBase baseField) := by
    dsimp only [overlapToBase]
    infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian (overlapToBase baseField)

instance relativeOverlap_isDominant : IsDominant (relativeOverlap (Spec (.of baseField))).ι :=
  Opens.isDominant_ι ((relativeOverlap (Spec (.of baseField))).2.dense
    ((Scheme.Opens.nonempty_iff _).mp inferInstance))

/-- The product of the relative projective line with its scaling parameter space. -/
def scalingFamily : Scheme.{u} := pullback (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField)

private abbrev scalingFamilyBase : scalingFamily baseField ⟶ (Spec (.of baseField)) :=
  pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField) ≫ (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField))

private abbrev scalingCover : (scalingFamily baseField).OpenCover where
  I₀ := (ULift.{u} (Fin 2))
  X coordinate := pullback (pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField))
    (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate).ι
  f coordinate := pullback.fst (pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField))
    (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate).ι
  mem₀ := ((relativeChartCover (Spec (.of baseField))).pullback₁
    (pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField))).mem₀

private def localScaling (coordinate : ULift.{u} (Fin 2)) :
    (scalingCover baseField).X coordinate ⟶ (relativeLine (Spec (.of baseField))) :=
  normalized ((scalingCover baseField).f coordinate ≫ scalingFamilyBase baseField) coordinate
    ((((scalingCover baseField).f coordinate ≫
        pullback.snd (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField)).appTop
          (scalingCoordinate baseField coordinate)) *
      ((pullback.snd (pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField))
        (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate).ι).appTop
          (relativeChartCoordinate (Spec (.of baseField)) coordinate)))

private lemma localScaling_compatible (first second : ULift.{u} (Fin 2)) :
    pullback.fst ((scalingCover baseField).f first) ((scalingCover baseField).f second) ≫
      localScaling baseField first = pullback.snd _ _ ≫ localScaling baseField second := by
  by_cases distinct : first = second
  · subst second
    have projections : pullback.fst ((scalingCover baseField).f first)
        ((scalingCover baseField).f first) =
        pullback.snd ((scalingCover baseField).f first) ((scalingCover baseField).f first) := by
      apply (cancel_mono ((scalingCover baseField).f first)).mp
      exact pullback.condition
    rw [projections]
  let firstMap := pullback.fst ((scalingCover baseField).f first) ((scalingCover baseField).f second)
  let secondMap := pullback.snd ((scalingCover baseField).f first) ((scalingCover baseField).f second)
  have samePoint : firstMap ≫ (scalingCover baseField).f first =
      secondMap ≫ (scalingCover baseField).f second := pullback.condition
  have sameParameter : firstMap ≫ (scalingCover baseField).f first ≫
      pullback.snd (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField) =
      secondMap ≫ (scalingCover baseField).f second ≫
        pullback.snd (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField) := by
    simpa only [Category.assoc] using congrArg
      (fun morphism ↦ morphism ≫ pullback.snd (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField)) samePoint
  have sameBase : firstMap ≫ (scalingCover baseField).f first ≫ scalingFamilyBase baseField =
      secondMap ≫ (scalingCover baseField).f second ≫ scalingFamilyBase baseField := by
    simpa only [Category.assoc] using congrArg
      (fun morphism ↦ morphism ≫ scalingFamilyBase baseField) samePoint
  have chartProjection (coordinate : ULift.{u} (Fin 2)) :
      pullback.snd (pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField))
        (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate).ι ≫
          (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate).ι =
      (scalingCover baseField).f coordinate ≫ pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField) :=
    pullback.condition.symm
  have coordinatesReciprocal := relativeChartCoordinate_mul first second distinct
    (firstMap ≫ pullback.snd (pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField))
      (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) first).ι)
    (secondMap ≫ pullback.snd (pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField))
      (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) second).ι) (by
        simp only [Category.assoc, chartProjection]
        simpa only [Category.assoc] using congrArg
          (fun morphism ↦ morphism ≫ pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField)) samePoint)
  dsimp only [localScaling]
  rw [comp_normalized, comp_normalized]
  simp only [map_mul, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Category.assoc]
  rw [sameBase]
  apply normalized_eq_of_mul_eq_one _ first second distinct
  dsimp only [firstMap, secondMap] at coordinatesReciprocal sameParameter
  rw [mul_mul_mul_comm, coordinatesReciprocal, mul_one, ← sameParameter, ← map_mul,
    scalingCoordinate_mul baseField first second distinct, map_one]

/-- Multiplicative scaling, glued from the two standard affine charts. -/
def scaling : scalingFamily baseField ⟶ (relativeLine (Spec (.of baseField))) :=
  (scalingCover baseField).glueMorphisms (localScaling baseField) (localScaling_compatible baseField)

@[reassoc]
private lemma scaling_local (coordinate : ULift.{u} (Fin 2)) :
    (scalingCover baseField).f coordinate ≫ scaling baseField = localScaling baseField coordinate :=
  (scalingCover baseField).ι_glueMorphisms _ _ coordinate

@[reassoc (attr := simp)]
lemma scaling_over : scaling baseField ≫ (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) =
    pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField) ≫ (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) := by
  apply (scalingCover baseField).hom_ext
  intro coordinate
  rw [← Category.assoc, scaling_local, localScaling, normalized_over]

private lemma comp_scaling_on_chart {source : Scheme.{u}}
    (morphism : source ⟶ scalingFamily baseField) (coordinate : ULift.{u} (Fin 2))
    (chartMap : source ⟶ (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate).toScheme)
    (chartEquation : chartMap ≫ (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate).ι =
      morphism ≫ pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField)) :
    morphism ≫ scaling baseField = normalized (morphism ≫ scalingFamilyBase baseField) coordinate
      (((morphism ≫ pullback.snd (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField)).appTop
          (scalingCoordinate baseField coordinate)) *
        chartMap.appTop (relativeChartCoordinate (Spec (.of baseField)) coordinate)) := by
  let liftMap : source ⟶ (scalingCover baseField).X coordinate :=
    pullback.lift morphism chartMap chartEquation.symm
  have lift_projection : liftMap ≫ (scalingCover baseField).f coordinate = morphism :=
    pullback.lift_fst ..
  have lift_chart : liftMap ≫ pullback.snd (pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField))
      (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate).ι = chartMap := pullback.lift_snd ..
  calc
    morphism ≫ scaling baseField =
        liftMap ≫ (scalingCover baseField).f coordinate ≫ scaling baseField := by
      rw [← Category.assoc, lift_projection]
    _ = liftMap ≫ localScaling baseField coordinate := by rw [scaling_local]
    _ = _ := by
      rw [localScaling, comp_normalized]
      simp only [map_mul, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        ← Category.assoc, lift_projection, lift_chart]

/-- Scaling by the unit parameter is the identity. -/
lemma scaling_at_unit :
    pullback.lift (𝟙 (relativeLine (Spec (.of baseField)))) ((relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) ≫ scalingUnit baseField)
      (by simp only [Category.id_comp, Category.assoc, scalingUnit_over, Category.comp_id]) ≫
        scaling baseField = 𝟙 (relativeLine (Spec (.of baseField))) := by
  let unitFamily : (relativeLine (Spec (.of baseField))) ⟶ scalingFamily baseField :=
    pullback.lift (𝟙 (relativeLine (Spec (.of baseField)))) ((relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) ≫ scalingUnit baseField)
      (by simp only [Category.id_comp, Category.assoc, scalingUnit_over, Category.comp_id])
  have first_projection : unitFamily ≫ pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField) =
      𝟙 (relativeLine (Spec (.of baseField))) := pullback.lift_fst ..
  have second_projection : unitFamily ≫ pullback.snd (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField) =
      (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) ≫ scalingUnit baseField := pullback.lift_snd ..
  have base_projection : unitFamily ≫ scalingFamilyBase baseField = (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) := by
    change unitFamily ≫ pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField) ≫ (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) = _
    rw [← Category.assoc, first_projection, Category.id_comp]
  change unitFamily ≫ scaling baseField = 𝟙 (relativeLine (Spec (.of baseField)))
  apply (relativeChartCover (Spec (.of baseField))).hom_ext
  intro coordinate
  have parameter_one : ((standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate).ι ≫ unitFamily ≫
      pullback.snd (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField)).appTop
        (scalingCoordinate baseField coordinate) = 1 := by
    rw [second_projection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, scalingUnit_coordinate, map_one, map_one]
  have chartFormula := comp_scaling_on_chart baseField
    ((standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate).ι ≫ unitFamily) coordinate (𝟙 _)
    (by simp only [Category.id_comp, Category.assoc, first_projection, Category.comp_id])
  have identityCoordinate :
      Scheme.Hom.appTop (𝟙 (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate).toScheme)
        (relativeChartCoordinate (Spec (.of baseField)) coordinate) =
          relativeChartCoordinate (Spec (.of baseField)) coordinate := rfl
  change (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate).ι ≫ (unitFamily ≫ scaling baseField) =
    (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate).ι ≫ 𝟙 (relativeLine (Spec (.of baseField)))
  calc
    _ = normalized ((standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) coordinate).ι ≫ (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField))) coordinate
        (relativeChartCoordinate (Spec (.of baseField)) coordinate) := by
      simpa only [Category.assoc, base_projection, parameter_one, identityCoordinate, one_mul]
        using chartFormula
    _ = _ := by
      simpa only [Category.comp_id] using
        (relativeChart_ι_eq_normalized (Spec (.of baseField)) coordinate).symm

/-- The family pairing a constant affine point with the scaling parameter. -/
def scalingPointFamily (sectionValue : Γ((Spec (.of baseField)), ⊤)) : (relativeOverlap (Spec (.of baseField))).toScheme ⟶ scalingFamily baseField :=
  pullback.lift (f := (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField))) (g := overlapToBase baseField)
    (overlapToBase baseField ≫ normalized (𝟙 (Spec (.of baseField))) (⟨1⟩ : ULift.{u} (Fin 2)) sectionValue)
    (𝟙 (relativeOverlap (Spec (.of baseField))).toScheme) (by rw [Category.assoc, normalized_over, Category.comp_id, Category.id_comp])

@[reassoc]
private lemma scalingPointFamily_fst (sectionValue : Γ((Spec (.of baseField)), ⊤)) :
    scalingPointFamily baseField sectionValue ≫ pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField) =
      overlapToBase baseField ≫ normalized (𝟙 (Spec (.of baseField))) (⟨1⟩ : ULift.{u} (Fin 2)) sectionValue :=
  pullback.lift_fst ..

@[reassoc]
private lemma scalingPointFamily_snd (sectionValue : Γ((Spec (.of baseField)), ⊤)) :
    scalingPointFamily baseField sectionValue ≫ pullback.snd (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField) =
      𝟙 (relativeOverlap (Spec (.of baseField))).toScheme := pullback.lift_snd ..

private lemma scalingPointFamily_base (sectionValue : Γ((Spec (.of baseField)), ⊤)) :
    scalingPointFamily baseField sectionValue ≫ scalingFamilyBase baseField = overlapToBase baseField := by
  change scalingPointFamily baseField sectionValue ≫
    pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField) ≫ (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) = _
  rw [scalingPointFamily_fst_assoc, normalized_over, Category.comp_id]

private def basePointChart (sectionValue : Γ((Spec (.of baseField)), ⊤)) :
    (Spec (.of baseField)) ⟶
      (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) (⟨1⟩ : ULift.{u} (Fin 2))).toScheme :=
  relativeChartPoint (𝟙 (Spec (.of baseField))) (⟨1⟩ : ULift.{u} (Fin 2)) sectionValue

private lemma basePointChart_ι (sectionValue : Γ((Spec (.of baseField)), ⊤)) :
    basePointChart baseField sectionValue ≫
        (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField))
          (⟨1⟩ : ULift.{u} (Fin 2))).ι =
      normalized (𝟙 (Spec (.of baseField))) (⟨1⟩ : ULift.{u} (Fin 2)) sectionValue :=
  relativeChartPoint_ι _ _ _

private lemma basePointChart_coordinate (sectionValue : Γ((Spec (.of baseField)), ⊤)) :
    (basePointChart baseField sectionValue).appTop
        (relativeChartCoordinate (Spec (.of baseField)) (⟨1⟩ : ULift.{u} (Fin 2))) = sectionValue :=
  relativeChartPoint_coordinate _ _ _

private def pointChart (sectionValue : Γ((Spec (.of baseField)), ⊤)) :
    (relativeOverlap (Spec (.of baseField))).toScheme ⟶
      (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField)) (⟨1⟩ : ULift.{u} (Fin 2))).toScheme :=
  overlapToBase baseField ≫ basePointChart baseField sectionValue

private lemma pointChart_ι (sectionValue : Γ((Spec (.of baseField)), ⊤)) :
    pointChart baseField sectionValue ≫
        (standardOpen (ULift.{u} (Fin 2)) (Spec (.of baseField))
          (⟨1⟩ : ULift.{u} (Fin 2))).ι =
      scalingPointFamily baseField sectionValue ≫
        pullback.fst (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField))
          (overlapToBase baseField) := by
  unfold pointChart
  rw [Category.assoc, basePointChart_ι, scalingPointFamily_fst]

private lemma pointChart_coordinate (sectionValue : Γ((Spec (.of baseField)), ⊤)) :
    (pointChart baseField sectionValue).appTop
        (relativeChartCoordinate (Spec (.of baseField)) (⟨1⟩ : ULift.{u} (Fin 2))) =
      (overlapToBase baseField).appTop sectionValue := by
  unfold pointChart
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, basePointChart_coordinate]

private lemma scaling_pointFamily (sectionValue : Γ((Spec (.of baseField)), ⊤)) :
    scalingPointFamily baseField sectionValue ≫ scaling baseField =
      normalized (overlapToBase baseField) (⟨1⟩ : ULift.{u} (Fin 2))
        (scalingCoordinate baseField (⟨1⟩ : ULift.{u} (Fin 2)) * (overlapToBase baseField).appTop sectionValue) := by
  have formula := comp_scaling_on_chart baseField (scalingPointFamily baseField sectionValue)
    (⟨1⟩ : ULift.{u} (Fin 2)) (pointChart baseField sectionValue)
      (pointChart_ι baseField sectionValue)
  have parameterEquation :
      (scalingPointFamily baseField sectionValue ≫
        pullback.snd (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField)) (overlapToBase baseField)).appTop
          (scalingCoordinate baseField (⟨1⟩ : ULift.{u} (Fin 2))) =
            scalingCoordinate baseField (⟨1⟩ : ULift.{u} (Fin 2)) :=
    congrArg (fun morphism : (relativeOverlap (Spec (.of baseField))).toScheme ⟶ (relativeOverlap (Spec (.of baseField))).toScheme ↦
      morphism.appTop (scalingCoordinate baseField (⟨1⟩ : ULift.{u} (Fin 2))))
        (scalingPointFamily_snd baseField sectionValue)
  exact formula.trans (congrArg₂
    (fun (structureMap : (relativeOverlap (Spec (.of baseField))).toScheme ⟶ (Spec (.of baseField))) (value : Γ((relativeOverlap (Spec (.of baseField))).toScheme, ⊤)) ↦
      normalized structureMap (⟨1⟩ : ULift.{u} (Fin 2)) value)
    (scalingPointFamily_base baseField sectionValue)
    (congrArg₂ (fun first second : Γ((relativeOverlap (Spec (.of baseField))).toScheme, ⊤) ↦ first * second)
      parameterEquation (pointChart_coordinate baseField sectionValue)))

/-- Every parameter fixes zero. -/
lemma scaling_fixes_zero : scalingPointFamily baseField 0 ≫ scaling baseField =
    overlapToBase baseField ≫ zeroPoint baseField := by
  have zeroFormula : overlapToBase baseField ≫ zeroPoint baseField =
      normalized (overlapToBase baseField) (⟨1⟩ : ULift.{u} (Fin 2)) 0 := by
    rw [zeroPoint, comp_normalized, Category.comp_id, map_zero]
  rw [scaling_pointFamily, map_zero, mul_zero, zeroFormula]

/-- The orbit of `[1:1]` is the dense open chart intersection. -/
lemma scaling_at_one : scalingPointFamily baseField 1 ≫ scaling baseField =
    (relativeOverlap (Spec (.of baseField))).ι := by
  have inclusion := congrArg
    (fun morphism ↦ ((relativeLine (Spec (.of baseField)))).homOfLE
      (relativeOverlap_le_standardOpen (Spec (.of baseField)) (⟨1⟩ : ULift.{u} (Fin 2))) ≫ morphism)
        (relativeChart_ι_eq_normalized (Spec (.of baseField)) (⟨1⟩ : ULift.{u} (Fin 2)))
  rw [Scheme.homOfLE_ι, comp_normalized, Scheme.homOfLE_ι_assoc] at inclusion
  rw [scaling_pointFamily, map_one, mul_one]
  exact inclusion.symm

end AlgebraicGeometry.ProjectiveLine
