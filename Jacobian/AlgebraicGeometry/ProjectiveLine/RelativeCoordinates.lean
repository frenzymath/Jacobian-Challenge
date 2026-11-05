import Jacobian.AlgebraicGeometry.ProjectiveSpace.Charts
import Jacobian.AlgebraicGeometry.ProjectiveSpace.SectionsNaturality
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Normalized coordinates on the relative projective line

The two standard charts of relative projective space have reciprocal affine
coordinates on their intersection. The chart construction also shows that the
relative projective line over a field is geometrically integral.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.ProjectiveLine

/-- The canonical two-coordinate relative projective line over a scheme. -/
abbrev relativeLine (base : Scheme.{u}) : Scheme.{u} := ℙ(ULift.{u} (Fin 2); base)

local notation "Line(" base ")" => relativeLine base

/-- The canonical relative projective line as an object over a field spectrum. -/
abbrev relativeLineOver (baseField : Type u) [Field baseField] :
    Over (Spec (.of baseField)) :=
  Over.mk (relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField))

attribute [local instance] Classical.decEq

/-- The other homogeneous coordinate of the projective line. -/
def otherCoordinate (coordinate : ULift.{u} (Fin 2)) : ULift.{u} (Fin 2) := ⟨coordinate.down.rev⟩

@[simp]
lemma otherCoordinate_ne (coordinate : ULift.{u} (Fin 2)) : otherCoordinate coordinate ≠ coordinate := by
  rcases coordinate with ⟨coordinate⟩
  fin_cases coordinate <;> decide

lemma otherCoordinate_eq {first second : ULift.{u} (Fin 2)} (distinct : first ≠ second) :
    otherCoordinate first = second := by
  rcases first with ⟨first⟩
  rcases second with ⟨second⟩
  fin_cases first <;> fin_cases second <;> simp_all [otherCoordinate]

lemma eq_or_eq_of_ne {first second : ULift.{u} (Fin 2)} (distinct : first ≠ second)
    (coordinate : ULift.{u} (Fin 2)) : coordinate = first ∨ coordinate = second := by
  rcases first with ⟨first⟩
  rcases second with ⟨second⟩
  rcases coordinate with ⟨coordinate⟩
  fin_cases first <;> fin_cases second <;> fin_cases coordinate <;> simp_all

/-- Homogeneous coordinates normalized to one in the indicated chart. -/
def normalizedSections {source : Scheme.{u}} (coordinate : ULift.{u} (Fin 2))
    (sectionValue : Γ(source, ⊤)) : ULift.{u} (Fin 2) → Γ(source, ⊤) :=
  fun index ↦ if index = coordinate then 1 else sectionValue

lemma normalizedSections_span {source : Scheme.{u}} (coordinate : ULift.{u} (Fin 2))
    (sectionValue : Γ(source, ⊤)) :
    Ideal.span (Set.range (normalizedSections coordinate sectionValue)) = ⊤ := by
  exact (Ideal.eq_top_iff_one _).mpr
    (Ideal.subset_span ⟨coordinate, by simp [normalizedSections]⟩)

/-- The relative projective point with one coordinate equal to one. -/
def normalized {source base : Scheme.{u}} (structureMap : source ⟶ base)
    (coordinate : ULift.{u} (Fin 2)) (sectionValue : Γ(source, ⊤)) : source ⟶ Line(base) :=
  homOfSections structureMap (normalizedSections coordinate sectionValue)
    (normalizedSections_span coordinate sectionValue)

@[reassoc (attr := simp)]
lemma normalized_over {source base : Scheme.{u}} (structureMap : source ⟶ base)
    (coordinate : ULift.{u} (Fin 2)) (sectionValue : Γ(source, ⊤)) :
    normalized structureMap coordinate sectionValue ≫ Line(base) ↘ base = structureMap :=
  homOfSections_over ..

@[reassoc]
lemma comp_normalized {source target base : Scheme.{u}} (morphism : target ⟶ source)
    (structureMap : source ⟶ base) (coordinate : ULift.{u} (Fin 2)) (sectionValue : Γ(source, ⊤)) :
    morphism ≫ normalized structureMap coordinate sectionValue =
      normalized (morphism ≫ structureMap) coordinate (morphism.appTop sectionValue) := by
  rw [normalized, comp_homOfSections]
  congr 1
  funext index
  simp only [normalizedSections]
  split_ifs <;> simp only [map_one]

/-- Changing the base preserves a normalized homogeneous tuple. -/
@[reassoc]
lemma normalized_map {source firstBase secondBase : Scheme.{u}}
    (structureMap : source ⟶ firstBase) (baseMap : firstBase ⟶ secondBase)
    (coordinate : ULift.{u} (Fin 2)) (sectionValue : Γ(source, ⊤)) :
    normalized structureMap coordinate sectionValue ≫ ProjectiveSpace.map (ULift.{u} (Fin 2)) baseMap =
      normalized (structureMap ≫ baseMap) coordinate sectionValue := by
  apply ProjectiveSpace.hom_ext (ULift.{u} (Fin 2)) secondBase
  · simp only [Category.assoc, ProjectiveSpace.map_over, normalized_over,
      normalized_over_assoc]
  · simp only [Category.assoc, ProjectiveSpace.map_toIntegralModel, normalized,
      ProjectiveSpace.homOfSections_toIntegralModel]

/-- Normalized homogeneous coordinates agree with the standard affine chart. -/
lemma normalized_eq_chart {source base : Scheme.{u}} (structureMap : source ⟶ base)
    (coordinate : ULift.{u} (Fin 2)) (sectionValue : Γ(source, ⊤)) :
    normalized structureMap coordinate sectionValue =
      AffineSpace.homOfVector structureMap
        (fun _ : {index : ULift.{u} (Fin 2) // index ≠ coordinate} ↦ sectionValue) ≫
          (standardOpenIso (ULift.{u} (Fin 2)) base coordinate).inv ≫
            (standardOpen (ULift.{u} (Fin 2)) base coordinate).ι := by
  let sections := normalizedSections coordinate sectionValue
  let sourceOpen := source.basicOpen (sections coordinate)
  have coordinate_one : sections coordinate = 1 := by simp [sections, normalizedSections]
  have sourceOpen_top : sourceOpen = ⊤ := by
    dsimp [sourceOpen]
    rw [coordinate_one]
    exact Scheme.basicOpen_of_isUnit _ isUnit_one
  letI : IsIso sourceOpen.ι := by
    rw [sourceOpen_top]
    exact source.topIso.isIso_hom
  have division (index : {index : ULift.{u} (Fin 2) // index ≠ coordinate}) :
      source.divBasicOpen (sections index.1) (sections coordinate) =
        sourceOpen.ι.appTop sectionValue := by
    have equation := Scheme.divBasicOpen_mul_self source (sections index.1) (sections coordinate)
    have index_value : sections index.1 = sectionValue := by
      simp [sections, normalizedSections, index.2]
    simpa only [coordinate_one, index_value, map_one, mul_one] using equation
  apply (cancel_epi sourceOpen.ι).mp
  calc
    sourceOpen.ι ≫ normalized structureMap coordinate sectionValue =
        (homOfSections structureMap sections
          (normalizedSections_span coordinate sectionValue)).resLE
            (standardOpen (ULift.{u} (Fin 2)) base coordinate) sourceOpen
            (homOfSections_preimage_standardOpen structureMap sections
              (normalizedSections_span coordinate sectionValue) coordinate).ge ≫
                (standardOpen (ULift.{u} (Fin 2)) base coordinate).ι :=
      (Scheme.Hom.resLE_comp_ι _ _).symm
    _ = AffineSpace.homOfVector (sourceOpen.ι ≫ structureMap)
        (fun _ ↦ sourceOpen.ι.appTop sectionValue) ≫
          (standardOpenIso (ULift.{u} (Fin 2)) base coordinate).inv ≫
            (standardOpen (ULift.{u} (Fin 2)) base coordinate).ι := by
      have chartEquation := homOfSections_resLE_standardOpenIso_hom structureMap sections
        (normalizedSections_span coordinate sectionValue) coordinate
      have comparison := congrArg
        (fun morphism ↦ morphism ≫ (standardOpenIso (ULift.{u} (Fin 2)) base coordinate).inv ≫
          (standardOpen (ULift.{u} (Fin 2)) base coordinate).ι) chartEquation
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, division] using comparison
    _ = sourceOpen.ι ≫ (AffineSpace.homOfVector structureMap
        (fun _ : {index : ULift.{u} (Fin 2) // index ≠ coordinate} ↦ sectionValue) ≫
          (standardOpenIso (ULift.{u} (Fin 2)) base coordinate).inv ≫
            (standardOpen (ULift.{u} (Fin 2)) base coordinate).ι) := by
      have naturality := AffineSpace.comp_homOfVector
        (fun _ : {index : ULift.{u} (Fin 2) // index ≠ coordinate} ↦ sectionValue)
        sourceOpen.ι structureMap
      simpa only [Function.comp_def, Category.assoc] using
        (congrArg (fun morphism ↦ morphism ≫ (standardOpenIso (ULift.{u} (Fin 2)) base coordinate).inv ≫
          (standardOpen (ULift.{u} (Fin 2)) base coordinate).ι) naturality).symm

/-- The affine coordinate on a standard chart of the relative projective line. -/
def relativeChartCoordinate (base : Scheme.{u}) (coordinate : ULift.{u} (Fin 2)) :
    Γ((standardOpen (ULift.{u} (Fin 2)) base coordinate).toScheme, ⊤) :=
  (standardOpenIso (ULift.{u} (Fin 2)) base coordinate).hom.appTop
    (AffineSpace.coord base ⟨otherCoordinate coordinate, otherCoordinate_ne coordinate⟩)

/-- A point in a standard affine chart with prescribed coordinate. -/
def relativeChartPoint {source base : Scheme.{u}} (structureMap : source ⟶ base)
    (coordinate : ULift.{u} (Fin 2)) (sectionValue : Γ(source, ⊤)) :
    source ⟶ (standardOpen (ULift.{u} (Fin 2)) base coordinate).toScheme :=
  AffineSpace.homOfVector structureMap
    (fun _ : {index : ULift.{u} (Fin 2) // index ≠ coordinate} ↦ sectionValue) ≫
      (standardOpenIso (ULift.{u} (Fin 2)) base coordinate).inv

@[reassoc (attr := simp)]
lemma relativeChartPoint_ι {source base : Scheme.{u}} (structureMap : source ⟶ base)
    (coordinate : ULift.{u} (Fin 2)) (sectionValue : Γ(source, ⊤)) :
    relativeChartPoint structureMap coordinate sectionValue ≫
      (standardOpen (ULift.{u} (Fin 2)) base coordinate).ι =
        normalized structureMap coordinate sectionValue := by
  exact (normalized_eq_chart structureMap coordinate sectionValue).symm

lemma relativeChartPoint_coordinate {source base : Scheme.{u}}
    (structureMap : source ⟶ base) (coordinate : ULift.{u} (Fin 2)) (sectionValue : Γ(source, ⊤)) :
    (relativeChartPoint structureMap coordinate sectionValue).appTop
      (relativeChartCoordinate base coordinate) = sectionValue := by
  rw [relativeChartCoordinate, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  simp [relativeChartPoint, AffineSpace.homOfVector_appTop_coord]

/-- The standard chart inclusion is given by its affine coordinate. -/
lemma relativeChart_ι_eq_normalized (base : Scheme.{u}) (coordinate : ULift.{u} (Fin 2)) :
    (standardOpen (ULift.{u} (Fin 2)) base coordinate).ι =
      normalized ((standardOpen (ULift.{u} (Fin 2)) base coordinate).ι ≫ Line(base) ↘ base)
        coordinate (relativeChartCoordinate base coordinate) := by
  rw [normalized_eq_chart]
  have chartEquation : AffineSpace.homOfVector
      ((standardOpen (ULift.{u} (Fin 2)) base coordinate).ι ≫ Line(base) ↘ base)
      (fun _ : {index : ULift.{u} (Fin 2) // index ≠ coordinate} ↦
        relativeChartCoordinate base coordinate) =
      (standardOpenIso (ULift.{u} (Fin 2)) base coordinate).hom := by
    refine AffineSpace.hom_ext ?_ fun index ↦ ?_
    · simp only [AffineSpace.homOfVector_over, standardOpenIso_hom_over]
    · rw [AffineSpace.homOfVector_appTop_coord, relativeChartCoordinate]
      exact congrArg
        (fun index ↦ (standardOpenIso (ULift.{u} (Fin 2)) base coordinate).hom.appTop
          (AffineSpace.coord base index))
        (Subtype.ext (otherCoordinate_eq index.2.symm))
  rw [chartEquation, Iso.hom_inv_id_assoc]

/-- Reciprocal affine coordinates determine the same projective point. -/
lemma normalized_eq_of_mul_eq_one {source base : Scheme.{u}} (structureMap : source ⟶ base)
    (first second : ULift.{u} (Fin 2)) (distinct : first ≠ second)
    (firstValue secondValue : Γ(source, ⊤)) (reciprocal : firstValue * secondValue = 1) :
    normalized structureMap first firstValue = normalized structureMap second secondValue := by
  let unitValue : Γ(source, ⊤)ˣ :=
    ⟨secondValue, firstValue, (mul_comm _ _).trans reciprocal, reciprocal⟩
  apply homOfSections_eq_of_unit_mul structureMap unitValue
    (normalizedSections_span first firstValue) (normalizedSections_span second secondValue)
  intro index
  rcases eq_or_eq_of_ne distinct index with rfl | rfl
  · simp [normalizedSections, distinct, distinct.symm, unitValue]
  · simp [normalizedSections, distinct, distinct.symm, unitValue, mul_comm secondValue firstValue,
      reciprocal]

lemma normalized_injective {source base : Scheme.{u}} (structureMap : source ⟶ base)
    (coordinate : ULift.{u} (Fin 2)) : Function.Injective (normalized structureMap coordinate) := by
  intro firstValue secondValue equation
  have chartEquation : relativeChartPoint structureMap coordinate firstValue =
      relativeChartPoint structureMap coordinate secondValue := by
    apply (cancel_mono (standardOpen (ULift.{u} (Fin 2)) base coordinate).ι).mp
    simpa only [relativeChartPoint_ι] using equation
  have evaluation := congrArg
    (fun morphism ↦ morphism.appTop (relativeChartCoordinate base coordinate)) chartEquation
  simpa only [relativeChartPoint_coordinate] using evaluation

/-- Affine coordinates on the two charts are reciprocal wherever both are defined. -/
lemma relativeChartCoordinate_mul {source base : Scheme.{u}}
    (first second : ULift.{u} (Fin 2)) (distinct : first ≠ second)
    (firstMap : source ⟶ (standardOpen (ULift.{u} (Fin 2)) base first).toScheme)
    (secondMap : source ⟶ (standardOpen (ULift.{u} (Fin 2)) base second).toScheme)
    (samePoint : firstMap ≫ (standardOpen (ULift.{u} (Fin 2)) base first).ι =
      secondMap ≫ (standardOpen (ULift.{u} (Fin 2)) base second).ι) :
    firstMap.appTop (relativeChartCoordinate base first) *
      secondMap.appTop (relativeChartCoordinate base second) = 1 := by
  let structureMap := firstMap ≫ (standardOpen (ULift.{u} (Fin 2)) base first).ι ≫ Line(base) ↘ base
  let firstValue := firstMap.appTop (relativeChartCoordinate base first)
  let secondValue := secondMap.appTop (relativeChartCoordinate base second)
  have first_normalized : firstMap ≫ (standardOpen (ULift.{u} (Fin 2)) base first).ι =
      normalized structureMap first firstValue := by
    rw [relativeChart_ι_eq_normalized base first, comp_normalized]
  have second_normalized : secondMap ≫ (standardOpen (ULift.{u} (Fin 2)) base second).ι =
      normalized structureMap second secondValue := by
    rw [relativeChart_ι_eq_normalized base second, comp_normalized]
    congr 1
    exact congrArg (fun morphism ↦ morphism ≫ Line(base) ↘ base) samePoint.symm
  have fullPreimage :
      (normalized structureMap first firstValue) ⁻¹ᵁ standardOpen (ULift.{u} (Fin 2)) base second = ⊤ := by
    rw [← first_normalized, samePoint]
    ext point
    change (secondMap point).val ∈ standardOpen (ULift.{u} (Fin 2)) base second ↔ True
    exact iff_true_intro (secondMap point).property
  have basicOpen_top : source.basicOpen firstValue = ⊤ := by
    simpa only [normalized, homOfSections_preimage_standardOpen, normalizedSections,
      if_neg distinct.symm] using fullPreimage
  have first_unit : IsUnit firstValue := by
    have restriction_unit : IsUnit (source.presheaf.map
        (homOfLE (show source.basicOpen firstValue ≤ ⊤ from le_top)).op firstValue) :=
      source.toRingedSpace.isUnit_res_basicOpen firstValue
    rw [basicOpen_top] at restriction_unit
    simpa only [homOfLE_refl, CategoryTheory.op_id, CategoryTheory.Functor.map_id,
      ConcreteCategory.id_apply] using restriction_unit
  obtain ⟨unitValue, unit_eq⟩ := first_unit
  have reciprocal : firstValue * (↑unitValue⁻¹ : Γ(source, ⊤)) = 1 := by
    rw [← unit_eq]
    exact unitValue.mul_inv
  have second_eq : (↑unitValue⁻¹ : Γ(source, ⊤)) = secondValue :=
    normalized_injective structureMap second
      ((normalized_eq_of_mul_eq_one structureMap first second distinct _ _ reciprocal).symm.trans
        (first_normalized.symm.trans (samePoint.trans second_normalized)))
  change firstValue * secondValue = 1
  exact (congrArg (fun value : Γ(source, ⊤) ↦ firstValue * value) second_eq).symm.trans reciprocal

/-- The two standard affine charts cover the relative projective line. -/
def relativeChartCover (base : Scheme.{u}) : Line(base).OpenCover :=
  (Line(base)).openCoverOfIsOpenCover (standardOpen (ULift.{u} (Fin 2)) base)
    (iSup_standardOpen (ULift.{u} (Fin 2)) base)

variable (baseField : Type u) [Field baseField]

/-- The relative projective line over a field is integral. -/
instance relative_isIntegral : IsIntegral Line(Spec (.of baseField)) := by
  let base := Spec (.of baseField)
  have chart_integral (coordinate : ULift.{u} (Fin 2)) :
      IsIntegral (standardOpen (ULift.{u} (Fin 2)) base coordinate).toScheme :=
    IsIntegral.of_isIso (standardOpenIso (ULift.{u} (Fin 2)) base coordinate).inv
  letI (coordinate : ULift.{u} (Fin 2)) : IsIntegral ((relativeChartCover base).X coordinate) :=
    chart_integral coordinate
  letI : IsReduced Line(base) := IsReduced.of_openCover _ (relativeChartCover base)
  let commonPoint := normalized (𝟙 base) (⟨0⟩ : ULift.{u} (Fin 2)) (1 : Γ(base, ⊤))
    (IsLocalRing.closedPoint baseField)
  have common_mem (coordinate : ULift.{u} (Fin 2)) : commonPoint ∈ standardOpen (ULift.{u} (Fin 2)) base coordinate := by
    change IsLocalRing.closedPoint baseField ∈
      normalized (𝟙 base) (⟨0⟩ : ULift.{u} (Fin 2)) (1 : Γ(base, ⊤)) ⁻¹ᵁ
        standardOpen (ULift.{u} (Fin 2)) base coordinate
    rw [normalized, homOfSections_preimage_standardOpen]
    simp [normalizedSections, Scheme.basicOpen_of_isUnit _ isUnit_one]
  have irreducible_chart (coordinate : ULift.{u} (Fin 2)) :
      IsIrreducible (standardOpen (ULift.{u} (Fin 2)) base coordinate : Set Line(base)) := by
    letI := chart_integral coordinate
    simpa only [Set.image_univ, Scheme.Opens.range_ι] using
      (IrreducibleSpace.isIrreducible_univ
        (standardOpen (ULift.{u} (Fin 2)) base coordinate).toScheme).image
          (standardOpen (ULift.{u} (Fin 2)) base coordinate).ι
          (standardOpen (ULift.{u} (Fin 2)) base coordinate).ι.continuous.continuousOn
  have union_top : (standardOpen (ULift.{u} (Fin 2)) base (⟨0⟩ : ULift.{u} (Fin 2)) : Set Line(base)) ∪
      standardOpen (ULift.{u} (Fin 2)) base (⟨1⟩ : ULift.{u} (Fin 2)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro point
    have membership : point ∈ (⊤ : Line(base).Opens) := trivial
    rw [← iSup_standardOpen (ULift.{u} (Fin 2)) base, Opens.mem_iSup] at membership
    obtain ⟨⟨coordinate⟩, membership⟩ := membership
    fin_cases coordinate
    · exact Or.inl membership
    · exact Or.inr membership
  have dense_first : closure (standardOpen (ULift.{u} (Fin 2)) base (⟨0⟩ : ULift.{u} (Fin 2)) : Set Line(base)) =
      Set.univ := by
    apply Set.eq_univ_of_forall
    intro point
    have membership : point ∈
        (standardOpen (ULift.{u} (Fin 2)) base (⟨0⟩ : ULift.{u} (Fin 2)) : Set Line(base)) ∪
          standardOpen (ULift.{u} (Fin 2)) base (⟨1⟩ : ULift.{u} (Fin 2)) := by
      rw [union_top]
      trivial
    rcases membership with first_mem | second_mem
    · exact subset_closure first_mem
    · have included := subset_closure_inter_of_isPreirreducible_of_isOpen
        (irreducible_chart ⟨1⟩).2 (standardOpen (ULift.{u} (Fin 2)) base (⟨0⟩ : ULift.{u} (Fin 2))).isOpen
        ⟨commonPoint, common_mem ⟨1⟩, common_mem ⟨0⟩⟩
      exact (closure_mono Set.inter_subset_right) (included second_mem)
  letI : IrreducibleSpace Line(base) := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set Line(base))
    rw [← dense_first]
    exact (irreducible_chart ⟨0⟩).closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Relative projective line commutes with field extension and is geometrically integral. -/
instance relative_geometricallyIntegral :
    GeometricallyIntegral (Line(Spec (.of baseField)) ↘ Spec (.of baseField)) := by
  refine ⟨fun extensionField _ point fiber first second square ↦ ?_⟩
  let comparison : fiber ≅ Line(Spec (.of extensionField)) :=
    square.isoIsPullback _ _ (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) point)
  exact IsIntegral.of_isIso comparison.inv

end AlgebraicGeometry.ProjectiveLine
