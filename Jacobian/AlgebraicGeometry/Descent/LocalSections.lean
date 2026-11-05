import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Properties

/-!
# Descending morphisms along local sections of reduced schemes

Morphisms from a reduced scheme to a separated scheme are determined by genuine
field-valued morphisms, including their residue-field maps. Consequently, a
morphism constant on all such fibres descends uniquely along Zariski local
sections between reduced schemes.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Morphisms from a reduced scheme to a separated scheme agree if their composites
with every field-valued morphism agree. -/
theorem over_hom_eq_of_field_tests {baseScheme : Scheme.{schemeUniverse}}
    {sourceScheme targetScheme : Over baseScheme}
    [IsReduced sourceScheme.left] [IsSeparated targetScheme.hom]
    (firstMap secondMap : sourceScheme ⟶ targetScheme)
    (fieldTests : ∀ (extensionField : Type schemeUniverse) [Field extensionField]
      (baseMap : Spec (.of extensionField) ⟶ baseScheme)
      (point : Over.mk baseMap ⟶ sourceScheme), point ≫ firstMap = point ≫ secondMap) :
    firstMap = secondMap := by
  apply Over.OverMorphism.ext
  apply ext_of_fromSpecResidueField_eq firstMap.left secondMap.left targetScheme.hom
    Set.univ dense_univ
  · intro sourcePoint membership
    let baseMap := sourceScheme.left.fromSpecResidueField sourcePoint ≫ sourceScheme.hom
    let point : Over.mk baseMap ⟶ sourceScheme :=
      Over.homMk (sourceScheme.left.fromSpecResidueField sourcePoint)
    exact congrArg CommaMorphism.left
      (fieldTests (sourceScheme.left.residueField sourcePoint) baseMap point)
  · exact (Over.w firstMap).trans (Over.w secondMap).symm

/-- A morphism to a separated scheme descends uniquely through Zariski local
sections between reduced schemes if it identifies all field-valued morphisms
with the same image. -/
theorem existsUnique_factorization_of_local_sections_of_field_tests
    {baseScheme : Scheme.{schemeUniverse}}
    {sourceScheme quotientScheme targetScheme : Over baseScheme}
    [IsReduced sourceScheme.left] [IsReduced quotientScheme.left]
    [IsSeparated targetScheme.hom]
    (quotientMap : sourceScheme ⟶ quotientScheme) (sourceMap : sourceScheme ⟶ targetScheme)
    (localSections : ∀ point : quotientScheme.left,
      ∃ openSubset : quotientScheme.left.Opens, point ∈ openSubset ∧
        ∃ sectionMap : Over.mk (openSubset.ι ≫ quotientScheme.hom) ⟶ sourceScheme,
          sectionMap ≫ quotientMap = Over.homMk openSubset.ι)
    (fieldComparison : ∀ (extensionField : Type schemeUniverse) [Field extensionField]
      (baseMap : Spec (.of extensionField) ⟶ baseScheme)
      (firstPoint secondPoint : Over.mk baseMap ⟶ sourceScheme),
      firstPoint ≫ quotientMap = secondPoint ≫ quotientMap →
        firstPoint ≫ sourceMap = secondPoint ≫ sourceMap) :
    ∃! factorMap : quotientScheme ⟶ targetScheme, quotientMap ≫ factorMap = sourceMap := by
  classical
  choose openSubset open_mem sectionMap section_fac using localSections
  let chart (point : quotientScheme.left) : Over baseScheme :=
    Over.mk ((openSubset point).ι ≫ quotientScheme.hom)
  let inclusion (point : quotientScheme.left) : chart point ⟶ quotientScheme :=
    Over.homMk (openSubset point).ι
  let cover : quotientScheme.left.OpenCover := {
    I₀ := quotientScheme.left
    X point := (openSubset point).toScheme
    f point := (openSubset point).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun point ↦ ⟨point, by simpa using open_mem point⟩, inferInstance⟩ }
  let chartMap (point : quotientScheme.left) : cover.X point ⟶ targetScheme.left :=
    (sectionMap point ≫ sourceMap).left
  have compatibility (firstPoint secondPoint : quotientScheme.left) :
      pullback.fst (cover.f firstPoint) (cover.f secondPoint) ≫ chartMap firstPoint =
        pullback.snd (cover.f firstPoint) (cover.f secondPoint) ≫ chartMap secondPoint := by
    let overlap : Over baseScheme := Over.mk
      (pullback.fst (cover.f firstPoint) (cover.f secondPoint) ≫
        (openSubset firstPoint).ι ≫ quotientScheme.hom)
    haveI : IsReduced overlap.left :=
      isReduced_of_isOpenImmersion (pullback.fst (cover.f firstPoint) (cover.f secondPoint))
    let firstProjection : overlap ⟶ chart firstPoint :=
      Over.homMk (pullback.fst (cover.f firstPoint) (cover.f secondPoint))
    let secondProjection : overlap ⟶ chart secondPoint :=
      Over.homMk (pullback.snd (cover.f firstPoint) (cover.f secondPoint)) (by
        change pullback.snd (openSubset firstPoint).ι (openSubset secondPoint).ι ≫
            (openSubset secondPoint).ι ≫ quotientScheme.hom =
          pullback.fst (openSubset firstPoint).ι (openSubset secondPoint).ι ≫
            (openSubset firstPoint).ι ≫ quotientScheme.hom
        exact (pullback.condition_assoc quotientScheme.hom).symm)
    have projection_eq : (firstProjection ≫ sectionMap firstPoint) ≫ quotientMap =
        (secondProjection ≫ sectionMap secondPoint) ≫ quotientMap := by
      rw [Category.assoc, section_fac, Category.assoc, section_fac]
      apply Over.OverMorphism.ext
      exact pullback.condition
    have image_eq : (firstProjection ≫ sectionMap firstPoint) ≫ sourceMap =
        (secondProjection ≫ sectionMap secondPoint) ≫ sourceMap := by
      apply over_hom_eq_of_field_tests
      intro extensionField _ baseMap point
      have point_eq : (point ≫ firstProjection ≫ sectionMap firstPoint) ≫ quotientMap =
          (point ≫ secondProjection ≫ sectionMap secondPoint) ≫ quotientMap := by
        simpa only [Category.assoc] using congrArg (fun morphism ↦ point ≫ morphism) projection_eq
      simpa only [Category.assoc] using fieldComparison extensionField baseMap
        (point ≫ firstProjection ≫ sectionMap firstPoint)
        (point ≫ secondProjection ≫ sectionMap secondPoint) point_eq
    simpa only [firstProjection, secondProjection, chartMap, Over.comp_left, Over.homMk_left,
      Category.assoc] using congrArg CommaMorphism.left image_eq
  let gluedMap := cover.glueMorphisms chartMap compatibility
  have glued_over : gluedMap ≫ targetScheme.hom = quotientScheme.hom := by
    apply cover.hom_ext
    intro point
    rw [← Category.assoc, cover.ι_glueMorphisms chartMap compatibility point]
    exact Over.w (sectionMap point ≫ sourceMap)
  let factorMap : quotientScheme ⟶ targetScheme := Over.homMk gluedMap glued_over
  have factor_chart (point : quotientScheme.left) :
      inclusion point ≫ factorMap = sectionMap point ≫ sourceMap := by
    apply Over.OverMorphism.ext
    exact cover.ι_glueMorphisms chartMap compatibility point
  have factorization : quotientMap ≫ factorMap = sourceMap := by
    apply over_hom_eq_of_field_tests
    intro extensionField _ baseMap point
    let basePoint : quotientScheme.left :=
      (point ≫ quotientMap).left (IsLocalRing.closedPoint extensionField)
    have point_range : Set.range (point ≫ quotientMap).left ⊆
        Set.range (openSubset basePoint).ι := by
      rintro _ ⟨spectrumPoint, rfl⟩
      rw [Scheme.Opens.range_ι]
      have spectrum_eq : spectrumPoint = IsLocalRing.closedPoint extensionField :=
        Subsingleton.elim (α := PrimeSpectrum extensionField) _ _
      rw [spectrum_eq]
      exact open_mem basePoint
    let liftedMap := IsOpenImmersion.lift (openSubset basePoint).ι
      (point ≫ quotientMap).left point_range
    have lifted_fac : liftedMap ≫ (openSubset basePoint).ι = (point ≫ quotientMap).left :=
      IsOpenImmersion.lift_fac (openSubset basePoint).ι (point ≫ quotientMap).left point_range
    let localPoint : Over.mk baseMap ⟶ chart basePoint := Over.homMk liftedMap (by
      change liftedMap ≫ ((openSubset basePoint).ι ≫ quotientScheme.hom) = baseMap
      rw [← Category.assoc, lifted_fac]
      exact Over.w (point ≫ quotientMap))
    have localPoint_comp : localPoint ≫ inclusion basePoint = point ≫ quotientMap := by
      apply Over.OverMorphism.ext
      exact lifted_fac
    have field_image : point ≫ sourceMap = (localPoint ≫ sectionMap basePoint) ≫ sourceMap := by
      apply fieldComparison extensionField baseMap point (localPoint ≫ sectionMap basePoint)
      rw [Category.assoc, section_fac]
      exact localPoint_comp.symm
    calc
      point ≫ (quotientMap ≫ factorMap) = (point ≫ quotientMap) ≫ factorMap :=
        (Category.assoc ..).symm
      _ = (localPoint ≫ inclusion basePoint) ≫ factorMap := by rw [localPoint_comp]
      _ = (localPoint ≫ sectionMap basePoint) ≫ sourceMap := by
        rw [Category.assoc, factor_chart]
        simp only [Category.assoc]
      _ = point ≫ sourceMap := field_image.symm
  refine ⟨factorMap, factorization, ?_⟩
  intro otherFactor other_fac
  apply Over.OverMorphism.ext
  apply cover.hom_ext
  intro point
  have chart_eq : inclusion point ≫ otherFactor = inclusion point ≫ factorMap := by
    calc
      inclusion point ≫ otherFactor = (sectionMap point ≫ quotientMap) ≫ otherFactor := by
        rw [section_fac point]
      _ = sectionMap point ≫ sourceMap := by rw [Category.assoc, other_fac]
      _ = (sectionMap point ≫ quotientMap) ≫ factorMap := by
        rw [Category.assoc, factorization]
      _ = inclusion point ≫ factorMap := by rw [section_fac point]
  exact congrArg CommaMorphism.left chart_eq

end AlgebraicGeometry.Scheme
