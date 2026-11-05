import Jacobian.AlgebraicGeometry.Hilbert.SectionPencil.BaseChange
import Jacobian.AlgebraicGeometry.Hilbert.SectionPencil.Core
import Jacobian.AlgebraicGeometry.Modules.FreeGeneratorPullback

/-!
# Field-valued fibres of a pencil

The pullback-composition and monoidal comparisons identify a pencil at a
field-valued parameter with a genuine scalar combination of its two sections.
Injectivity of canonical cohomology base change then proves nonvanishing.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory
open CategoryTheory.Limits (zero_comp comp_zero)
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.SectionPencil

private theorem tensor_sum_eq_zero_iff_conjugate
    {category : Type*} [Category category] [MonoidalCategory category]
    [Preadditive category]
    {firstSource secondSource firstTarget secondTarget : category}
    {newFirstSource newSecondSource newFirstTarget newSecondTarget : category}
    (firstSourceIso : firstSource ≅ newFirstSource)
    (secondSourceIso : secondSource ≅ newSecondSource)
    (firstTargetIso : firstTarget ≅ newFirstTarget)
    (secondTargetIso : secondTarget ≅ newSecondTarget)
    (firstSection secondSection : firstSource ⟶ firstTarget)
    (firstCoefficient secondCoefficient : secondSource ⟶ secondTarget) :
    firstSection ⊗ₘ firstCoefficient + secondSection ⊗ₘ secondCoefficient = 0 ↔
      (firstSourceIso.inv ≫ firstSection ≫ firstTargetIso.hom) ⊗ₘ
          (secondSourceIso.inv ≫ firstCoefficient ≫ secondTargetIso.hom) +
        (firstSourceIso.inv ≫ secondSection ≫ firstTargetIso.hom) ⊗ₘ
          (secondSourceIso.inv ≫ secondCoefficient ≫ secondTargetIso.hom) = 0 := by
  have conjugation :
      (firstSourceIso ⊗ᵢ secondSourceIso).inv ≫
          (firstSection ⊗ₘ firstCoefficient + secondSection ⊗ₘ secondCoefficient) ≫
          (firstTargetIso ⊗ᵢ secondTargetIso).hom =
        (firstSourceIso.inv ≫ firstSection ≫ firstTargetIso.hom) ⊗ₘ
            (secondSourceIso.inv ≫ firstCoefficient ≫ secondTargetIso.hom) +
          (firstSourceIso.inv ≫ secondSection ≫ firstTargetIso.hom) ⊗ₘ
            (secondSourceIso.inv ≫ secondCoefficient ≫ secondTargetIso.hom) := by
    simp only [Preadditive.comp_add, Preadditive.add_comp, tensorIso_inv,
      tensorIso_hom, tensorHom_comp_tensorHom, Category.assoc]
  rw [← conjugation]
  constructor
  · intro vanishing
    simp only [vanishing, zero_comp, comp_zero]
  · intro vanishing
    apply (cancel_epi (firstSourceIso ⊗ᵢ secondSourceIso).inv).mp
    apply (cancel_mono (firstTargetIso ⊗ᵢ secondTargetIso).hom).mp
    simpa only [Category.assoc, comp_zero, zero_comp] using vanishing

variable {source parameter family test fieldScheme : Scheme.{u}}

/-- The vanishing test after pullback uses the actual monoidal comparison. -/
theorem pullback_pencilSection_eq_zero_iff (restriction : test ⟶ family)
    (sourceProjection : family ⟶ source) (parameterProjection : family ⟶ parameter)
    {sourceLine : source.Modules} {parameterLine : parameter.Modules}
    (firstSection secondSection : unit source ⟶ sourceLine)
    (firstCoefficient secondCoefficient : unit parameter ⟶ parameterLine) :
    (pullback restriction).map (pencilSection sourceProjection parameterProjection
        firstSection secondSection firstCoefficient secondCoefficient) = 0 ↔
      (pullback restriction).map ((pullback sourceProjection).map firstSection) ⊗ₘ
          (pullback restriction).map ((pullback parameterProjection).map firstCoefficient) +
        (pullback restriction).map ((pullback sourceProjection).map secondSection) ⊗ₘ
          (pullback restriction).map ((pullback parameterProjection).map secondCoefficient) = 0 := by
  rw [← pulledSourceIso_inv_comp]
  constructor
  · intro vanishing
    simp only [vanishing, comp_zero, zero_comp]
  · intro vanishing
    apply (cancel_epi (pulledSourceIso restriction sourceProjection parameterProjection).inv).mp
    apply (cancel_mono (Functor.Monoidal.μIso (pullback restriction)
      ((pullback sourceProjection).obj sourceLine)
      ((pullback parameterProjection).obj parameterLine)).inv).mp
    simpa only [Category.assoc, comp_zero, zero_comp] using vanishing

/-- Naturality of the composition comparison, with a specified composite. -/
@[reassoc]
theorem pullbackCompOfEq_naturality (restriction : test ⟶ family)
    (projection : family ⟶ source) (composite : test ⟶ source)
    (equation : restriction ≫ projection = composite)
    {firstModule secondModule : source.Modules} (moduleMap : firstModule ⟶ secondModule) :
    (pullback restriction).map ((pullback projection).map moduleMap) ≫
        (pullbackCompOfEq restriction projection composite equation secondModule).hom =
      (pullbackCompOfEq restriction projection composite equation firstModule).hom ≫
        (pullback composite).map moduleMap :=
  ((pullbackComp restriction projection ≪≫ pullbackCongr equation).hom.naturality moduleMap)

/-- Comparing a pulled map with pullback along its composite. -/
theorem pullbackCompOfEq_conjugate (restriction : test ⟶ family)
    (projection : family ⟶ source) (composite : test ⟶ source)
    (equation : restriction ≫ projection = composite)
    {firstModule secondModule : source.Modules} (moduleMap : firstModule ⟶ secondModule) :
    (pullbackCompOfEq restriction projection composite equation firstModule).inv ≫
        (pullback restriction).map ((pullback projection).map moduleMap) ≫
        (pullbackCompOfEq restriction projection composite equation secondModule).hom =
      (pullback composite).map moduleMap := by
  rw [pullbackCompOfEq_naturality]
  simp only [Iso.inv_hom_id_assoc]

/-- Compare the two factorizations of the parameter projection. -/
def parameterPullbackIso (restriction : test ⟶ family)
    (projection : family ⟶ parameter) (fieldProjection : test ⟶ fieldScheme)
    (parameterPoint : fieldScheme ⟶ parameter)
    (equation : restriction ≫ projection = fieldProjection ≫ parameterPoint)
    (moduleSheaf : parameter.Modules) :
    (pullback restriction).obj ((pullback projection).obj moduleSheaf) ≅
      (pullback fieldProjection).obj ((pullback parameterPoint).obj moduleSheaf) :=
  pullbackCompOfEq restriction projection (fieldProjection ≫ parameterPoint)
    equation moduleSheaf ≪≫ ((pullbackComp fieldProjection parameterPoint).app moduleSheaf).symm

@[reassoc]
theorem parameterPullbackIso_naturality (restriction : test ⟶ family)
    (projection : family ⟶ parameter) (fieldProjection : test ⟶ fieldScheme)
    (parameterPoint : fieldScheme ⟶ parameter)
    (equation : restriction ≫ projection = fieldProjection ≫ parameterPoint)
    {firstModule secondModule : parameter.Modules} (moduleMap : firstModule ⟶ secondModule) :
    (pullback restriction).map ((pullback projection).map moduleMap) ≫
        (parameterPullbackIso restriction projection fieldProjection parameterPoint
          equation secondModule).hom =
      (parameterPullbackIso restriction projection fieldProjection parameterPoint
        equation firstModule).hom ≫
          (pullback fieldProjection).map ((pullback parameterPoint).map moduleMap) :=
  ((pullbackComp restriction projection ≪≫ pullbackCongr equation ≪≫
    (pullbackComp fieldProjection parameterPoint).symm).hom.naturality moduleMap)

/-- The structure-sheaf endomorphism obtained by trivializing a parameter line. -/
def parameterCoefficient {parameterLine : parameter.Modules}
    (parameterPoint : fieldScheme ⟶ parameter)
    (trivialization : (pullback parameterPoint).obj parameterLine ≅ unit fieldScheme)
    (coefficient : unit parameter ⟶ parameterLine) : unit fieldScheme ⟶ unit fieldScheme :=
  (pullbackObjUnitIso parameterPoint).inv ≫
    (pullback parameterPoint).map coefficient ≫ trivialization.hom

/-- A trivialization of the parameter line turns vanishing into a scalar tensor test. -/
theorem pullback_pencilSection_eq_zero_iff_parameter
    (restriction : test ⟶ family) (sourceProjection : family ⟶ source)
    (parameterProjection : family ⟶ parameter) (sourceMap : test ⟶ source)
    (fieldProjection : test ⟶ fieldScheme) (parameterPoint : fieldScheme ⟶ parameter)
    (sourceEquation : restriction ≫ sourceProjection = sourceMap)
    (parameterEquation : restriction ≫ parameterProjection = fieldProjection ≫ parameterPoint)
    {sourceLine : source.Modules} {parameterLine : parameter.Modules}
    (trivialization : (pullback parameterPoint).obj parameterLine ≅ unit fieldScheme)
    (firstSection secondSection : unit source ⟶ sourceLine)
    (firstCoefficient secondCoefficient : unit parameter ⟶ parameterLine) :
    (pullback restriction).map (pencilSection sourceProjection parameterProjection
        firstSection secondSection firstCoefficient secondCoefficient) = 0 ↔
      (pullback sourceMap).map firstSection ⊗ₘ
          (pullback fieldProjection).map
            (parameterCoefficient parameterPoint trivialization firstCoefficient) +
        (pullback sourceMap).map secondSection ⊗ₘ
          (pullback fieldProjection).map
            (parameterCoefficient parameterPoint trivialization secondCoefficient) = 0 := by
  rw [pullback_pencilSection_eq_zero_iff]
  let sourceUnitIso := pullbackCompOfEq restriction sourceProjection sourceMap
    sourceEquation (unit source)
  let sourceLineIso := pullbackCompOfEq restriction sourceProjection sourceMap
    sourceEquation sourceLine
  let parameterUnitIso := parameterPullbackIso restriction parameterProjection
    fieldProjection parameterPoint parameterEquation (unit parameter) ≪≫
      (pullback fieldProjection).mapIso (pullbackObjUnitIso parameterPoint)
  let parameterLineIso := parameterPullbackIso restriction parameterProjection
    fieldProjection parameterPoint parameterEquation parameterLine ≪≫
      (pullback fieldProjection).mapIso trivialization
  rw [tensor_sum_eq_zero_iff_conjugate sourceUnitIso parameterUnitIso
    sourceLineIso parameterLineIso]
  have sourceComparison (sectionMap : unit source ⟶ sourceLine) :
      sourceUnitIso.inv ≫ (pullback restriction).map
          ((pullback sourceProjection).map sectionMap) ≫ sourceLineIso.hom =
        (pullback sourceMap).map sectionMap :=
    pullbackCompOfEq_conjugate restriction sourceProjection sourceMap sourceEquation sectionMap
  have parameterComparison (coefficient : unit parameter ⟶ parameterLine) :
      parameterUnitIso.inv ≫ (pullback restriction).map
          ((pullback parameterProjection).map coefficient) ≫ parameterLineIso.hom =
        (pullback fieldProjection).map
          (parameterCoefficient parameterPoint trivialization coefficient) := by
    let unitComparison := parameterPullbackIso restriction parameterProjection
      fieldProjection parameterPoint parameterEquation (unit parameter)
    let lineComparison := parameterPullbackIso restriction parameterProjection
      fieldProjection parameterPoint parameterEquation parameterLine
    have naturality := parameterPullbackIso_naturality restriction parameterProjection
      fieldProjection parameterPoint parameterEquation coefficient
    have conjugation : unitComparison.inv ≫ (pullback restriction).map
        ((pullback parameterProjection).map coefficient) ≫ lineComparison.hom =
          (pullback fieldProjection).map ((pullback parameterPoint).map coefficient) :=
      (congrArg (fun moduleMap ↦ unitComparison.inv ≫ moduleMap) naturality).trans
        (Iso.inv_hom_id_assoc unitComparison
          ((pullback fieldProjection).map ((pullback parameterPoint).map coefficient)))
    have comparison := congrArg
      (fun moduleMap : (pullback fieldProjection).obj ((pullback parameterPoint).obj
          (unit parameter)) ⟶ (pullback fieldProjection).obj
            ((pullback parameterPoint).obj parameterLine) ↦
        (pullback fieldProjection).map (pullbackObjUnitIso parameterPoint).inv ≫
          moduleMap ≫ (pullback fieldProjection).map trivialization.hom) conjugation
    simpa only [unitComparison, lineComparison, parameterUnitIso, parameterLineIso,
      Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
      parameterCoefficient, Functor.map_comp, Category.assoc] using comparison
  rw [sourceComparison, sourceComparison, parameterComparison, parameterComparison]

/-- Evaluation on the two pulled unit generators computes the scalar combination. -/
theorem tensor_sum_eq_zero_implies_sections
    (sourceMap : test ⟶ source) (fieldProjection : test ⟶ fieldScheme)
    {sourceLine : source.Modules} (firstSection secondSection : unit source ⟶ sourceLine)
    (firstCoefficient secondCoefficient : unit fieldScheme ⟶ unit fieldScheme)
    (vanishing : (pullback sourceMap).map firstSection ⊗ₘ
        (pullback fieldProjection).map firstCoefficient +
      (pullback sourceMap).map secondSection ⊗ₘ
        (pullback fieldProjection).map secondCoefficient = 0) :
    fieldProjection.appTop (firstCoefficient.app ⊤ (1 : Γ(fieldScheme, ⊤))) •
        pullbackΓ sourceMap sourceLine (firstSection.app ⊤ (1 : Γ(source, ⊤))) +
      fieldProjection.appTop (secondCoefficient.app ⊤ (1 : Γ(fieldScheme, ⊤))) •
        pullbackΓ sourceMap sourceLine (secondSection.app ⊤ (1 : Γ(source, ⊤))) = 0 := by
  let generator := tmulSection (pullbackΓ sourceMap (unit source) (1 : Γ(source, ⊤)))
    (pullbackΓ fieldProjection (unit fieldScheme) (1 : Γ(fieldScheme, ⊤)))
  let contraction : (pullback sourceMap).obj sourceLine ⊗
      (pullback fieldProjection).obj (unit fieldScheme) ⟶ (pullback sourceMap).obj sourceLine :=
    ((pullback sourceMap).obj sourceLine ◁ (pullbackObjUnitIso fieldProjection).hom) ≫
      (ρ_ _).hom
  have evaluated := congrArg
    (fun moduleMap ↦ (contraction.app ⊤) (moduleMap.app ⊤ generator)) vanishing
  have unitGenerator : pullbackΓ fieldProjection (unit fieldScheme) (1 : Γ(fieldScheme, ⊤)) =
      (pullbackObjUnitIso fieldProjection).inv.app ⊤ (1 : Γ(test, ⊤)) := by
    rw [pullbackΓ_apply]
    exact pullbackSection_one_eq fieldProjection
  have term (sectionMap : unit source ⟶ sourceLine)
      (coefficient : unit fieldScheme ⟶ unit fieldScheme) :
      contraction.app ⊤ (((pullback sourceMap).map sectionMap ⊗ₘ
          (pullback fieldProjection).map coefficient).app ⊤ generator) =
        fieldProjection.appTop (coefficient.app ⊤ (1 : Γ(fieldScheme, ⊤))) •
          pullbackΓ sourceMap sourceLine (sectionMap.app ⊤ (1 : Γ(source, ⊤))) := by
    have scalar : (pullbackObjUnitIso fieldProjection).hom.app ⊤
        (((pullback fieldProjection).map coefficient).app ⊤
          (pullbackΓ fieldProjection (unit fieldScheme) (1 : Γ(fieldScheme, ⊤)))) =
        fieldProjection.appTop (coefficient.app ⊤ (1 : Γ(fieldScheme, ⊤))) := by
      rw [unitGenerator]
      simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using
        Scheme.Modules.pullbackObjUnitIso_conj_app_top fieldProjection coefficient
    dsimp only [contraction, generator]
    rw [tensorHom_app_tmulSection, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      whiskerLeft_app_tmulSection, pullbackΓ_naturality, scalar]
    change (ρ_ ((pullback sourceMap).obj sourceLine)).hom.app ⊤
      (tmulSection (pullbackΓ sourceMap sourceLine (sectionMap.app ⊤ (1 : Γ(source, ⊤))))
        (unitSectionsEquiv ⊤
          (fieldProjection.appTop (coefficient.app ⊤ (1 : Γ(fieldScheme, ⊤)))))) = _
    exact rightUnitor_hom_app_tmulSection _ _
  have evaluation_add : contraction.app ⊤
      (((pullback sourceMap).map firstSection ⊗ₘ (pullback fieldProjection).map firstCoefficient +
        (pullback sourceMap).map secondSection ⊗ₘ
          (pullback fieldProjection).map secondCoefficient).app ⊤ generator) =
      contraction.app ⊤ (((pullback sourceMap).map firstSection ⊗ₘ
        (pullback fieldProjection).map firstCoefficient).app ⊤ generator) +
      contraction.app ⊤ (((pullback sourceMap).map secondSection ⊗ₘ
        (pullback fieldProjection).map secondCoefficient).app ⊤ generator) := by
    change contraction.app ⊤ (_ + _) = _
    exact map_add _ _ _
  rw [evaluation_add, term, term] at evaluated
  change _ = contraction.app ⊤ (0 : Γ((pullback sourceMap).obj sourceLine ⊗
    (pullback fieldProjection).obj (unit fieldScheme), ⊤)) at evaluated
  exact evaluated.trans (contraction.app ⊤).hom.map_zero

/-- Every field-valued parameter gives a nonzero pencil if its sections are independent. -/
theorem pullback_pencilSection_ne_zero_of_field_coefficients
    {baseField extensionField : Type u} [Field baseField] [Field extensionField]
    [Algebra baseField extensionField] {source parameter family : Scheme.{u}}
    [source.Over (Spec (.of baseField))]
    [QuasiCompact (source ↘ Spec (.of baseField))]
    [QuasiSeparated (source ↘ Spec (.of baseField))]
    (sourceProjection : family ⟶ source) (parameterProjection : family ⟶ parameter)
    (parameterPoint : Spec (.of extensionField) ⟶ parameter)
    (restriction : Limits.pullback (source ↘ Spec (.of baseField))
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) ⟶ family)
    (sourceEquation : restriction ≫ sourceProjection = Limits.pullback.fst _ _)
    (parameterEquation : restriction ≫ parameterProjection =
      Limits.pullback.snd _ _ ≫ parameterPoint)
    (sourceLine : source.Modules) [sourceLine.IsQuasicoherent]
    (firstClass secondClass : sourceLine.H 0)
    (independent : LinearIndependent baseField ![firstClass, secondClass])
    {parameterLine : parameter.Modules}
    (firstCoefficient secondCoefficient : unit parameter ⟶ parameterLine)
    (trivialization : (pullback parameterPoint).obj parameterLine ≅ unit (Spec (.of extensionField)))
    (nonzero : (parameterCoefficient parameterPoint trivialization firstCoefficient).app ⊤
          (1 : Γ(Spec (.of extensionField), ⊤)) ≠ 0 ∨
        (parameterCoefficient parameterPoint trivialization secondCoefficient).app ⊤
          (1 : Γ(Spec (.of extensionField), ⊤)) ≠ 0) :
    (pullback restriction).map (pencilSection sourceProjection parameterProjection
      (homOfGlobalSection sourceLine (H.zeroLinearEquiv sourceLine firstClass))
      (homOfGlobalSection sourceLine (H.zeroLinearEquiv sourceLine secondClass))
      firstCoefficient secondCoefficient) ≠ 0 := by
  let sourceMap := Limits.pullback.fst (source ↘ Spec (.of baseField))
    (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))
  let fieldProjection := Limits.pullback.snd (source ↘ Spec (.of baseField))
    (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))
  let firstValue := parameterCoefficient parameterPoint trivialization firstCoefficient
  let secondValue := parameterCoefficient parameterPoint trivialization secondCoefficient
  let firstScalar := (Scheme.ΓSpecIso (.of extensionField)).hom
    (firstValue.app ⊤ (1 : Γ(Spec (.of extensionField), ⊤)))
  let secondScalar := (Scheme.ΓSpecIso (.of extensionField)).hom
    (secondValue.app ⊤ (1 : Γ(Spec (.of extensionField), ⊤)))
  have nonzeroScalar : firstScalar ≠ 0 ∨ secondScalar ≠ 0 := by
    rcases nonzero with firstNonzero | secondNonzero
    · exact Or.inl fun equality ↦ firstNonzero
        ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of extensionField)).hom).injective
          (equality.trans (map_zero _).symm))
    · exact Or.inr fun equality ↦ secondNonzero
        ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of extensionField)).hom).injective
          (equality.trans (map_zero _).symm))
  intro vanishing
  have tensorVanishing := (pullback_pencilSection_eq_zero_iff_parameter restriction
    sourceProjection parameterProjection sourceMap fieldProjection parameterPoint
    sourceEquation parameterEquation trivialization _ _
    firstCoefficient secondCoefficient).mp vanishing
  have sectionVanishing := tensor_sum_eq_zero_implies_sections sourceMap fieldProjection
    _ _ firstValue secondValue tensorVanishing
  have nonzeroSection := pulled_pencil_ne_zero sourceLine firstClass secondClass independent
    firstScalar secondScalar nonzeroScalar
  have scalarEquation (scalar : Γ(Spec (.of extensionField), ⊤)) :
      globalSectionsRingHom extensionField
          (X := Limits.pullback (source ↘ Spec (.of baseField))
            (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))
          ((Scheme.ΓSpecIso (.of extensionField)).hom scalar) =
        fieldProjection.appTop scalar := by
    change fieldProjection.appTop ((Scheme.ΓSpecIso (.of extensionField)).inv
      ((Scheme.ΓSpecIso (.of extensionField)).hom scalar)) = _
    rw [Iso.hom_inv_id_apply]
  let sectionModule := ((pullback sourceMap).obj sourceLine).val.obj (.op ⊤)
  letI : Module Γ(Limits.pullback (source ↘ Spec (.of baseField))
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))), ⊤)
      sectionModule := sectionModule.isModule
  let firstRingScalar := fieldProjection.appTop
    (firstValue.app ⊤ (1 : Γ(Spec (.of extensionField), ⊤)))
  let secondRingScalar := fieldProjection.appTop
    (secondValue.app ⊤ (1 : Γ(Spec (.of extensionField), ⊤)))
  let firstPulledSection : sectionModule :=
    (pullbackUnit sourceMap sourceLine).app ⊤
      (H.zeroLinearEquiv sourceLine firstClass)
  let secondPulledSection : sectionModule :=
    (pullbackUnit sourceMap sourceLine).app ⊤
      (H.zeroLinearEquiv sourceLine secondClass)
  apply nonzeroSection
  simp only [firstValue, secondValue, firstScalar, secondScalar,
    scalarEquation, pullbackΓ_apply, homOfGlobalSection_app_one,
    Scheme.Hom.preimage_top, Scheme.Modules.presheaf_map_id_apply,
    sourceMap, fieldProjection, pullbackSection, pullbackUnitApp] at sectionVanishing ⊢
  change firstRingScalar • firstPulledSection +
    secondRingScalar • secondPulledSection = (0 : sectionModule) at sectionVanishing
  change firstRingScalar • firstPulledSection +
    secondRingScalar • secondPulledSection = (0 : sectionModule)
  exact sectionVanishing

end AlgebraicGeometry.SectionPencil
