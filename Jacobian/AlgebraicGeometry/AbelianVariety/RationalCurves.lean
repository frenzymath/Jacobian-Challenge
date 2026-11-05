import Jacobian.AlgebraicGeometry.AbelianVariety.BaseChange
import Jacobian.AlgebraicGeometry.Group.Rigidity
import Jacobian.AlgebraicGeometry.ProjectiveLine.Scaling
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Rational curves in abelian varieties

Every morphism from the canonical relative projective line over a field to an
abelian variety is constant. Over an algebraic closure this follows from the
scaling family and the rigidity theorem for proper geometrically integral
schemes. Faithful effective-epimorphic field base change then descends the
equality to the original field.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace AlgebraicGeometry.AbelianVariety.RationalCurves

private abbrev base (field : Type u) [Field field] : Scheme.{u} := Spec (.of field)
private abbrev line (field : Type u) [Field field] : Scheme.{u} :=
  ProjectiveLine.relativeLine (base field)
private abbrev lineOver (field : Type u) [Field field] : Over (base field) :=
  ProjectiveLine.relativeLineOver field

private abbrev overlap (field : Type u) [Field field] :
    Scheme.{u} := (ProjectiveLine.relativeOverlap (base field)).toScheme

private abbrev overlapOver (field : Type u) [Field field] : Over (base field) :=
  Over.mk (ProjectiveLine.overlapToBase field)

private abbrev zeroOver (field : Type u) [Field field] := ProjectiveLine.zeroPointOver field

private def oneOver (field : Type u) [Field field] :
    𝟙_ (Over (base field)) ⟶ lineOver field :=
  Over.homMk (ProjectiveLine.onePoint field) (by
    change ProjectiveLine.onePoint field ≫ line field ↘ base field = 𝟙 (base field)
    exact ProjectiveLine.normalized_over ..)

private def unitOver (field : Type u) [Field field] :
    𝟙_ (Over (base field)) ⟶ overlapOver field :=
  Over.homMk (ProjectiveLine.scalingUnit field)
    (ProjectiveLine.scalingUnit_over field)

private def torusInclusion (field : Type u) [Field field] :
    overlapOver field ⟶ lineOver field :=
  Over.homMk (ProjectiveLine.relativeOverlap (base field)).ι rfl

private def scalingOver (field : Type u) [Field field] :
    lineOver field ⊗ overlapOver field ⟶ lineOver field :=
  Over.homMk (ProjectiveLine.scaling field)
    (ProjectiveLine.scaling_over field)

private lemma scalingOver_at_unit (field : Type u) [Field field] :
    lift (𝟙 (lineOver field)) (toUnit (lineOver field) ≫ unitOver field) ≫
        scalingOver field = 𝟙 (lineOver field) := by
  apply Over.OverMorphism.ext
  exact ProjectiveLine.scaling_at_unit field

private lemma scalingOver_fixes_zero (field : Type u) [Field field] :
    lift (toUnit (overlapOver field) ≫ zeroOver field) (𝟙 (overlapOver field)) ≫
        scalingOver field = toUnit (overlapOver field) ≫ zeroOver field := by
  apply Over.OverMorphism.ext
  change ProjectiveLine.scalingPointFamily field 0 ≫ ProjectiveLine.scaling field =
    ProjectiveLine.overlapToBase field ≫ ProjectiveLine.zeroPoint field
  exact ProjectiveLine.scaling_fixes_zero field

private lemma scalingOver_at_one (field : Type u) [Field field] :
    lift (toUnit (overlapOver field) ≫ oneOver field) (𝟙 (overlapOver field)) ≫
        scalingOver field = torusInclusion field := by
  apply Over.OverMorphism.ext
  change ProjectiveLine.scalingPointFamily field 1 ≫ ProjectiveLine.scaling field =
    (ProjectiveLine.relativeOverlap (base field)).ι
  exact ProjectiveLine.scaling_at_one field

private instance family_integral (field : Type u) [Field field] :
    IsIntegral (lineOver field ⊗ overlapOver field).left := by
  change IsIntegral (pullback (line field ↘ base field) (ProjectiveLine.overlapToBase field))
  infer_instance

private theorem eq_zero_comp_of_isAlgClosed {field : Type u} [Field field] [IsAlgClosed field]
    (group : CommGrp (Over (base field)))
    [IsSeparated group.X.hom] [LocallyOfFiniteType group.X.hom]
    (morphism : lineOver field ⟶ group.X) :
    morphism = toUnit (lineOver field) ≫ zeroOver field ≫ morphism := by
  letI : IsProper (lineOver field).hom := by
    change IsProper (line field ↘ base field)
    exact ProjectiveSpace.instIsProper (ULift.{u} (Fin 2)) (base field)
  letI : GeometricallyIntegral (lineOver field).hom := by
    change GeometricallyIntegral (line field ↘ base field)
    exact ProjectiveLine.relative_geometricallyIntegral field
  letI : LocallyOfFiniteType (overlapOver field).hom := by
    change LocallyOfFiniteType (ProjectiveLine.overlapToBase field)
    dsimp only [ProjectiveLine.overlapToBase]
    infer_instance
  have invariant :
      scalingOver field ≫ morphism = fst (lineOver field) (overlapOver field) ≫ morphism := by
    let defect : lineOver field ⊗ overlapOver field ⟶ group.X :=
      (scalingOver field ≫ morphism) *
        (fst (lineOver field) (overlapOver field) ≫ morphism)⁻¹
    have defect_at_unit :
        lift (𝟙 (lineOver field)) (toUnit (lineOver field) ≫ unitOver field) ≫ defect =
          toUnit (lineOver field) ≫ η[group.X] := by
      simp only [defect, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
        scalingOver_at_unit, lift_fst, Category.id_comp, mul_inv_cancel, Hom.one_def]
    obtain ⟨value, value_eq, _⟩ :=
      exists_unique_eq_snd_comp_of_isProper_of_geometricallyIntegral
        defect (unitOver field) η[group.X] defect_at_unit
    have value_one : value = 1 := by
      have equation := congrArg
        (fun arrow => lift (toUnit (overlapOver field) ≫ zeroOver field)
          (𝟙 (overlapOver field)) ≫ arrow) value_eq
      simp only [defect, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
        scalingOver_fixes_zero, lift_fst, lift_snd, Category.id_comp,
        mul_inv_cancel] at equation
      exact equation.symm
    have defect_one : defect = 1 := by rw [value_eq, value_one, MonObj.comp_one]
    exact mul_inv_eq_one.mp defect_one
  have overlap_equality : torusInclusion field ≫ morphism =
      toUnit (overlapOver field) ≫ oneOver field ≫ morphism := by
    let unitSlice : overlapOver field ⟶ lineOver field ⊗ overlapOver field :=
      lift (toUnit (overlapOver field) ≫ oneOver field) (𝟙 (overlapOver field))
    have unitSlice_scaling : unitSlice ≫ scalingOver field = torusInclusion field := by
      simpa only [unitSlice] using scalingOver_at_one field
    have unitSlice_first : unitSlice ≫ fst (lineOver field) (overlapOver field) =
        toUnit (overlapOver field) ≫ oneOver field := lift_fst ..
    calc
      torusInclusion field ≫ morphism = (unitSlice ≫ scalingOver field) ≫ morphism :=
        congrArg (fun arrow : overlapOver field ⟶ lineOver field => arrow ≫ morphism)
          unitSlice_scaling.symm
      _ = (unitSlice ≫ fst (lineOver field) (overlapOver field)) ≫ morphism := by
        simpa only [Category.assoc] using congrArg
          (fun arrow : lineOver field ⊗ overlapOver field ⟶ group.X => unitSlice ≫ arrow)
            invariant
      _ = toUnit (overlapOver field) ≫ oneOver field ≫ morphism := by
        rw [unitSlice_first, Category.assoc]
  have constant : morphism = toUnit (lineOver field) ≫ oneOver field ≫ morphism := by
    apply Over.OverMorphism.ext
    apply ext_of_isDominant_of_isSeparated group.X.hom (by simp)
      (ProjectiveLine.relativeOverlap (base field)).ι
    exact congrArg Over.Hom.left overlap_equality
  have zero_one : zeroOver field ≫ morphism = oneOver field ≫ morphism := by
    have equation := congrArg (fun arrow : lineOver field ⟶ group.X =>
      zeroOver field ≫ arrow) constant
    simpa only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp] using equation
  rw [zero_one]
  exact constant

private theorem effectiveEpi_relativeLineMap {field extensionField : Type u}
    [Field field] [Field extensionField] [Algebra field extensionField] :
    EffectiveEpi (ProjectiveSpace.map (ULift.{u} (Fin 2))
      (Spec.map (CommRingCat.ofHom (algebraMap field extensionField)))) := by
  let baseMap : base extensionField ⟶ base field :=
    Spec.map (CommRingCat.ofHom (algebraMap field extensionField))
  letI : Surjective baseMap :=
    ⟨fun point => ⟨Classical.arbitrary (base extensionField), Subsingleton.elim _ point⟩⟩
  letI : Flat baseMap := inferInstanceAs
    (Flat (Spec.map (CommRingCat.ofHom (algebraMap field extensionField))))
  letI : QuasiCompact baseMap := inferInstanceAs
    (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap field extensionField))))
  letI : Surjective (ProjectiveSpace.map (ULift.{u} (Fin 2)) baseMap) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) baseMap).flip inferInstance
  letI : Flat (ProjectiveSpace.map (ULift.{u} (Fin 2)) baseMap) :=
    MorphismProperty.of_isPullback (P := @Flat)
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) baseMap).flip inferInstance
  letI : QuasiCompact (ProjectiveSpace.map (ULift.{u} (Fin 2)) baseMap) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) baseMap).flip inferInstance
  infer_instance

/-- The normalized `[0:1]` value is the unique constant of a map from relative P¹. -/
theorem eq_zero_comp {field : Type u} [Field field]
    (variety : AlgebraicGeometry.AbelianVariety field)
    (morphism : ProjectiveLine.relativeLineOver field ⟶ variety.group.X) :
    morphism = toUnit (ProjectiveLine.relativeLineOver field) ≫
      ProjectiveLine.zeroPointOver field ≫ morphism := by
  let extensionField := AlgebraicClosure field
  let baseChangeMap : base extensionField ⟶ base field :=
    Spec.map (CommRingCat.ofHom (algebraMap field extensionField))
  let projectiveMap : line extensionField ⟶ line field :=
    ProjectiveSpace.map (ULift.{u} (Fin 2)) baseChangeMap
  let extendedVariety :=
    (AlgebraicGeometry.AbelianVariety.baseChange field extensionField).obj variety
  let extendedMorphism : lineOver extensionField ⟶ extendedVariety.group.X :=
    Over.homMk
      (pullback.lift (projectiveMap ≫ morphism.left) (line extensionField ↘ base extensionField)
        (by rw [Category.assoc, Over.w morphism]; exact ProjectiveSpace.map_over _ _))
      (pullback.lift_snd ..)
  have extendedEquality := eq_zero_comp_of_isAlgClosed extendedVariety.group extendedMorphism
  have firstProjection : extendedMorphism.left ≫ pullback.fst variety.group.X.hom baseChangeMap =
      projectiveMap ≫ morphism.left := pullback.lift_fst ..
  have projectedEquality := congrArg
    (fun arrow : lineOver extensionField ⟶ extendedVariety.group.X =>
      arrow.left ≫ pullback.fst variety.group.X.hom baseChangeMap) extendedEquality
  have terminalProjection : (toUnit (lineOver extensionField)).left =
      (line extensionField ↘ base extensionField) := Over.toUnit_left
  have zeroProjection : (zeroOver extensionField).left =
      ProjectiveLine.zeroPoint extensionField := rfl
  have projectedEquality' : projectiveMap ≫ morphism.left =
      (line extensionField ↘ base extensionField) ≫
        ProjectiveLine.zeroPoint extensionField ≫ projectiveMap ≫ morphism.left := by
    simpa only [Over.comp_left, terminalProjection, zeroProjection,
      Category.assoc, firstProjection] using projectedEquality
  have zeroPoint_baseChange :
      ProjectiveLine.zeroPoint extensionField ≫ projectiveMap =
        baseChangeMap ≫ ProjectiveLine.zeroPoint field := by
    unfold ProjectiveLine.zeroPoint
    rw [ProjectiveLine.normalized_map, ProjectiveLine.comp_normalized]
    simp only [Category.id_comp, Category.comp_id, map_zero]
  rw [← Category.assoc (ProjectiveLine.zeroPoint extensionField) projectiveMap,
    zeroPoint_baseChange, Category.assoc] at projectedEquality'
  have structureMap : (line extensionField ↘ base extensionField) ≫ baseChangeMap =
      projectiveMap ≫ (line field ↘ base field) := (ProjectiveSpace.map_over _ _).symm
  have equality : projectiveMap ≫ morphism.left =
      projectiveMap ≫ (line field ↘ base field) ≫
        ProjectiveLine.zeroPoint field ≫ morphism.left := by
    simpa only [← Category.assoc, structureMap] using projectedEquality'
  letI : EffectiveEpi projectiveMap := by
    exact effectiveEpi_relativeLineMap
  apply Over.OverMorphism.ext
  apply (cancel_epi projectiveMap).mp
  exact equality

/-- Every map from the canonical relative P¹ to an abelian variety has a unique constant. -/
theorem existsUnique_constant {field : Type u} [Field field]
    (variety : AlgebraicGeometry.AbelianVariety field)
    (morphism : ProjectiveLine.relativeLineOver field ⟶ variety.group.X) :
    ∃! constant : 𝟙_ (Over (Spec (.of field))) ⟶ variety.group.X,
      morphism = toUnit (ProjectiveLine.relativeLineOver field) ≫ constant := by
  refine ⟨ProjectiveLine.zeroPointOver field ≫ morphism, eq_zero_comp variety morphism, ?_⟩
  intro constant equation
  have evaluated := congrArg
    (fun arrow : ProjectiveLine.relativeLineOver field ⟶ variety.group.X =>
      ProjectiveLine.zeroPointOver field ≫ arrow) equation
  simpa only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp] using evaluated.symm

end AlgebraicGeometry.AbelianVariety.RationalCurves
