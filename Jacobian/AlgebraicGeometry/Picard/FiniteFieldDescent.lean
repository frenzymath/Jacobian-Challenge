import Jacobian.AlgebraicGeometry.Limits.FieldExtension
import Jacobian.AlgebraicGeometry.Picard.AbelianVariety
import Jacobian.AlgebraicGeometry.Picard.DegreeFieldExtension
import Jacobian.AlgebraicGeometry.Picard.Fpqc

/-!
# Finite separable fields of definition for the degree-zero Picard scheme

A degree-zero Picard representative over a separable closure descends to a
finite intermediate field together with its canonical transport of points.
The transport is trivial at a finite level because it is trivial on the
diagonal, which is the inverse limit of the tensor diagonals. Fpqc descent of
the degree-zero sheaf then identifies the descended scheme as a representative.

The final comparison identifies classifying maps over the separable closure
with those over the finite field of definition. No descended representative or
transport-invariance hypothesis is required as input.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits Opposite IntermediateField TensorProduct

namespace AlgebraicGeometry

open Scheme

private lemma presheaf_map_map_eq_of_comp_eq
    {CategoryType : Type*} [Category CategoryType] (presheaf : CategoryTypeᵒᵖ ⥤ Type*)
    {source firstMiddle secondMiddle target : CategoryType}
    (firstMap : source ⟶ firstMiddle) (secondMap : firstMiddle ⟶ target)
    (thirdMap : source ⟶ secondMiddle) (fourthMap : secondMiddle ⟶ target)
    (equality : firstMap ≫ secondMap = thirdMap ≫ fourthMap)
    (sectionValue : presheaf.obj (.op target)) :
    presheaf.map firstMap.op (presheaf.map secondMap.op sectionValue) =
      presheaf.map thirdMap.op (presheaf.map fourthMap.op sectionValue) := by
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, equality]

private lemma specMap_algebraMap_comp (baseField stageField extensionField : Type schemeUniverse)
    [Field baseField] [Field stageField] [Field extensionField]
    [Algebra baseField stageField] [Algebra baseField extensionField]
    [Algebra stageField extensionField] [IsScalarTower baseField stageField extensionField] :
    Spec.map (CommRingCat.ofHom (algebraMap stageField extensionField)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap baseField stageField)) =
      Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)) := by
  rw [← Spec.map_comp]
  congr 1
  ext element
  exact (IsScalarTower.algebraMap_apply baseField stageField extensionField element).symm

private theorem exists_finiteStage_equal_pullback_maps
    {Index : Type schemeUniverse} [Category.{schemeUniverse} Index]
    {diagram : Index ⥤ Scheme.{schemeUniverse}} {cone : Cone diagram}
    (limit : IsLimit cone) [IsCofiltered Index]
    [∀ {firstIndex secondIndex : Index} (transition : firstIndex ⟶ secondIndex),
      IsAffineHom (diagram.map transition)]
    [∀ index, CompactSpace (diagram.obj index)]
    [∀ index, QuasiSeparatedSpace (diagram.obj index)]
    {stageIndex : Index} {source target : Scheme.{schemeUniverse}}
    (sourceMap : source ⟶ diagram.obj stageIndex) (targetMap : target ⟶ diagram.obj stageIndex)
    [LocallyOfFinitePresentation sourceMap] [QuasiCompact sourceMap] [QuasiSeparated sourceMap]
    [LocallyOfFinitePresentation targetMap] [QuasiCompact targetMap] [QuasiSeparated targetMap]
    (firstMap secondMap : source ⟶ target)
    (firstOver : firstMap ≫ targetMap = sourceMap)
    (secondOver : secondMap ≫ targetMap = sourceMap)
    (equality : pullback.fst sourceMap (cone.π.app stageIndex) ≫ firstMap =
      pullback.fst sourceMap (cone.π.app stageIndex) ≫ secondMap) :
    ∃ (laterIndex : Index) (transition : laterIndex ⟶ stageIndex),
      pullback.fst sourceMap (diagram.map transition) ≫ firstMap =
        pullback.fst sourceMap (diagram.map transition) ≫ secondMap := by
  letI : CompactSpace source := QuasiCompact.compactSpace_of_compactSpace sourceMap
  letI : QuasiSeparatedSpace source := quasiSeparatedSpace_of_quasiSeparated sourceMap
  obtain ⟨laterIndex, transition, eventualEquality⟩ :=
    Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (baseChangeDiagram diagram sourceMap) (baseChangeDiagramStructure diagram sourceMap)
      targetMap (baseChangeCone diagram cone sourceMap)
      (isLimitBaseChangeCone diagram cone sourceMap limit) (i := Over.mk (𝟙 stageIndex))
      (pullback.fst _ _ ≫ firstMap) (pullback.fst _ _ ≫ secondMap)
      (by simp [baseChangeDiagramStructure, firstOver])
      (by simp [baseChangeDiagramStructure, secondOver])
      (by rw [baseChangeCone_π_app_fst_assoc, baseChangeCone_π_app_fst_assoc, equality])
  exact ⟨laterIndex.left, laterIndex.hom, by simpa using eventualEquality⟩

variable {baseField : Type schemeUniverse} [Field baseField]

private lemma picardDegree_inclusion {curve : Scheme.{schemeUniverse}}
    (family : curve ⟶ Spec (.of baseField)) (degree : ℤ)
    [QuasiCompact family] [QuasiSeparated family]
    {parameter : Over (Spec (.of baseField))}
    (sectionValue : (picardFunctorDegree family degree).obj.obj (.op parameter))
    (point : parameter.left) :
    picardDegree family ((picardFunctorDegreeι family degree).hom.app _ sectionValue) point =
      degree := by
  let topology := fppfTopology.over (Spec (.of baseField))
  obtain ⟨localParameter, restriction, ⟨lineClass, compatibility⟩, _, _, localPoint, rfl⟩ :=
    exists_flat_mem_of_mem_fppfTopology_over
      (Presheaf.imageSieve_mem topology
        (toSheafify topology (picardSubfunctorDegree family degree).toFunctor) sectionValue) point
  rw [← picardDegree_map, ← NatTrans.naturality_apply (picardFunctorDegreeι family degree).hom,
    show (picardFunctorDegree family degree).obj.map restriction.op sectionValue =
      (toSheafify topology (picardSubfunctorDegree family degree).toFunctor).app _ lineClass
        from compatibility.symm,
    picardFunctorDegreeι_app_toSheafify, picardDegree_toPicardFunctor]
  exact (mem_picardSubfunctorDegree_iff family lineClass.1 degree).1 lineClass.2 localPoint

private lemma exists_picardDegree_lift {curve : Scheme.{schemeUniverse}}
    (family : curve ⟶ Spec (.of baseField)) (degree : ℤ)
    [QuasiCompact family] [QuasiSeparated family]
    {parameter : Over (Spec (.of baseField))}
    (sectionValue : (picardFunctor family).obj.obj (.op parameter))
    (constantDegree : ∀ point, picardDegree family sectionValue point = degree) :
    ∃ lift, (picardFunctorDegreeι family degree).hom.app _ lift = sectionValue := by
  let topology := fppfTopology.over (Spec (.of baseField))
  let inclusion := (picardFunctorDegreeι family degree).hom
  let imageSieve := Presheaf.imageSieve inclusion sectionValue
  have covering : imageSieve ∈ topology parameter := by
    refine topology.superset_covering (fun localParameter restriction membership ↦ ?_)
      (Presheaf.imageSieve_mem topology (toPicardFunctor family) sectionValue)
    obtain ⟨lineClass, compatibility⟩ := membership
    have degreeMembership : lineClass ∈
        (picardSubfunctorDegree family degree).obj (.op localParameter) :=
      (mem_picardSubfunctorDegree_iff family lineClass degree).2 fun point ↦ by
        rw [← picardDegree_eq family sectionValue restriction lineClass compatibility point,
          constantDegree]
    exact ⟨(toSheafify topology (picardSubfunctorDegree family degree).toFunctor).app _
      ⟨lineClass, degreeMembership⟩, by
        rw [picardFunctorDegreeι_app_toSheafify]
        exact compatibility⟩
  let localValues : Presieve.FamilyOfElements (picardFunctorDegree family degree).obj
      imageSieve.arrows := fun _ _ membership ↦ membership.choose
  have localValues_inclusion {localParameter : Over (Spec (.of baseField))}
      (restriction : localParameter ⟶ parameter) (membership : imageSieve restriction) :
      inclusion.app _ (localValues restriction membership) =
        (picardFunctor family).obj.map restriction.op sectionValue := membership.choose_spec
  have compatible : localValues.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro firstParameter secondParameter firstRestriction secondRestriction firstMembership
    apply injective_picardFunctorDegreeι_app family degree
    change inclusion.app _ _ = inclusion.app _ _
    rw [NatTrans.naturality_apply, localValues_inclusion, localValues_inclusion, op_comp,
      Functor.map_comp_apply]
  have degreeSheaf := (isSheaf_iff_isSheaf_of_type _ _).1
    (picardFunctorDegree family degree).property
  have fullSheaf := (isSheaf_iff_isSheaf_of_type _ _).1 (picardFunctor family).property
  obtain ⟨lift, recovers, _⟩ := degreeSheaf imageSieve covering localValues compatible
  refine ⟨lift, (fullSheaf imageSieve covering).isSeparatedFor.ext
    fun localParameter restriction membership ↦ ?_⟩
  change (picardFunctor family).obj.map restriction.op (inclusion.app _ lift) = _
  rw [← NatTrans.naturality_apply, recovers restriction membership, localValues_inclusion]

private theorem isSheafFor_picardDegree_singleton (curve : Scheme.{schemeUniverse})
    [curve.Over (Spec (.of baseField))]
    [IsProper (curve ↘ Spec (.of baseField))]
    [GeometricallyIntegral (curve ↘ Spec (.of baseField))]
    (degree : ℤ) {parameter localParameter : Over (Spec (.of baseField))}
    (cover : localParameter ⟶ parameter) [Flat cover.left] [Surjective cover.left]
    [QuasiCompact cover.left] :
    Presieve.IsSheafFor (picardFunctorDegree (curve ↘ Spec (.of baseField)) degree).obj
      (.singleton cover) := by
  let family := curve ↘ Spec (.of baseField)
  let inclusion := (picardFunctorDegreeι family degree).hom
  have fullSheaf := (isSheaf_iff_isSheaf_of_type _ _).1
    (isSheaf_fpqc_picardFunctor_of_geometricallyIntegral
      (baseField := baseField) (source := curve))
  have fullGlues : Presieve.IsSheafFor (picardFunctor family).obj (.singleton cover) :=
    (Presieve.isSheafFor_iff_generate (.singleton cover)).2
      (fullSheaf _ (singleton_mem_over_fpqcTopology cover))
  rw [Presieve.isSheafFor_singleton] at fullGlues ⊢
  intro localValue localCompatible
  obtain ⟨sectionValue, recovers, unique⟩ := fullGlues (inclusion.app _ localValue)
    fun firstMap secondMap equality ↦ by
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply,
        localCompatible firstMap secondMap equality]
  obtain ⟨lift, rfl⟩ := exists_picardDegree_lift family degree sectionValue fun point ↦ by
    obtain ⟨localPoint, rfl⟩ := cover.left.surjective point
    rw [← picardDegree_map, recovers, picardDegree_inclusion]
  refine ⟨lift, injective_picardFunctorDegreeι_app family degree _ ?_,
    fun otherLift equality ↦ injective_picardFunctorDegreeι_app family degree _ (unique _ ?_)⟩
  · rw [NatTrans.naturality_apply]
    exact recovers
  · beta_reduce
    rw [← NatTrans.naturality_apply, equality]

/-- A degree-zero Picard representative over a separable closure and its
canonical transport of points descend together to a finite intermediate field. -/
theorem exists_finiteSubext_picardDegreeZero_transport
    {closureField : Type schemeUniverse} [Field closureField] [Algebra baseField closureField]
    [IsSepClosure baseField closureField] (curve : Scheme.{schemeUniverse})
    [curve.Over (Spec (.of baseField))]
    [SmoothOfRelativeDimension 1 (curve ↘ Spec (.of baseField))]
    [IsProper (curve ↘ Spec (.of baseField))]
    [GeometricallyIntegral (curve ↘ Spec (.of baseField))]
    (closureRepresentative : Over (Spec (.of closureField)))
    (closureRepresentation : ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap baseField closureField)))).op ⋙
      (picardFunctorDegree (curve ↘ Spec (.of baseField)) 0).obj).RepresentableBy closureRepresentative) :
    ∃ (stage : FiniteSubext baseField closureField)
      (stageRepresentative : Over (Spec (.of stage.1)))
      (comparison : closureRepresentative.left ⟶ stageRepresentative.left)
      (_ : IsPullback comparison closureRepresentative.hom stageRepresentative.hom
        (Spec.map (CommRingCat.ofHom (algebraMap stage.1 closureField)))),
      ∀ {testScheme : Scheme.{schemeUniverse}} (firstMap secondMap : testScheme ⟶ Spec (.of closureField))
        (baseEquality : firstMap ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField closureField)) =
          secondMap ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField closureField))),
        firstMap ≫ Spec.map (CommRingCat.ofHom (algebraMap stage.1 closureField)) =
          secondMap ≫ Spec.map (CommRingCat.ofHom (algebraMap stage.1 closureField)) →
        ∀ pointMap : Over.mk firstMap ⟶ closureRepresentative,
          (closureRepresentation.overTransport firstMap secondMap baseEquality pointMap).left ≫
              comparison = pointMap.left ≫ comparison := by
  have : IsSepClosed closureField := IsSepClosure.sep_closed baseField
  have : Algebra.IsSeparable baseField closureField := inferInstance
  let closureMap := Spec.map (CommRingCat.ofHom (algebraMap baseField closureField))
  let closureCurve := pullback (curve ↘ Spec (.of baseField)) closureMap
  letI : closureCurve.Over (Spec (.of closureField)) :=
    ⟨pullback.snd (curve ↘ Spec (.of baseField)) closureMap⟩
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  letI : SmoothOfRelativeDimension 1 (closureCurve ↘ Spec (.of closureField)) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  letI : IsProper (closureCurve ↘ Spec (.of closureField)) :=
    inferInstanceAs (IsProper (pullback.snd (curve ↘ Spec (.of baseField)) closureMap))
  letI : GeometricallyIntegral (closureCurve ↘ Spec (.of closureField)) :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd (curve ↘ Spec (.of baseField)) closureMap))
  let degreeComparison := picardFunctorDegreeIsoOfIsPullback
    (IsPullback.of_hasPullback (curve ↘ Spec (.of baseField)) closureMap) 0
  let closureDegreeRepresentation := closureRepresentation.ofIso degreeComparison
  letI : IsProper closureRepresentative.hom :=
    isProper_of_representableBy_picardFunctorDegree_zero closureRepresentative closureDegreeRepresentation
  have closureSmooth := smoothOfRelativeDimension_of_representableBy_picardFunctorDegree_zero
    closureRepresentative closureDegreeRepresentation
  letI : Smooth closureRepresentative.hom := closureSmooth.smooth
  obtain ⟨initialStage, initialScheme, initialProjection, _, _, _, initialComparison, initialSquare⟩ := exists_finiteSubext_isPullback (baseField := baseField) closureRepresentative.hom
  let closureBaseMap := Spec.map (CommRingCat.ofHom (algebraMap baseField closureField))
  let initialBaseMap := Spec.map (CommRingCat.ofHom (algebraMap initialStage.1 closureField))
  have baseComposition (stage : FiniteSubext baseField closureField) : Spec.map (CommRingCat.ofHom (algebraMap stage.1 closureField)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap baseField stage.1)) = closureBaseMap :=
    specMap_algebraMap_comp baseField stage.1 closureField
  let firstProjection := tensorSpecPr₁ initialStage
  let secondProjection := tensorSpecPr₂ initialStage
  have projectionEquality : firstProjection ≫ initialBaseMap = secondProjection ≫ initialBaseMap := (isPullback_tensorSpecPr initialStage).w
  have baseProjectionEquality : firstProjection ≫ closureBaseMap = secondProjection ≫ closureBaseMap := by
    rw [← baseComposition initialStage, ← Category.assoc, projectionEquality, Category.assoc]
  let sourceProjection := pullback.snd closureRepresentative.hom firstProjection
  let firstStructure := pullback.fst closureRepresentative.hom firstProjection ≫ closureRepresentative.hom
  let secondStructure := sourceProjection ≫ secondProjection
  have firstStructure_eq : firstStructure = sourceProjection ≫ firstProjection := pullback.condition
  have structureEquality : firstStructure ≫ closureBaseMap = secondStructure ≫ closureBaseMap := by
    rw [firstStructure_eq, Category.assoc, baseProjectionEquality, Category.assoc]
  let universalPoint : Over.mk firstStructure ⟶ closureRepresentative := Over.homMk (pullback.fst closureRepresentative.hom firstProjection) rfl
  let transportedComparison := (closureRepresentation.overTransport firstStructure secondStructure structureEquality universalPoint).left ≫ initialComparison
  let targetProjection := pullback.snd initialProjection (firstProjection ≫ initialBaseMap)
  have firstCompatibility : (pullback.fst closureRepresentative.hom firstProjection ≫ initialComparison) ≫ initialProjection = sourceProjection ≫ firstProjection ≫ initialBaseMap := by
    rw [Category.assoc, initialSquare.w, ← Category.assoc, pullback.condition, Category.assoc]
  have secondCompatibility : transportedComparison ≫ initialProjection = sourceProjection ≫ firstProjection ≫ initialBaseMap := by
    have := Over.w (closureRepresentation.overTransport firstStructure secondStructure structureEquality universalPoint)
    simp only [Over.mk_hom] at this
    rw [Category.assoc, initialSquare.w, ← Category.assoc, this, projectionEquality]
    rfl
  let firstComparison := pullback.lift _ _ firstCompatibility
  let secondComparison := pullback.lift _ _ secondCompatibility
  let diagonal : Spec (.of closureField) ⟶ Spec (.of (TensorProduct initialStage.1 closureField closureField)) :=
    (diagonalSpecCone baseField closureField).π.app (.op initialStage)
  have diagonalEquality : pullback.fst sourceProjection diagonal ≫ firstComparison = pullback.fst sourceProjection diagonal ≫ secondComparison := by
    let diagonalProjection := pullback.fst sourceProjection diagonal
    have diagonalStructureEquality : diagonalProjection ≫ secondStructure = diagonalProjection ≫ firstStructure := by
      rw [firstStructure_eq]
      simp only [secondStructure, ← Category.assoc, diagonalProjection, pullback.condition]
      rw [Category.assoc, Category.assoc]
      exact (congrArg _ (diagonalSpecCone_π_comp_tensorSpecPr₂ initialStage)).trans
        (congrArg _ (diagonalSpecCone_π_comp_tensorSpecPr₁ initialStage)).symm
    have transportNaturality := congrArg CommaMorphism.left
      (closureRepresentation.overDescentDatum.transport_homMk_comp diagonalProjection firstStructure secondStructure structureEquality universalPoint)
    have transportIdentity : (closureRepresentation.overDescentDatum.transport (diagonalProjection ≫ firstStructure) (diagonalProjection ≫ secondStructure)
        (by simp only [Category.assoc]; rw [structureEquality])
        ((Over.homMk diagonalProjection : Over.mk (diagonalProjection ≫ firstStructure) ⟶ Over.mk firstStructure) ≫ universalPoint)).left =
          diagonalProjection ≫ pullback.fst closureRepresentative.hom firstProjection := by
      rw [closureRepresentation.overDescentDatum.transport_left_congr _ rfl
        ((Over.homMk diagonalProjection : Over.mk (diagonalProjection ≫ firstStructure) ⟶ Over.mk firstStructure) ≫ universalPoint)
        ((Over.homMk diagonalProjection : Over.mk (diagonalProjection ≫ firstStructure) ⟶ Over.mk firstStructure) ≫ universalPoint) rfl diagonalStructureEquality rfl,
        Over.DescentDatum.transport_self]
      rfl
    have firstEquation : diagonalProjection ≫ (closureRepresentation.overTransport firstStructure secondStructure structureEquality universalPoint).left = diagonalProjection ≫ pullback.fst closureRepresentative.hom firstProjection :=
      transportNaturality.symm.trans transportIdentity
    apply pullback.hom_ext
    · simp only [firstComparison, secondComparison, Category.assoc, pullback.lift_fst, transportedComparison]
      rw [← Category.assoc, ← firstEquation, Category.assoc]
    · simp only [firstComparison, secondComparison, Category.assoc, pullback.lift_snd]
  have : ∀ {sourceIndex targetIndex : (FiniteSubext baseField closureField)ᵒᵖ}
      (stageTransition : sourceIndex ⟶ targetIndex),
      IsAffineHom (((diagonalDiagram baseField closureField).op ⋙ Scheme.Spec).map stageTransition) := fun stageTransition ↦
    isAffineHom_of_isAffine (X := Spec _) (Y := Spec _) _
  have : ∀ index : (FiniteSubext baseField closureField)ᵒᵖ,
      CompactSpace (((diagonalDiagram baseField closureField).op ⋙ Scheme.Spec).obj index) :=
      fun index ↦
    have : IsAffine (((diagonalDiagram baseField closureField).op ⋙ Scheme.Spec).obj index) :=
      inferInstanceAs (IsAffine (Spec _))
    inferInstance
  have : ∀ index : (FiniteSubext baseField closureField)ᵒᵖ,
      QuasiSeparatedSpace (((diagonalDiagram baseField closureField).op ⋙ Scheme.Spec).obj index) :=
      fun index ↦
    have : IsAffine (((diagonalDiagram baseField closureField).op ⋙ Scheme.Spec).obj index) :=
      inferInstanceAs (IsAffine (Spec _))
    inferInstance
  obtain ⟨⟨stage⟩, stageTransition, eventualEquality⟩ := exists_finiteStage_equal_pullback_maps
    (isLimitDiagonalSpecCone baseField closureField) (stageIndex := .op initialStage)
    sourceProjection targetProjection firstComparison secondComparison (pullback.lift_snd _ _ _)
    (pullback.lift_snd _ _ _) diagonalEquality
  have stageLe : initialStage ≤ stage := leOfHom stageTransition.unop
  let stageInclusion : Spec (.of stage.1) ⟶ Spec (.of initialStage.1) :=
    Spec.map (CommRingCat.ofHom (IntermediateField.inclusion stageLe).toRingHom)
  let closureBase := Spec.map (CommRingCat.ofHom (algebraMap stage.1 closureField))
  have closureFactorization : closureBase ≫ stageInclusion = initialBaseMap := by
    rw [← Spec.map_comp]
    rfl
  let stageRepresentative : Over (Spec (.of stage.1)) := Over.mk (pullback.snd initialProjection stageInclusion)
  let comparison : closureRepresentative.left ⟶ stageRepresentative.left := pullback.lift initialComparison (closureRepresentative.hom ≫ closureBase) (by
    rw [initialSquare.w, Category.assoc, closureFactorization])
  have square : IsPullback comparison closureRepresentative.hom stageRepresentative.hom closureBase := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback initialProjection stageInclusion)
    rw [pullback.lift_fst, closureFactorization]
    exact initialSquare
  refine ⟨stage, stageRepresentative, comparison, square, fun {testScheme} firstMap secondMap baseEquality stageEquality pointMap ↦ ?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, comparison, pullback.lift_fst]
    let pairMap : testScheme ⟶ Spec (.of (TensorProduct stage.1 closureField closureField)) := (isPullback_tensorSpecPr stage).lift firstMap secondMap stageEquality
    let pairInitialMap := pairMap ≫ ((diagonalDiagram baseField closureField).op ⋙ Scheme.Spec).map stageTransition
    have pairInitialMap_fst : pairInitialMap ≫ firstProjection = firstMap := by
      simp only [pairInitialMap, Category.assoc, firstProjection]
      rw [map_comp_tensorSpecPr₁ stageTransition]
      exact (isPullback_tensorSpecPr stage).lift_fst _ _ _
    have pairInitialMap_snd : pairInitialMap ≫ secondProjection = secondMap := by
      simp only [pairInitialMap, Category.assoc, secondProjection]
      rw [map_comp_tensorSpecPr₂ stageTransition]
      exact (isPullback_tensorSpecPr stage).lift_snd _ _ _
    have pointStructure : pointMap.left ≫ closureRepresentative.hom = firstMap := Over.w pointMap
    let liftedPoint : testScheme ⟶ pullback closureRepresentative.hom firstProjection := pullback.lift pointMap.left pairInitialMap (by rw [pointStructure, pairInitialMap_fst])
    have liftedPoint_fst : liftedPoint ≫ pullback.fst closureRepresentative.hom firstProjection = pointMap.left := pullback.lift_fst _ _ _
    have liftedPoint_snd : liftedPoint ≫ sourceProjection = pairInitialMap := pullback.lift_snd _ _ _
    let refinedPoint : testScheme ⟶ pullback sourceProjection (((diagonalDiagram baseField closureField).op ⋙ Scheme.Spec).map stageTransition) :=
      pullback.lift liftedPoint pairMap liftedPoint_snd
    have transportAgreement : liftedPoint ≫ transportedComparison = liftedPoint ≫ pullback.fst closureRepresentative.hom firstProjection ≫ initialComparison := by
      have refinedPoint_fst : refinedPoint ≫ pullback.fst sourceProjection (((diagonalDiagram baseField closureField).op ⋙ Scheme.Spec).map stageTransition) = liftedPoint :=
        pullback.lift_fst _ _ _
      have := congrArg (fun testMap ↦ refinedPoint ≫ testMap ≫ pullback.fst initialProjection (firstProjection ≫ initialBaseMap)) eventualEquality
      simp only [firstComparison, secondComparison, Category.assoc, pullback.lift_fst] at this
      erw [pullback.lift_fst_assoc, pullback.lift_fst_assoc] at this
      rw [← Category.assoc liftedPoint (pullback.fst closureRepresentative.hom firstProjection) initialComparison, liftedPoint_fst]
      refine (congrArg (· ≫ transportedComparison) refinedPoint_fst).symm.trans ?_
      simpa only [Category.assoc] using this.symm
    have transportNaturality := congrArg CommaMorphism.left
      (closureRepresentation.overDescentDatum.transport_homMk_comp liftedPoint firstStructure secondStructure structureEquality universalPoint)
    have firstPointStructure : firstMap = liftedPoint ≫ firstStructure := by
      simp only [firstStructure]
      rw [← Category.assoc, liftedPoint_fst, pointStructure]
    have secondPointStructure : secondMap = liftedPoint ≫ secondStructure := by
      simp only [secondStructure]
      rw [← Category.assoc, liftedPoint_snd, pairInitialMap_snd]
    have transportCongruence := closureRepresentation.overDescentDatum.transport_left_congr baseEquality
      (by simp only [Category.assoc]; rw [structureEquality])
      pointMap ((Over.homMk liftedPoint : Over.mk (liftedPoint ≫ firstStructure) ⟶ Over.mk firstStructure) ≫ universalPoint) firstPointStructure secondPointStructure liftedPoint_fst.symm
    change (closureRepresentation.overDescentDatum.transport firstMap secondMap baseEquality pointMap).left ≫ initialComparison = _
    rw [transportCongruence]
    refine (congrArg (· ≫ initialComparison) transportNaturality).trans ?_
    change (liftedPoint ≫ (closureRepresentation.overTransport firstStructure secondStructure structureEquality universalPoint).left) ≫ initialComparison = _
    rw [Category.assoc, ← liftedPoint_fst, Category.assoc]
    exact transportAgreement
  · simp only [Category.assoc, comparison, pullback.lift_snd]
    have firstEquation := Over.w pointMap
    have secondEquation := Over.w (closureRepresentation.overTransport firstMap secondMap baseEquality pointMap)
    simp only [Over.mk_hom] at firstEquation secondEquation
    rw [← Category.assoc, secondEquation, ← Category.assoc, firstEquation]
    exact stageEquality.symm


/-- The degree-zero Picard sheaf has a representative over a finite separable
intermediate field, compatibly with the given representative over the separable
closure on every test scheme. -/
theorem exists_finiteIntermediateField_picardDegreeZero_representableBy
    {closureField : Type schemeUniverse} [Field closureField] [Algebra baseField closureField]
    [IsSepClosure baseField closureField] (curve : Scheme.{schemeUniverse})
    [curve.Over (Spec (.of baseField))]
    [SmoothOfRelativeDimension 1 (curve ↘ Spec (.of baseField))]
    [IsProper (curve ↘ Spec (.of baseField))]
    [GeometricallyIntegral (curve ↘ Spec (.of baseField))]
    (closureRepresentative : Over (Spec (.of closureField)))
    (closureRepresentation : ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap baseField closureField)))).op ⋙
      (picardFunctorDegree (curve ↘ Spec (.of baseField)) 0).obj).RepresentableBy closureRepresentative) :
    ∃ (intermediateField : IntermediateField baseField closureField),
      FiniteDimensional baseField intermediateField ∧ Algebra.IsSeparable baseField intermediateField ∧
      ∃ (finiteRepresentative : Over (Spec (.of intermediateField))) (comparison : closureRepresentative.left ⟶ finiteRepresentative.left)
        (square : IsPullback comparison closureRepresentative.hom finiteRepresentative.hom (Spec.map (CommRingCat.ofHom (algebraMap intermediateField closureField))))
        (stageRepresentation : ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap baseField intermediateField)))).op ⋙
          (picardFunctorDegree (curve ↘ Spec (.of baseField)) 0).obj).RepresentableBy finiteRepresentative),
        ∀ {testScheme : Scheme.{schemeUniverse}} (testStructure : testScheme ⟶ Spec (.of closureField)) (pointMap : Over.mk testStructure ⟶ closureRepresentative),
          stageRepresentation.homEquiv (Over.homMk (pointMap.left ≫ comparison) (by
            rw [Category.assoc, square.w, ← Category.assoc, Over.w pointMap]; rfl) :
              Over.mk (testStructure ≫ Spec.map (CommRingCat.ofHom (algebraMap intermediateField closureField))) ⟶ finiteRepresentative) =
            (picardFunctorDegree (curve ↘ Spec (.of baseField)) 0).obj.map
              (Over.homMk (𝟙 testScheme) (by
                simp [specMap_algebraMap_comp baseField intermediateField closureField]) :
                (Over.map (Spec.map (CommRingCat.ofHom (algebraMap baseField intermediateField)))).obj
                  (Over.mk (testStructure ≫ Spec.map (CommRingCat.ofHom (algebraMap intermediateField closureField)))) ⟶
                Over.mk (testStructure ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField closureField)))).op
              (closureRepresentation.homEquiv pointMap) := by
  have : Algebra.IsSeparable baseField closureField := inferInstance
  obtain ⟨stage, stageRepresentative, comparison, square, transportInvariant⟩ := exists_finiteSubext_picardDegreeZero_transport curve closureRepresentative closureRepresentation
  let degreeSheaf := (picardFunctorDegree (curve ↘ Spec (.of baseField)) 0).obj
  let closureBaseMap := Spec.map (CommRingCat.ofHom (algebraMap baseField closureField))
  let stageBase := Spec.map (CommRingCat.ofHom (algebraMap baseField stage.1))
  let closureBase := Spec.map (CommRingCat.ofHom (algebraMap stage.1 closureField))
  have baseComposition : closureBase ≫ stageBase = closureBaseMap := specMap_algebraMap_comp baseField stage.1 closureField
  let baseFactorization : Over.map closureBaseMap ≅ Over.map closureBase ⋙ Over.map stageBase :=
    Over.mapCongr closureBaseMap (closureBase ≫ stageBase) baseComposition.symm ≪≫ Over.mapComp closureBase stageBase
  let iteratedRepresentation : ((Over.map closureBase).op ⋙ (Over.map stageBase).op ⋙ degreeSheaf).RepresentableBy closureRepresentative :=
    closureRepresentation.ofIso (Functor.isoWhiskerRight (NatIso.op baseFactorization).symm degreeSheaf)
  have iteratedClassifies {testScheme : Scheme.{schemeUniverse}} (testStructure : testScheme ⟶ Spec (.of closureField)) (descendedPoint : Over.mk testStructure ⟶ closureRepresentative) :
      iteratedRepresentation.homEquiv descendedPoint = degreeSheaf.map (Over.homMk (𝟙 testScheme) (by simp [← baseComposition]) :
        (Over.map stageBase).obj ((Over.map closureBase).obj (Over.mk testStructure)) ⟶ (Over.map closureBaseMap).obj (Over.mk testStructure)).op
          (closureRepresentation.homEquiv descendedPoint) := rfl
  have iteratedTransport {testScheme : Scheme.{schemeUniverse}} (firstMap secondMap : testScheme ⟶ Spec (.of closureField)) (baseEquality : firstMap ≫ closureBase = secondMap ≫ closureBase)
      (pointMap : Over.mk firstMap ⟶ closureRepresentative) :
      iteratedRepresentation.overTransport firstMap secondMap baseEquality pointMap = closureRepresentation.overTransport firstMap secondMap
        (by have := congrArg (· ≫ stageBase) baseEquality; simp only [Category.assoc, baseComposition] at this; exact this)
          pointMap := by
    apply iteratedRepresentation.homEquiv.injective
    rw [Functor.RepresentableBy.homEquiv_overTransport, iteratedClassifies]
    erw [iteratedClassifies firstMap pointMap, Functor.RepresentableBy.homEquiv_overTransport]
    exact presheaf_map_map_eq_of_comp_eq degreeSheaf
      ((Over.map stageBase).map (Functor.RepresentableBy.overMapHomMkId firstMap secondMap baseEquality)) _ _ _
      (by ext; simp) _
  letI : Flat closureBase := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  letI : Surjective closureBase := ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  obtain ⟨stageRepresentation, stageClassifies⟩ := Functor.RepresentableBy.exists_representableBy_of_descent
    (presheaf := (Over.map stageBase).op ⋙ degreeSheaf)
    iteratedRepresentation comparison square
    (fun firstMap secondMap baseEquality pointMap ↦ by rw [iteratedTransport]; exact transportInvariant firstMap secondMap _ baseEquality pointMap)
    (fun testScheme ↦ inferInstance)
    (fun testScheme pointMap pointCompatible ↦
      ⟨EffectiveEpi.desc _ pointMap fun firstMap secondMap coverEquality ↦ by
        simpa using congrArg (pullback.lift firstMap secondMap coverEquality ≫ ·) pointCompatible,
      EffectiveEpi.fac _ _ _⟩)
    fun testScheme ↦
      have : Flat ((Over.map stageBase).map (Functor.RepresentableBy.descentCoverπ closureBase testScheme)).left :=
        inferInstanceAs (Flat (pullback.fst _ _))
      have : Surjective ((Over.map stageBase).map (Functor.RepresentableBy.descentCoverπ closureBase testScheme)).left :=
        inferInstanceAs (Surjective (pullback.fst _ _))
      have : QuasiCompact ((Over.map stageBase).map (Functor.RepresentableBy.descentCoverπ closureBase testScheme)).left :=
        inferInstanceAs (QuasiCompact (pullback.fst _ _))
      Functor.RepresentableBy.isSheafFor_singleton_overMap stageBase _
        (isSheafFor_picardDegree_singleton curve 0 _)
  refine ⟨stage.1, stage.2, Algebra.isSeparable_tower_bot_of_isSeparable baseField stage.1 closureField, stageRepresentative, comparison, square, stageRepresentation,
    fun {testScheme} testStructure pointMap ↦ ?_⟩
  let descendedPoint : (Over.map closureBase).obj (Over.mk testStructure) ⟶ stageRepresentative := Over.homMk (pointMap.left ≫ comparison) (by
    rw [Category.assoc, square.w, ← Category.assoc, Over.w pointMap]; rfl)
  let sectionMap : Over.mk testStructure ⟶ Over.mk (pullback.snd ((Over.map closureBase).obj (Over.mk testStructure)).hom closureBase) :=
    Over.homMk (pullback.lift (𝟙 testScheme) testStructure (by simp)) (pullback.lift_snd _ _ _)
  have sectionEquation : (Over.map closureBase).map sectionMap ≫
      Functor.RepresentableBy.descentCoverπ closureBase ((Over.map closureBase).obj (Over.mk testStructure)) = 𝟙 _ := by
    ext
    exact pullback.lift_fst _ _ _
  have baseEquality := presheaf_map_map_eq_of_comp_eq ((Over.map stageBase).op ⋙ degreeSheaf)
    ((Over.map closureBase).map sectionMap)
    (Functor.RepresentableBy.descentCoverπ closureBase ((Over.map closureBase).obj (Over.mk testStructure))) (𝟙 _) (𝟙 _)
    (by rw [sectionEquation, Category.comp_id]) (stageRepresentation.homEquiv descendedPoint)
  erw [stageClassifies] at baseEquality
  have mapIdentity (sectionValue) : ((Over.map stageBase).op ⋙ degreeSheaf).map (𝟙 ((Over.map closureBase).obj (Over.mk testStructure))).op sectionValue = sectionValue := by
    rw [op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [mapIdentity, mapIdentity] at baseEquality
  change stageRepresentation.homEquiv descendedPoint = _
  rw [← baseEquality]
  change ((Over.map closureBase).op ⋙ (Over.map stageBase).op ⋙ degreeSheaf).map sectionMap.op (iteratedRepresentation.homEquiv _) = _
  rw [← iteratedRepresentation.homEquiv_comp, iteratedClassifies]
  congr 2
  refine Over.OverMorphism.ext (square.hom_ext ?_ ?_)
  · simp only [sectionMap, descendedPoint, Over.comp_left, Over.homMk_left, Category.assoc, IsPullback.lift_fst]
    rw [pullback.lift_fst_assoc]
    exact Category.id_comp _
  · simp only [sectionMap, Over.comp_left, Over.homMk_left, Category.assoc, IsPullback.lift_snd]
    rw [pullback.lift_snd]
    exact (Over.w pointMap).symm


end AlgebraicGeometry
