import Jacobian.AlgebraicGeometry.Descent.Finite
import Jacobian.AlgebraicGeometry.Cohomology.FieldExtension
import Jacobian.AlgebraicGeometry.Geometrically.Smooth
import Jacobian.AlgebraicGeometry.Group.Separated
import Jacobian.AlgebraicGeometry.Group.QuasiProjective
import Jacobian.AlgebraicGeometry.Morphisms.SmoothSourceDescent
import Jacobian.AlgebraicGeometry.Picard.FiniteFieldDescent
import Jacobian.AlgebraicGeometry.ProjectiveSpace.FiniteSet
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Degree-zero Picard schemes over arbitrary fields

The geometric degree-zero Picard representative descends to a finite separable
intermediate field. Its actual group law and properness give a closed projective
embedding, hence affine neighbourhoods of finite sets. Finite-flat effective
descent and the sheaf condition then construct a representative over the original
field, without a rational point or a supplied descended representative.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

open Scheme

private theorem fieldMap_fpqc (baseField extensionField : Type u)
    [Field baseField] [Field extensionField] [Algebra baseField extensionField] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) := by
  have faithfullyFlat :=
    (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap baseField extensionField))).mpr
        ((RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance)
  exact ⟨⟨faithfullyFlat.2, faithfullyFlat.1⟩, inferInstance⟩

private theorem exists_commonField (baseField firstField secondField : Type u)
    [Field baseField] [Field firstField] [Field secondField]
    [Algebra baseField firstField] [Algebra baseField secondField] :
    ∃ (commonField : Type u) (_ : Field commonField)
      (firstEmbedding : firstField →+* commonField)
      (secondEmbedding : secondField →+* commonField),
      firstEmbedding.comp (algebraMap baseField firstField) =
        secondEmbedding.comp (algebraMap baseField secondField) := by
  obtain ⟨maximalIdeal, maximality⟩ :=
    Ideal.exists_maximal (α := firstField ⊗[baseField] secondField)
  letI := maximality
  refine ⟨_, Ideal.Quotient.field maximalIdeal,
    (Ideal.Quotient.mk maximalIdeal).comp
      (Algebra.TensorProduct.includeLeft : firstField →ₐ[baseField]
        firstField ⊗[baseField] secondField),
    (Ideal.Quotient.mk maximalIdeal).comp
      (Algebra.TensorProduct.includeRight : secondField →ₐ[baseField]
        firstField ⊗[baseField] secondField), ?_⟩
  rw [RingHom.comp_assoc, RingHom.comp_assoc,
    AlgHom.comp_algebraMap, AlgHom.comp_algebraMap]

private theorem geometricallyIrreducible_of_field_pullback
    {baseField extensionField : Type u} [Field baseField] [Field extensionField]
    [Algebra baseField extensionField] {source extendedSource : Scheme.{u}}
    {projection : source ⟶ Spec (.of baseField)}
    {extendedProjection : extendedSource ⟶ Spec (.of extensionField)}
    {comparison : extendedSource ⟶ source}
    (square : IsPullback comparison extendedProjection projection
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))
    [GeometricallyIrreducible extendedProjection] : GeometricallyIrreducible projection := by
  rw [geometricallyIrreducible_iff, geometrically_iff_of_commRing]
  intro testField _ _ fiber firstProjection secondProjection fiberSquare
  obtain ⟨commonField, _, firstEmbedding, secondEmbedding, embeddingsAgree⟩ :=
    exists_commonField baseField testField extensionField
  let firstMap : Spec (.of commonField) ⟶ Spec (.of testField) :=
    Spec.map (CommRingCat.ofHom firstEmbedding)
  let secondMap : Spec (.of commonField) ⟶ Spec (.of extensionField) :=
    Spec.map (CommRingCat.ofHom secondEmbedding)
  have baseEquation :
      firstMap ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField testField)) =
        secondMap ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)) := by
    simp only [firstMap, secondMap, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, embeddingsAgree]
  have outer := (IsPullback.of_hasPullback secondProjection firstMap).paste_horiz fiberSquare
  rw [baseEquation] at outer
  have geometricSquare : IsPullback
      (square.lift (pullback.fst secondProjection firstMap ≫ firstProjection)
        (pullback.snd secondProjection firstMap ≫ secondMap) (by simpa using outer.w))
      (pullback.snd secondProjection firstMap) extendedProjection secondMap :=
    IsPullback.of_right (by rwa [square.lift_fst]) (square.lift_snd _ _ _) square
  haveI : IrreducibleSpace ↥(Limits.pullback secondProjection firstMap) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace
      (f := extendedProjection) secondMap _ _ geometricSquare
  letI : Algebra testField commonField := firstEmbedding.toAlgebra
  haveI : Surjective firstMap := (fieldMap_fpqc testField commonField).1.1
  exact (pullback.fst secondProjection firstMap).surjective.irreducibleSpace
    (pullback.fst secondProjection firstMap).continuous

private theorem isProper_of_field_pullback
    {baseField extensionField : Type u} [Field baseField] [Field extensionField]
    [Algebra baseField extensionField] {source extendedSource : Scheme.{u}}
    {projection : source ⟶ Spec (.of baseField)}
    {extendedProjection : extendedSource ⟶ Spec (.of extensionField)}
    {comparison : extendedSource ⟶ source}
    (square : IsPullback comparison extendedProjection projection
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))
    [IsProper extendedProjection] : IsProper projection := by
  letI : MorphismProperty.DescendsAlong (@IsClosedImmersion : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    IsClosedImmersion.descendsAlong_surjective_inf_flat_inf_quasicompact
  letI : MorphismProperty.DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
    rw [IsSeparated.isSeparated_eq_diagonal_isClosedImmersion]
    infer_instance
  letI : MorphismProperty.DescendsAlong (@IsProper : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
    rw [isProper_eq]
    infer_instance
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsProper)
    square.flip (fieldMap_fpqc baseField extensionField) inferInstance

private theorem smooth_of_field_pullback
    {baseField extensionField : Type u} [Field baseField] [Field extensionField]
    [Algebra baseField extensionField] {source extendedSource : Scheme.{u}}
    {projection : source ⟶ Spec (.of baseField)}
    {extendedProjection : extendedSource ⟶ Spec (.of extensionField)}
    {comparison : extendedSource ⟶ source}
    (square : IsPullback comparison extendedProjection projection
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))
    [Smooth extendedProjection] : Smooth projection :=
  MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
    square.flip (fieldMap_fpqc baseField extensionField) inferInstance

private theorem smoothOfRelativeDimension_of_field_pullback
    {baseField extensionField : Type u} [Field baseField] [Field extensionField]
    [Algebra baseField extensionField] {source extendedSource : Scheme.{u}}
    {projection : source ⟶ Spec (.of baseField)}
    {extendedProjection : extendedSource ⟶ Spec (.of extensionField)}
    {comparison : extendedSource ⟶ source}
    (square : IsPullback comparison extendedProjection projection
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))
    (dimension : ℕ) [Smooth projection]
    [SmoothOfRelativeDimension dimension extendedProjection] :
    SmoothOfRelativeDimension dimension projection := by
  refine smoothOfRelativeDimension_of_forall_exists_mem projection dimension fun point ↦ ?_
  obtain ⟨baseOpen, sourceOpen, -, -, point_mem, openLe, localDimension, localSmooth⟩ :=
    Smooth.exists_smoothOfRelativeDimension_resLE projection point
  letI := localSmooth
  have sourceSmooth : SmoothOfRelativeDimension localDimension (sourceOpen.ι ≫ projection) := by
    rw [← Scheme.Hom.resLE_comp_ι projection openLe]
    exact smoothOfRelativeDimension_comp (n := localDimension) (m := 0) _ _
  let extendedOpen := comparison ⁻¹ᵁ sourceOpen
  have openSquare : IsPullback (comparison ∣_ sourceOpen)
      (extendedOpen.ι ≫ extendedProjection) (sourceOpen.ι ≫ projection)
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) :=
    (isPullback_morphismRestrict comparison sourceOpen).paste_vert square
  letI : MorphismProperty.IsStableUnderBaseChange
      (@SmoothOfRelativeDimension.{u} localDimension) :=
    smoothOfRelativeDimension_isStableUnderBaseChange localDimension
  have extendedLocalSmooth : SmoothOfRelativeDimension localDimension
      (extendedOpen.ι ≫ extendedProjection) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @SmoothOfRelativeDimension localDimension) openSquare sourceSmooth
  have extendedSmooth : SmoothOfRelativeDimension dimension
      (extendedOpen.ι ≫ extendedProjection) := by
    simpa only [zero_add] using
      (smoothOfRelativeDimension_comp (n := 0) (m := dimension) extendedOpen.ι extendedProjection)
  letI : Surjective comparison := MorphismProperty.of_isPullback
    (P := @Surjective) square.flip (fieldMap_fpqc baseField extensionField).1.1
  obtain ⟨extendedPoint, point_eq⟩ := comparison.surjective point
  letI : Nonempty extendedOpen := ⟨⟨extendedPoint, by simpa [extendedOpen, point_eq] using point_mem⟩⟩
  obtain rfl := SmoothOfRelativeDimension.eq_of_field
    (extendedOpen.ι ≫ extendedProjection) extendedLocalSmooth extendedSmooth
  exact ⟨sourceOpen, point_mem, sourceSmooth⟩

variable {baseField : Type u} [Field baseField]

/-- A finite-level Picard representative has affine neighbourhoods of finite sets.
Its group law is constructed from its actual Picard representation. -/
theorem exists_isAffineOpen_superset_picardDegreeZero_finiteStage
    {closureField : Type u} [Field closureField] [Algebra baseField closureField]
    [IsSepClosure baseField closureField] (curve : Scheme.{u})
    [curve.Over (Spec (.of baseField))]
    [SmoothOfRelativeDimension 1 (curve ↘ Spec (.of baseField))]
    [IsProper (curve ↘ Spec (.of baseField))]
    [GeometricallyIntegral (curve ↘ Spec (.of baseField))]
    (closureRepresentative : Over (Spec (.of closureField)))
    [Smooth closureRepresentative.hom] [IsProper closureRepresentative.hom]
    [GeometricallyIrreducible closureRepresentative.hom]
    (intermediateField : IntermediateField baseField closureField)
    (stageRepresentative : Over (Spec (.of intermediateField)))
    (comparison : closureRepresentative.left ⟶ stageRepresentative.left)
    (square : IsPullback comparison closureRepresentative.hom stageRepresentative.hom
      (Spec.map (CommRingCat.ofHom (algebraMap intermediateField closureField))))
    (representation : ((Over.map (Spec.map
      (CommRingCat.ofHom (algebraMap baseField intermediateField)))).op ⋙
        (picardFunctorDegree (curve ↘ Spec (.of baseField)) 0).obj).RepresentableBy
          stageRepresentative) :
    ∀ points : Set stageRepresentative.left, points.Finite →
      ∃ openSubset : stageRepresentative.left.Opens,
        IsAffineOpen openSubset ∧ points ⊆ openSubset := by
  let stageMap := Spec.map (CommRingCat.ofHom (algebraMap baseField intermediateField))
  let stageCurve := pullback (curve ↘ Spec (.of baseField)) stageMap
  letI : stageCurve.Over (Spec (.of intermediateField)) :=
    ⟨pullback.snd (curve ↘ Spec (.of baseField)) stageMap⟩
  letI : IsProper (stageCurve ↘ Spec (.of intermediateField)) :=
    inferInstanceAs (IsProper (pullback.snd (curve ↘ Spec (.of baseField)) stageMap))
  letI : GeometricallyIntegral (stageCurve ↘ Spec (.of intermediateField)) :=
    inferInstanceAs
      (GeometricallyIntegral (pullback.snd (curve ↘ Spec (.of baseField)) stageMap))
  letI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  letI : SmoothOfRelativeDimension 1 (stageCurve ↘ Spec (.of intermediateField)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @SmoothOfRelativeDimension 1)
      (IsPullback.of_hasPullback (curve ↘ Spec (.of baseField)) stageMap) inferInstance
  let stageRepresentation :
      (picardFunctorDegree (stageCurve ↘ Spec (.of intermediateField)) 0).obj.RepresentableBy
        stageRepresentative :=
    representation.ofIso
      (picardFunctorDegreeIsoOfIsPullback
        (IsPullback.of_hasPullback (curve ↘ Spec (.of baseField)) stageMap) 0)
  letI : CommGrpObj stageRepresentative :=
    picardDegreeZeroCommGrpObj (stageCurve ↘ Spec (.of intermediateField)) stageRepresentation
  letI : IsProper stageRepresentative.hom := isProper_of_field_pullback square
  letI : Smooth stageRepresentative.hom := smooth_of_field_pullback square
  letI : GeometricallyIrreducible stageRepresentative.hom :=
    geometricallyIrreducible_of_field_pullback square
  letI : GeometricallyIntegral stageRepresentative.hom := inferInstance
  letI : IsSeparated stageRepresentative.hom := inferInstance
  obtain ⟨coordinates, _, embedding, immersion, overBase⟩ :=
    GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral
      stageRepresentative
  letI := immersion
  haveI : UniversallyClosed
      (embedding ≫ ℙ(coordinates; Spec (.of intermediateField)) ↘ Spec (.of intermediateField)) := by
    rw [overBase]
    infer_instance
  letI : UniversallyClosed embedding := UniversallyClosed.of_comp_of_isSeparated embedding
    (ℙ(coordinates; Spec (.of intermediateField)) ↘ Spec (.of intermediateField))
  letI : IsClosedImmersion embedding :=
    IsClosedImmersion.of_isPreimmersion embedding embedding.isClosedMap.isClosed_range
  exact exists_isAffineOpen_superset_of_isClosedImmersion embedding

variable (curve : Scheme.{u}) [curve.Over (Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (curve ↘ Spec (.of baseField))]
  [IsProper (curve ↘ Spec (.of baseField))]
  [GeometricallyIntegral (curve ↘ Spec (.of baseField))]

/-- The degree-zero Picard sheaf of a smooth proper geometrically integral curve
over any field is represented by an abelian variety. Its group law classifies
tensor product, and its smooth dimension is the arithmetic genus of the curve. -/
theorem exists_abelianVariety_picardDegreeZero :
    ∃ (variety : AbelianVariety baseField)
      (representation : (picardFunctorDegree (curve ↘ Spec (.of baseField)) 0).obj.RepresentableBy
        variety.group.X),
      PicardTensorCompatible (curve ↘ Spec (.of baseField)) variety.group representation ∧
      SmoothOfRelativeDimension (curve.arithmeticGenus baseField) variety.group.X.hom := by
  let closureField := SeparableClosure baseField
  let closureMap := Spec.map (CommRingCat.ofHom (algebraMap baseField closureField))
  let closureCurve := pullback (curve ↘ Spec (.of baseField)) closureMap
  let closureSquare := IsPullback.of_hasPullback (curve ↘ Spec (.of baseField)) closureMap
  letI : closureCurve.Over (Spec (.of closureField)) :=
    ⟨pullback.snd (curve ↘ Spec (.of baseField)) closureMap⟩
  letI : IsProper (closureCurve ↘ Spec (.of closureField)) :=
    inferInstanceAs (IsProper (pullback.snd (curve ↘ Spec (.of baseField)) closureMap))
  letI : GeometricallyIntegral (closureCurve ↘ Spec (.of closureField)) :=
    inferInstanceAs
      (GeometricallyIntegral (pullback.snd (curve ↘ Spec (.of baseField)) closureMap))
  letI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  letI : SmoothOfRelativeDimension 1 (closureCurve ↘ Spec (.of closureField)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @SmoothOfRelativeDimension 1) closureSquare inferInstance
  obtain ⟨closureVariety, closureRepresentation, _, closureDimension⟩ :=
    exists_abelianVariety_representableBy_picardFunctorDegree_zero
      (baseField := closureField) (source := closureCurve)
  let closureRepresentative := closureVariety.group.X
  let restrictedRepresentation :
      ((Over.map closureMap).op ⋙
        (picardFunctorDegree (curve ↘ Spec (.of baseField)) 0).obj).RepresentableBy
          closureRepresentative :=
    closureRepresentation.ofIso (picardFunctorDegreeIsoOfIsPullback closureSquare 0).symm
  obtain ⟨intermediateField, finiteExtension, _, stageRepresentative, stageComparison,
    stageSquare, stageRepresentation, _⟩ :=
      exists_finiteIntermediateField_picardDegreeZero_representableBy
        curve closureRepresentative restrictedRepresentation
  letI : FiniteDimensional baseField intermediateField := finiteExtension
  let stageMap := Spec.map (CommRingCat.ofHom (algebraMap baseField intermediateField))
  letI : IsFinite stageMap := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  letI : Flat stageMap := (fieldMap_fpqc baseField intermediateField).1.2
  letI : Surjective stageMap := (fieldMap_fpqc baseField intermediateField).1.1
  letI : LocallyOfFinitePresentation stageMap := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.FinitePresentation.of_finiteType.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
        (inferInstanceAs (LocallyOfFiniteType stageMap)))
  obtain ⟨descendedObject, descentMap, descentSquare, invariant⟩ :=
    stageRepresentation.overDescentDatum.isEffective_of_isFinite
      (exists_isAffineOpen_superset_picardDegreeZero_finiteStage curve
        closureRepresentative intermediateField stageRepresentative stageComparison
          stageSquare stageRepresentation)
  obtain ⟨representation⟩ := Functor.RepresentableBy.nonempty_representableBy_of_descent
    stageRepresentation descentMap descentSquare
    (fun firstMap secondMap equality point ↦ by
      rw [← Functor.RepresentableBy.overDescentDatum_transport]
      exact invariant firstMap secondMap equality point)
    (fun parameter ↦ inferInstance)
    (fun parameter point compatible ↦ by
      have pointCompatible : ∀ {test : Scheme.{u}}
          (firstMap secondMap : test ⟶ pullback parameter.hom stageMap),
          firstMap ≫ pullback.fst parameter.hom stageMap =
            secondMap ≫ pullback.fst parameter.hom stageMap →
          firstMap ≫ point = secondMap ≫ point := by
        intro test firstMap secondMap equality
        let coverMap := pullback.fst parameter.hom stageMap
        let comparison : test ⟶ pullback coverMap coverMap :=
          pullback.lift (f := coverMap) (g := coverMap) firstMap secondMap equality
        have firstProjection : comparison ≫ pullback.fst coverMap coverMap = firstMap :=
          pullback.lift_fst (f := coverMap) (g := coverMap) firstMap secondMap equality
        have secondProjection : comparison ≫ pullback.snd coverMap coverMap = secondMap :=
          pullback.lift_snd (f := coverMap) (g := coverMap) firstMap secondMap equality
        calc
          firstMap ≫ point = comparison ≫ (pullback.fst coverMap coverMap ≫ point) :=
            (congrArg (fun morphism ↦ morphism ≫ point) firstProjection.symm).trans
              (Category.assoc _ _ _)
          _ = comparison ≫ (pullback.snd coverMap coverMap ≫ point) :=
            congrArg (fun morphism ↦ comparison ≫ morphism) compatible
          _ = secondMap ≫ point :=
            (Category.assoc _ _ _).symm.trans
              (congrArg (fun morphism ↦ morphism ≫ point) secondProjection)
      exact ⟨EffectiveEpi.desc _ point pointCompatible,
        EffectiveEpi.fac _ point pointCompatible⟩)
    (fun parameter ↦ by
      have : Flat (Functor.RepresentableBy.descentCoverπ stageMap parameter).left :=
        inferInstanceAs (Flat (pullback.fst _ _))
      have : Surjective (Functor.RepresentableBy.descentCoverπ stageMap parameter).left :=
        inferInstanceAs (Surjective (pullback.fst _ _))
      have : LocallyOfFinitePresentation
          (Functor.RepresentableBy.descentCoverπ stageMap parameter).left :=
        inferInstanceAs (LocallyOfFinitePresentation (pullback.fst _ _))
      exact (Presieve.isSheafFor_iff_generate _).mpr
        (((isSheaf_iff_isSheaf_of_type _ _).mp
          (picardFunctorDegree (curve ↘ Spec (.of baseField)) 0).property) _
            (singleton_mem_over_fppfTopology
              (Functor.RepresentableBy.descentCoverπ stageMap parameter))))
  have baseComposition :
      Spec.map (CommRingCat.ofHom (algebraMap intermediateField closureField)) ≫ stageMap =
        closureMap := by
    change Spec.map (CommRingCat.ofHom (algebraMap intermediateField closureField)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap baseField intermediateField)) =
        Spec.map (CommRingCat.ofHom (algebraMap baseField closureField))
    rw [← Spec.map_comp]
    congr 1
  have descendedSquare : IsPullback (stageComparison ≫ descentMap)
      closureRepresentative.hom descendedObject.hom closureMap := by
    rw [← baseComposition]
    exact stageSquare.paste_horiz descentSquare
  letI : IsProper descendedObject.hom := isProper_of_field_pullback descendedSquare
  letI : Smooth descendedObject.hom := smooth_of_field_pullback descendedSquare
  letI : GeometricallyIrreducible descendedObject.hom :=
    geometricallyIrreducible_of_field_pullback descendedSquare
  letI : CommGrpObj descendedObject :=
    picardDegreeZeroCommGrpObj (curve ↘ Spec (.of baseField)) representation
  have genusEquality : closureCurve.arithmeticGenus closureField =
      curve.arithmeticGenus baseField :=
    arithmeticGenus_pullback (k := baseField) (X := curve) closureField
  letI geometricDimension : SmoothOfRelativeDimension (curve.arithmeticGenus baseField)
      closureRepresentative.hom :=
    Eq.mp (congrArg (fun dimension : ℕ ↦
      SmoothOfRelativeDimension dimension closureVariety.group.X.hom) genusEquality)
      closureDimension
  have genusDimension : SmoothOfRelativeDimension (curve.arithmeticGenus baseField)
      descendedObject.hom :=
    smoothOfRelativeDimension_of_field_pullback descendedSquare (curve.arithmeticGenus baseField)
  exact ⟨⟨CommGrp.mk descendedObject⟩, representation,
    picardTensorCompatible_ofRepresentableBy (curve ↘ Spec (.of baseField)) representation,
    genusDimension⟩

end AlgebraicGeometry
