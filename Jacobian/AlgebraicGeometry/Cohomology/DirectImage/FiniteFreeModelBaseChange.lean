import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeModel
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Restrict
import Jacobian.AlgebraicGeometry.Modules.FiniteFreeComplexPullback
import Jacobian.AlgebraicGeometry.Modules.Limits.Noetherian

/-!
# Finite free cohomology models over arbitrary bases

A proper finitely presented family with relatively flat finitely presented
coefficients has, near every point of its base, a bounded finite free complex
computing all higher direct images after arbitrary Cartesian base change.
The construction descends the family and its coefficients to a Noetherian
model, then pulls back the finite free complex on that model.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A proper finitely presented family with finitely presented relatively flat
coefficients admits a universal finite free cohomology model near every base
point, without a Noetherian hypothesis on the base. -/
theorem exists_isFiniteFreeComplex_higherDirectImage
    {sourceScheme baseScheme : Scheme.{u}} (sourceMap : sourceScheme ⟶ baseScheme)
    [IsProper sourceMap] [LocallyOfFinitePresentation sourceMap]
    (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsFinitePresentation]
    (flat : moduleSheaf.IsFlatOver sourceMap) (point : baseScheme) :
    ∃ (openSubset : baseScheme.Opens)
      (complex : CochainComplex openSubset.toScheme.Modules ℤ) (bound : ℕ),
      point ∈ openSubset ∧ IsFiniteFreeComplex complex bound ∧
      ∀ {targetScheme pulledScheme : Scheme.{u}}
        (baseChange : targetScheme ⟶ openSubset.toScheme)
        (pullbackMap : pulledScheme ⟶ sourceScheme) (pulledMap : pulledScheme ⟶ targetScheme)
        [HasInjectiveResolutions pulledScheme.Modules],
        IsPullback pullbackMap pulledMap sourceMap (baseChange ≫ openSubset.ι) →
        ∀ degree : ℕ, Nonempty
          ((((pullback baseChange).mapHomologicalComplex _).obj complex).homology degree ≅
            (higherDirectImage pulledMap degree).obj ((pullback pullbackMap).obj moduleSheaf)) := by
  obtain ⟨affineOpen, membership, affine, stageRing, noetherian, stageScheme, stageMap,
      proper, finitePresentation, stageModule, finiteCoefficient, stageFlat,
      comparison, baseComparison, stageSquare, ⟨coefficientRecovery⟩⟩ :=
    exists_mem_opens_isPullback_over_noetherian_of_isProper sourceMap moduleSheaf flat point
  letI : IsAffine affineOpen.toScheme := affine
  letI : IsNoetherianRing stageRing := noetherian
  letI : IsProper stageMap := proper
  letI : LocallyOfFinitePresentation stageMap := finitePresentation
  letI : stageModule.IsFinitePresentation := finiteCoefficient
  obtain ⟨denominator, stageComplex, bound, stageMembership, finiteFree, stageComparison⟩ :=
    exists_isFiniteFreeComplex_higherDirectImage_of_isProper stageRing stageMap stageModule
      stageFlat (baseComparison ⟨point, membership⟩)
  let modelOpen := (Spec stageRing).basicOpen denominator
  let localOpen := baseComparison ⁻¹ᵁ modelOpen
  let openMap : localOpen.toScheme ⟶ baseScheme := localOpen.ι ≫ affineOpen.ι
  let modelBase : openMap.opensRange.toScheme ⟶ modelOpen.toScheme :=
    openMap.isoOpensRange.inv ≫ (baseComparison ∣_ modelOpen)
  let complex : CochainComplex openMap.opensRange.toScheme.Modules ℤ :=
    ((pullback modelBase).mapHomologicalComplex _).obj stageComplex
  have pointMembership : point ∈ openMap.opensRange := by
    exact ⟨⟨⟨point, membership⟩, stageMembership⟩, rfl⟩
  refine ⟨openMap.opensRange, complex, bound, pointMembership,
    finiteFree.pullback_complex modelBase, ?_⟩
  intro targetScheme pulledScheme baseChange pullbackMap pulledMap _ square degree
  let localBase : targetScheme ⟶ affineOpen.toScheme :=
    baseChange ≫ openMap.isoOpensRange.inv ≫ localOpen.ι
  have localFactorization : localBase ≫ affineOpen.ι = baseChange ≫ openMap.opensRange.ι := by
    simpa only [localBase, openMap, Category.assoc] using
      congrArg (fun baseMap ↦ baseChange ≫ baseMap) openMap.isoOpensRange_inv_comp
  let localComparison : pulledScheme ⟶ Limits.pullback sourceMap affineOpen.ι :=
    pullback.lift pullbackMap (pulledMap ≫ localBase) (by
      calc
        pullbackMap ≫ sourceMap = pulledMap ≫ (baseChange ≫ openMap.opensRange.ι) := square.w
        _ = pulledMap ≫ (localBase ≫ affineOpen.ι) :=
          congrArg (fun baseMap ↦ pulledMap ≫ baseMap) localFactorization.symm
        _ = (pulledMap ≫ localBase) ≫ affineOpen.ι := (Category.assoc _ _ _).symm)
  have localSquare : IsPullback localComparison pulledMap
      (pullback.snd sourceMap affineOpen.ι) localBase := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback sourceMap affineOpen.ι)
    simpa only [localComparison, pullback.lift_fst, localFactorization] using square
  have baseFactorization : (baseChange ≫ modelBase) ≫ modelOpen.ι =
      localBase ≫ baseComparison := by
    simp only [modelBase, localBase, localOpen, Category.assoc, morphismRestrict_ι]
  have modelSquare : IsPullback (localComparison ≫ comparison) pulledMap stageMap
      ((baseChange ≫ modelBase) ≫ modelOpen.ι) := by
    rw [baseFactorization]
    exact localSquare.paste_horiz stageSquare
  let coefficientComparison :
      (pullback (localComparison ≫ comparison)).obj stageModule ≅
        (pullback pullbackMap).obj moduleSheaf :=
    (pullbackComp localComparison comparison).symm.app stageModule ≪≫
      (pullback localComparison).mapIso coefficientRecovery ≪≫
      pullbackCompOfEq localComparison (pullback.fst sourceMap affineOpen.ι)
        pullbackMap (pullback.lift_fst _ _ _) moduleSheaf
  let complexComparison :
      ((pullback baseChange).mapHomologicalComplex (.up ℤ)).obj complex ≅
        ((pullback (baseChange ≫ modelBase)).mapHomologicalComplex (.up ℤ)).obj stageComplex :=
    (Functor.mapHomologicalComplexCompIso (pullbackComp baseChange modelBase) (.up ℤ)).app
      stageComplex
  obtain ⟨homologyComparison⟩ := stageComparison (baseChange ≫ modelBase)
    (localComparison ≫ comparison) pulledMap modelSquare degree
  exact ⟨(HomologicalComplex.homologyFunctor targetScheme.Modules (.up ℤ) (degree : ℤ)).mapIso
    complexComparison ≪≫ homologyComparison ≪≫
      (higherDirectImage pulledMap degree).mapIso coefficientComparison⟩

/-- Restricting a higher direct image identifies it with the homology of a
universal model whenever the restricted base map factors through the model. -/
theorem nonempty_restrict_higherDirectImage_iso_homology
    {sourceScheme baseScheme : Scheme.{u}} (sourceMap : sourceScheme ⟶ baseScheme)
    [QuasiCompact sourceMap] [IsSeparated sourceMap]
    (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsQuasicoherent]
    {openSubset : baseScheme.Opens} {complex : CochainComplex openSubset.toScheme.Modules ℤ}
    (baseChangeComparison : ∀ {targetScheme pulledScheme : Scheme.{u}}
      (baseChange : targetScheme ⟶ openSubset.toScheme)
      (pullbackMap : pulledScheme ⟶ sourceScheme) (pulledMap : pulledScheme ⟶ targetScheme)
      [HasInjectiveResolutions pulledScheme.Modules],
      IsPullback pullbackMap pulledMap sourceMap (baseChange ≫ openSubset.ι) →
      ∀ degree : ℕ, Nonempty
        ((((pullback baseChange).mapHomologicalComplex _).obj complex).homology degree ≅
          (higherDirectImage pulledMap degree).obj ((pullback pullbackMap).obj moduleSheaf)))
    {targetScheme pulledScheme : Scheme.{u}} (baseChange : targetScheme ⟶ baseScheme)
    (pullbackMap : pulledScheme ⟶ sourceScheme) (pulledMap : pulledScheme ⟶ targetScheme)
    [HasInjectiveResolutions pulledScheme.Modules]
    (square : IsPullback pullbackMap pulledMap sourceMap baseChange)
    (targetOpen : targetScheme.Opens) (localBaseChange : targetOpen.toScheme ⟶ openSubset.toScheme)
    (factorization : localBaseChange ≫ openSubset.ι = targetOpen.ι ≫ baseChange)
    (degree : ℕ) :
    Nonempty (((higherDirectImage pulledMap degree).obj
        ((pullback pullbackMap).obj moduleSheaf)).restrict targetOpen.ι ≅
      (((pullback localBaseChange).mapHomologicalComplex _).obj complex).homology degree) := by
  have localSquare : IsPullback (pulledMap ⁻¹ᵁ targetOpen).ι (pulledMap ∣_ targetOpen)
      pulledMap targetOpen.ι := (isPullback_morphismRestrict pulledMap targetOpen).flip
  have compositeSquare : IsPullback ((pulledMap ⁻¹ᵁ targetOpen).ι ≫ pullbackMap)
      (pulledMap ∣_ targetOpen) sourceMap (localBaseChange ≫ openSubset.ι) := by
    rw [factorization]
    exact localSquare.paste_horiz square
  let restrictionComparison := higherDirectImagePullbackIsoRestrict localSquare
    ((pullback pullbackMap).obj moduleSheaf) degree
  obtain ⟨modelComparison⟩ := baseChangeComparison localBaseChange _ _ compositeSquare degree
  exact ⟨restrictionComparison.symm ≪≫ (higherDirectImage (pulledMap ∣_ targetOpen) degree).mapIso
    ((pullbackComp _ _).app moduleSheaf) ≪≫ modelComparison.symm⟩

end AlgebraicGeometry.Scheme.Modules
