import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.RankLocus
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechFlat
import Jacobian.AlgebraicGeometry.Modules.Flat
import Jacobian.AlgebraicGeometry.Modules.LocalIsomorphism
import Jacobian.AlgebraicGeometry.Modules.RelativeZeroLocus
import Jacobian.AlgebraicGeometry.Modules.ZeroLocusFunctorial
import Jacobian.AlgebraicGeometry.Picard.Counit
import Jacobian.AlgebraicGeometry.Picard.CounitBaseChange
import Jacobian.AlgebraicGeometry.Picard.Divisors
import Jacobian.AlgebraicGeometry.Picard.Normalized
import Jacobian.AlgebraicGeometry.Sites.OpenImmersion
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsSepClosed

/-!
# The cohomology chart of the Picard functor

The cohomology chart consists of normalized line-bundle classes whose direct
image is invertible and whose positive higher direct images vanish. Its
membership locus is open and is characterized after every base change, so the
chart is an open subfunctor of the normalized Picard functor.
Pulling the chart back along a represented Hilbert functor gives an open
subscheme of its parameter scheme, with membership characterized on every test scheme.
For a proper smooth geometrically integral curve, evaluation of a chart class
cuts out a finite flat relative effective Cartier divisor.
For a class in the chart, the canonical direct-image base-change map is
invertible, so the existing evaluation-map comparison applies without an
additional base-change hypothesis.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

open Scheme

variable {baseField : Type u} [Field baseField] {sourceScheme : Scheme.{u}}

local instance (structureMap : sourceScheme ⟶ Spec (.of baseField))
    [SmoothOfRelativeDimension 1 structureMap] : Smooth structureMap :=
  SmoothOfRelativeDimension.smooth 1 structureMap

/-- A Picard class has invertible direct image in degree zero and vanishing
positive higher direct images. The representative is chosen from its skeleton class. -/
def IsInvertibleDirectImage (structureMap : sourceScheme ⟶ Spec (.of baseField))
    (parameter : Over (Spec (.of baseField)))
    [HasInjectiveResolutions (pullback structureMap parameter.hom).Modules]
    (lineBundle : (pullback structureMap parameter.hom).Pic) : Prop :=
  SheafOfModules.IsInvertible
      ((Modules.higherDirectImage (pullback.snd structureMap parameter.hom) 0).obj
        ((fromSkeleton _).obj lineBundle.val)) ∧
    ∀ degree : ℕ, 0 < degree →
      IsZero ((Modules.higherDirectImage (pullback.snd structureMap parameter.hom) degree).obj
        ((fromSkeleton _).obj lineBundle.val))

/-- The ordinary direct image of a class in the cohomology chart is invertible. -/
theorem IsInvertibleDirectImage.isInvertible_pushforward
    (structureMap : sourceScheme ⟶ Spec (.of baseField))
    (parameter : Over (Spec (.of baseField)))
    [HasInjectiveResolutions (pullback structureMap parameter.hom).Modules]
    (lineBundle : (pullback structureMap parameter.hom).Pic)
    (membership : IsInvertibleDirectImage structureMap parameter lineBundle) :
    ((Modules.pushforward (pullback.snd structureMap parameter.hom)).obj
      ((fromSkeleton _).obj lineBundle.val)).IsInvertible := by
  exact SheafOfModules.IsInvertible.of_iso.{u, u, u}
    ((Functor.rightDerivedZeroIsoSelf
      (Modules.pushforward (pullback.snd structureMap parameter.hom))).app _)
    (property := membership.1)

/-- The cohomology-chart condition cuts out an open subset of each parameter
scheme, characterized by pullback along arbitrary parameter morphisms. -/
theorem exists_opens_isInvertibleDirectImage_map_iff
    (structureMap : sourceScheme ⟶ Spec (.of baseField)) [Flat structureMap]
    [IsProper structureMap] [LocallyOfFinitePresentation structureMap]
    [∀ parameter : Over (Spec (.of baseField)),
      HasInjectiveResolutions (pullback structureMap parameter.hom).Modules]
    {parameter : Over (Spec (.of baseField))}
    (lineBundle : (pullback structureMap parameter.hom).Pic) :
    ∃ openSubset : parameter.left.Opens,
      ∀ (targetParameter : Over (Spec (.of baseField))) (restriction : targetParameter ⟶ parameter),
        IsInvertibleDirectImage structureMap targetParameter
            (Pic.map (baseChangeMap structureMap restriction) lineBundle) ↔
          Set.range restriction.left ⊆ openSubset := by
  let representative : (pullback structureMap parameter.hom).Modules :=
    (fromSkeleton _).obj lineBundle.val
  letI : SheafOfModules.IsInvertible.{u, u, u} representative := lineBundle.isInvertible
  letI : SheafOfModules.IsFiniteLocallyFree.{u, u, u} representative :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} representative
  letI : representative.IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} representative
  obtain ⟨openSubset, _, universal⟩ :=
    Modules.exists_opens_range_subset_iff_isFiniteLocallyFreeInDegree
      (pullback.snd structureMap parameter.hom) representative
      (Modules.isFlatOver_of_isInvertible _ representative) 0 1
  refine ⟨openSubset, fun targetParameter restriction ↦ ?_⟩
  rw [universal _ _ _ (isPullback_baseChangeMap structureMap restriction),
    Modules.isFiniteLocallyFreeInDegree_zero_one_iff]
  let comparison (degree : ℕ) :=
    (Modules.higherDirectImage (pullback.snd structureMap targetParameter.hom) degree).mapIso
      (fromSkeletonToSkeletonIso ((Modules.pullback
        (baseChangeMap structureMap restriction)).obj representative))
  exact ⟨fun ⟨invertible, vanishing⟩ ↦
      ⟨fun degree nonzero ↦
        (vanishing degree (Nat.pos_of_ne_zero nonzero)).of_iso (comparison degree).symm,
        SheafOfModules.IsInvertible.of_iso.{u, u, u} (comparison 0) (property := invertible)⟩,
    fun ⟨vanishing, invertible⟩ ↦
      ⟨SheafOfModules.IsInvertible.of_iso.{u, u, u} (comparison 0).symm
          (property := invertible),
        fun degree positive ↦ (vanishing degree positive.ne').of_iso (comparison degree)⟩⟩

/-- Membership in the cohomology chart is preserved by every base change. -/
theorem IsInvertibleDirectImage.map_of_isProper
    (structureMap : sourceScheme ⟶ Spec (.of baseField)) [Flat structureMap]
    [IsProper structureMap] [LocallyOfFinitePresentation structureMap]
    [∀ parameter : Over (Spec (.of baseField)),
      HasInjectiveResolutions (pullback structureMap parameter.hom).Modules]
    {parameter targetParameter : Over (Spec (.of baseField))}
    (restriction : targetParameter ⟶ parameter)
    {lineBundle : (pullback structureMap parameter.hom).Pic}
    (membership : IsInvertibleDirectImage structureMap parameter lineBundle) :
    IsInvertibleDirectImage structureMap targetParameter
      (Pic.map (baseChangeMap structureMap restriction) lineBundle) := by
  obtain ⟨openSubset, universal⟩ :=
    exists_opens_isInvertibleDirectImage_map_iff structureMap lineBundle
  have fullRange : Set.range (Over.Hom.left (𝟙 parameter)) ⊆ openSubset := by
    refine (universal parameter (𝟙 parameter)).1 ?_
    rwa [baseChangeMap_id, Pic.map_id]
  refine (universal targetParameter restriction).2 (subset_trans (fun point _ ↦ ?_) fullRange)
  exact ⟨point, rfl⟩

private theorem isIso_of_nonzero_residue_pullbacks {scheme : Scheme.{u}}
    {source target : scheme.Modules} [source.IsInvertible] [target.IsInvertible]
    (morphism : source ⟶ target)
    (nonzero : ∀ point : scheme,
      (Modules.pullback (scheme.fromSpecResidueField point)).map morphism ≠ 0) :
    IsIso morphism := by
  refine Modules.Hom.isIso_of_forall_bijective_app morphism fun point ↦ ?_
  obtain ⟨affineOpen, point_mem, _, ⟨sourceGenerator, sourceFree⟩,
      targetGenerator, targetFree⟩ :=
    Modules.exists_isFreeGenerator₂ source target (TopologicalSpace.Opens.mem_top point)
  obtain ⟨coefficient, coefficient_eq⟩ :=
    targetFree.exists_smul_eq (morphism.app affineOpen.1 sourceGenerator)
  have point_basic : point ∈ scheme.basicOpen coefficient := by
    by_contra not_mem
    apply nonzero point
    rw [← Modules.Hom.zeroLocus_eq_bot_iff, ← Modules.Hom.comap_zeroLocus]
    have pointOpen : ⊤ ≤ scheme.fromSpecResidueField point ⁻¹ᵁ affineOpen.1 := by
      intro residuePoint _
      change scheme.fromSpecResidueField point residuePoint ∈ affineOpen.1
      rwa [Scheme.fromSpecResidueField_apply]
    have coefficient_zero :
        (scheme.fromSpecResidueField point).appLE affineOpen.1 ⊤ pointOpen coefficient = 0 := by
      apply (basicOpen_eq_bot_iff _).mp
      rw [Scheme.basicOpen_appLE, top_inf_eq, eq_bot_iff]
      intro residuePoint membership
      apply not_mem
      change scheme.fromSpecResidueField point residuePoint ∈ scheme.basicOpen coefficient
        at membership
      rwa [Scheme.fromSpecResidueField_apply] at membership
    refine le_bot_iff.mp (Scheme.IdealSheafData.le_of_iSup_eq_top
      (fun _ : Unit ↦ (⟨⊤, isAffineOpen_top _⟩ :
        (Spec (scheme.residueField point)).affineOpens)) (by simp) fun _ ↦ ?_)
    rw [Scheme.IdealSheafData.ideal_comap_appLE _ _ affineOpen
      ⟨⊤, isAffineOpen_top _⟩ pointOpen,
      Modules.Hom.ideal_zeroLocus morphism affineOpen sourceFree targetFree
        coefficient_eq.symm, Ideal.map_span, Set.image_singleton, coefficient_zero]
    simp
  refine ⟨scheme.basicOpen coefficient, point_basic, fun smallerOpen contained ↦ ?_⟩
  have contained_affine := contained.trans (scheme.basicOpen_le coefficient)
  have coefficient_unit :
      IsUnit (scheme.presheaf.map (homOfLE contained_affine).op coefficient) := by
    have restrictedUnit := (RingedSpace.isUnit_res_basicOpen scheme.toRingedSpace coefficient).map
      (scheme.presheaf.map (homOfLE contained).op).hom
    convert restrictedUnit using 1
    change _ = (scheme.presheaf.map (homOfLE (scheme.basicOpen_le coefficient)).op ≫
      scheme.presheaf.map (homOfLE contained).op) coefficient
    rw [← Functor.map_comp]
    rfl
  have multiplication (scalar : Γ(scheme, smallerOpen)) :
      morphism.app smallerOpen
          (scalar • source.presheaf.map (homOfLE contained_affine).op sourceGenerator) =
        (scalar * scheme.presheaf.map (homOfLE contained_affine).op coefficient) •
          target.presheaf.map (homOfLE contained_affine).op targetGenerator := by
    rw [Modules.Hom.app_smul, Modules.Hom.app_presheaf_map, ← coefficient_eq, mul_smul,
      Modules.map_smul]
  have factorization : morphism.app smallerOpen ∘
      (fun scalar : Γ(scheme, smallerOpen) ↦
        scalar • source.presheaf.map (homOfLE contained_affine).op sourceGenerator) =
      (fun scalar : Γ(scheme, smallerOpen) ↦
        scalar • target.presheaf.map (homOfLE contained_affine).op targetGenerator) ∘
        (fun scalar ↦ scalar * scheme.presheaf.map (homOfLE contained_affine).op coefficient) :=
    funext multiplication
  refine (Function.Bijective.of_comp_iff _ (sourceFree.map contained_affine).bijective).mp ?_
  rw [factorization]
  exact (targetFree.map contained_affine).bijective.comp
    coefficient_unit.unit.mulRight.bijective

private theorem lTensor_tmul_eq_zero
    {coefficientRing leftModule sourceModule targetModule : Type u}
    [CommRing coefficientRing] [AddCommGroup leftModule] [Module coefficientRing leftModule]
    [AddCommGroup sourceModule] [Module coefficientRing sourceModule]
    [AddCommGroup targetModule] [Module coefficientRing targetModule]
    (linearMap : sourceModule →ₗ[coefficientRing] targetModule)
    (leftElement : leftModule) (sourceElement : sourceModule)
    (vanishing : leftElement ⊗ₜ[coefficientRing] sourceElement = 0) :
    leftElement ⊗ₜ[coefficientRing] linearMap sourceElement = 0 := by
  have transported := congrArg (linearMap.lTensor leftModule) vanishing
  simpa only [LinearMap.lTensor_tmul, map_zero] using transported

private theorem lTensor_cycle_generator_ne_zero
    {coefficientRing extensionRing cochains : Type u}
    [CommRing coefficientRing] [CommRing extensionRing]
    [Algebra coefficientRing extensionRing] [Nontrivial extensionRing]
    [AddCommGroup cochains] [Module coefficientRing cochains]
    (cycles : Submodule coefficientRing cochains)
    (generator : coefficientRing ≃ₗ[coefficientRing] cycles)
    (injectiveTensor : Function.Injective (cycles.subtype.lTensor extensionRing)) :
    (1 : extensionRing) ⊗ₜ[coefficientRing] (generator 1 : cochains) ≠ 0 := by
  intro zeroTensor
  have cycleTensor : (1 : extensionRing) ⊗ₜ[coefficientRing] generator 1 = 0 :=
    injectiveTensor (zeroTensor.trans (map_zero _).symm)
  have unitTensor := congrArg (TensorProduct.rid coefficientRing extensionRing)
    (congrArg ((LinearEquiv.lTensor extensionRing generator).symm) cycleTensor)
  rw [map_zero, map_zero, LinearEquiv.symm_lTensor, LinearEquiv.lTensor_tmul,
    LinearEquiv.symm_apply_apply, TensorProduct.rid_tmul, one_smul] at unitTensor
  exact one_ne_zero unitTensor

private theorem affinePullbackSection_ne_zero
    {scheme base changedScheme changedBase : Scheme.{u}}
    (structureMap : scheme ⟶ base) [IsAffine base] [IsProper structureMap]
    [HasInjectiveResolutions scheme.Modules] (moduleSheaf : scheme.Modules)
    [moduleSheaf.IsInvertible] (flat : moduleSheaf.IsFlatOver structureMap)
    (vanishing : ∀ degree : ℕ, 0 < degree →
      IsZero ((Modules.higherDirectImage structureMap degree).obj moduleSheaf))
    {baseMap : changedBase ⟶ base} {sourceMap : changedScheme ⟶ scheme}
    {changedStructure : changedScheme ⟶ changedBase}
    (square : IsPullback sourceMap changedStructure structureMap baseMap)
    [IsAffine changedBase] [Nontrivial Γ(changedBase, ⊤)]
    (sectionValue : Γ(moduleSheaf, ⊤))
    (generator : Function.Bijective (fun scalar : Γ(base, ⊤) ↦
      scalar • (show Modules.sectionsModule structureMap moduleSheaf ⊤ from sectionValue))) :
    Modules.pullbackSection sourceMap sectionValue ≠ 0 := by
  classical
  letI : CompactSpace scheme := QuasiCompact.compactSpace_of_compactSpace structureMap
  obtain ⟨affines, finiteAffines, covering⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : scheme.Opens))).mp
      (by simpa using isCompact_univ)
  letI : Finite affines := finiteAffines
  let indices := Option affines
  letI : Fintype indices := Fintype.ofFinite indices
  let cover : indices → scheme.Opens := fun index ↦
    index.elim ⊥ fun affine ↦ affine.1.1
  have affineCover : ∀ index, IsAffineOpen (cover index) := by
    rintro (_ | affine)
    exacts [isAffineOpen_bot scheme, affine.1.2]
  have covers : iSup cover = ⊤ := by
    refine le_antisymm le_top ?_
    rw [covering]
    exact iSup₂_le fun affine membership ↦
      le_iSup_of_le (some ⟨affine, membership⟩) le_rfl
  let complex := Modules.cechModuleComplex structureMap moduleSheaf cover
  have exactPositive (degree : ℤ) (positive : 1 ≤ degree) : complex.ExactAt degree := by
    obtain ⟨naturalDegree, rfl⟩ : ∃ naturalDegree : ℕ, (naturalDegree : ℤ) = degree :=
      ⟨degree.toNat, by omega⟩
    obtain ⟨comparison⟩ := Modules.nonempty_homology_cechModuleComplex_linearEquiv
      structureMap moduleSheaf cover affineCover covers naturalDegree
    have zeroImage := vanishing naturalDegree (by omega)
    haveI : Subsingleton Γ((Modules.higherDirectImage structureMap naturalDegree).obj
        moduleSheaf, ⊤) := ⟨fun left right ↦ by
      have zeroIdentity := zeroImage.eq_of_src (𝟙 _) 0
      have left_zero := congr($(congrArg (fun map ↦ Modules.Hom.app map ⊤) zeroIdentity) left)
      have right_zero := congr($(congrArg (fun map ↦ Modules.Hom.app map ⊤) zeroIdentity) right)
      simpa using left_zero.trans right_zero.symm⟩
    haveI : Subsingleton (complex.homology naturalDegree) := comparison.toEquiv.subsingleton
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (ModuleCat.isZero_of_subsingleton _)
  have flatTerms := Modules.flat_cechModuleComplex_X structureMap moduleSheaf cover flat
    (Modules.isAffineOpen_iInf_of_isSeparated structureMap cover affineCover)
  have flatCycles := CochainComplex.flat_ker_d_of_exactAt (C := complex) flatTerms
    (m := 1) exactPositive (Modules.flat_ker_d_cechModuleComplex
      structureMap moduleSheaf cover affineCover covers flat)
  letI := baseMap.appTop.hom.toAlgebra
  let degreeZero := (Modules.cechModuleComplexNat structureMap moduleSheaf cover).extendXIso
    ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) rfl
  let degreeOne := (Modules.cechModuleComplexNat structureMap moduleSheaf cover).extendXIso
    ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) rfl
  have cycle_iff (cochain : complex.X 0) :
      cochain ∈ LinearMap.ker (complex.d 0 1).hom ↔
        Modules.cechModuleD structureMap moduleSheaf cover 0
          (degreeZero.toLinearEquiv cochain) = 0 := by
    change (complex.d 0 1) cochain = 0 ↔ _
    rw [show complex.d 0 1 = degreeZero.hom ≫
        (Modules.cechModuleComplexNat structureMap moduleSheaf cover).d 0 1 ≫
          degreeOne.inv from
      (Modules.cechModuleComplexNat structureMap moduleSheaf cover).extend_d_eq
        ComplexShape.embeddingUpNat (i := 0) (j := 1) rfl rfl,
      Modules.cechModuleComplexNat_d]
    change degreeOne.toLinearEquiv.symm
      (Modules.cechModuleD structureMap moduleSheaf cover 0
        (degreeZero.toLinearEquiv cochain)) = 0 ↔ _
    exact degreeOne.toLinearEquiv.symm.map_eq_zero_iff
  let restriction : Modules.sectionsModule structureMap moduleSheaf ⊤ →ₗ[Γ(base, ⊤)]
      (∀ simplex : Fin 1 → indices,
        Modules.sectionsModule structureMap moduleSheaf (⨅ position, cover (simplex position))) :=
    { toFun sectionValue simplex := moduleSheaf.presheaf.map (homOfLE le_top).op sectionValue
      map_add' left right := by funext simplex; exact map_add _ left right
      map_smul' scalar sectionValue := by
        funext simplex
        exact (Modules.sectionsModuleRestrict structureMap moduleSheaf le_top).map_smul
          scalar sectionValue }
  let extendedRestriction := degreeZero.toLinearEquiv.symm.toLinearMap.comp restriction
  have restriction_cycle (sectionValue : Modules.sectionsModule structureMap moduleSheaf ⊤) :
      extendedRestriction sectionValue ∈ LinearMap.ker (complex.d 0 1).hom := by
    rw [cycle_iff]
    change Modules.cechModuleD structureMap moduleSheaf cover 0
      (degreeZero.toLinearEquiv (degreeZero.toLinearEquiv.symm (restriction sectionValue))) = 0
    rw [LinearEquiv.apply_symm_apply]
    rw [Modules.cechModuleD_apply]
    exact TopCat.Presheaf.cechComplex_d_zero_restrict cover moduleSheaf.presheaf
      sectionValue fun _ ↦ le_top
  have cochainCover (point : scheme) (_ : point ∈ (⊤ : scheme.Opens)) :
      point ∈ ⨆ simplex : Fin 1 → indices, ⨅ position, cover (simplex position) := by
    obtain ⟨index, membership⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (covers.ge (Set.mem_univ point))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨fun _ ↦ index, by simpa using membership⟩
  let cycles : Modules.sectionsModule structureMap moduleSheaf ⊤ ≃ₗ[Γ(base, ⊤)]
      LinearMap.ker (complex.d 0 1).hom :=
    LinearEquiv.ofBijective (extendedRestriction.codRestrict _ restriction_cycle) (by
      constructor
      · intro left right equality
        refine TopCat.Sheaf.eq_of_locally_eq' ⟨moduleSheaf.presheaf, moduleSheaf.isSheaf⟩
          (fun simplex : Fin 1 → indices ↦ ⨅ position, cover (simplex position)) ⊤
          (fun _ ↦ homOfLE le_top) cochainCover left right
          (fun simplex ↦ by
            have cochainEquality := congrArg
              (fun cycle ↦ degreeZero.toLinearEquiv (Subtype.val cycle)) equality
            exact congr_fun (by simpa only [extendedRestriction, LinearMap.codRestrict_apply,
              LinearMap.comp_apply, LinearEquiv.coe_coe,
              LinearEquiv.apply_symm_apply] using cochainEquality) simplex)
      · rintro ⟨cochain, cycle⟩
        have cechCycle : ((TopCat.Presheaf.cechComplex cover).obj
            moduleSheaf.presheaf).d 0 1 (degreeZero.toLinearEquiv cochain) = 0 := by
          have naturalCycle := (cycle_iff cochain).mp cycle
          rwa [Modules.cechModuleD_apply] at naturalCycle
        obtain ⟨sectionValue, restrictions, _⟩ := TopCat.Sheaf.existsUnique_gluing'
          ⟨moduleSheaf.presheaf, moduleSheaf.isSheaf⟩
          (fun simplex : Fin 1 → indices ↦ ⨅ position, cover (simplex position)) ⊤
          (fun _ ↦ homOfLE le_top) cochainCover (degreeZero.toLinearEquiv cochain)
          (fun left right ↦ TopCat.Presheaf.map_inf_eq_of_cechComplex_d_zero
            cover moduleSheaf.presheaf (degreeZero.toLinearEquiv cochain)
              cechCycle left right)
        refine ⟨sectionValue, Subtype.ext (degreeZero.toLinearEquiv.injective ?_)⟩
        change degreeZero.toLinearEquiv
          (degreeZero.toLinearEquiv.symm (restriction sectionValue)) = _
        rw [LinearEquiv.apply_symm_apply]
        exact funext restrictions)
  let globalSection : Modules.sectionsModule structureMap moduleSheaf ⊤ := sectionValue
  let generatorEquiv : Γ(base, ⊤) ≃ₗ[Γ(base, ⊤)]
      Modules.sectionsModule structureMap moduleSheaf ⊤ :=
    LinearEquiv.ofBijective
      { toFun scalar := scalar • globalSection
        map_add' left right := add_smul left right globalSection
        map_smul' left right := mul_smul left right globalSection } generator
  letI : Module.Flat Γ(base, ⊤)
      (LinearMap.ker (complex.d ((0 : ℤ) + 1) (0 + 1 + 1)).hom) :=
    flatCycles (1 : ℤ) (by omega)
  have injectiveTensor := CochainComplex.injective_lTensor_subtype_ker_d
    (C := complex) Γ(changedBase, ⊤) 0 (exactPositive 1 le_rfl)
  have generatorOne : (generatorEquiv.trans cycles) 1 = cycles globalSection := by
    change cycles ((1 : Γ(base, ⊤)) • globalSection) = cycles globalSection
    rw [one_smul]
  have nonzeroExtendedTensor : (1 : Γ(changedBase, ⊤)) ⊗ₜ[Γ(base, ⊤)]
      extendedRestriction globalSection ≠ 0 := by
    have nonzero := lTensor_cycle_generator_ne_zero
      (LinearMap.ker (complex.d 0 1).hom) (generatorEquiv.trans cycles) injectiveTensor
    rw [generatorOne] at nonzero
    exact nonzero
  have nonzeroTensor : (1 : Γ(changedBase, ⊤)) ⊗ₜ[Γ(base, ⊤)]
      restriction globalSection ≠ 0 := by
    intro zeroTensor
    apply nonzeroExtendedTensor
    change (1 : Γ(changedBase, ⊤)) ⊗ₜ[Γ(base, ⊤)]
      degreeZero.toLinearEquiv.symm (restriction globalSection) = 0
    exact lTensor_tmul_eq_zero (leftModule := Γ(changedBase, ⊤))
      degreeZero.toLinearEquiv.symm.toLinearMap 1 (restriction globalSection) zeroTensor
  intro section_zero
  apply nonzeroTensor
  apply (Modules.bijective_cechModuleBaseChange square moduleSheaf rfl cover
    (Modules.isAffineOpen_iInf_of_isSeparated structureMap cover affineCover) 0).1
  rw [map_zero]
  funext simplex
  rw [Modules.cechModuleBaseChange_tmul]
  simp only [one_smul, Modules.sectionsModuleRestrict_apply,
    Modules.pullbackSectionAddHom_apply]
  change ((Modules.pullback sourceMap).obj moduleSheaf).presheaf.map _
    (Modules.pullbackSection sourceMap
      (moduleSheaf.presheaf.map (homOfLE le_top).op sectionValue)) = 0
  rw [Modules.pullbackSection_map, section_zero, map_zero, map_zero]

private theorem chartPullbackSection_ne_zero
    (structureMap : sourceScheme ⟶ Spec (.of baseField)) [Flat structureMap]
    [IsProper structureMap] [LocallyOfFinitePresentation structureMap]
    [∀ parameter : Over (Spec (.of baseField)),
      HasInjectiveResolutions (pullback structureMap parameter.hom).Modules]
    {parameter : Over (Spec (.of baseField))}
    {lineBundle : (pullback structureMap parameter.hom).Pic}
    (membership : IsInvertibleDirectImage structureMap parameter lineBundle)
    {affineOpen : parameter.left.Opens} (affine : IsAffineOpen affineOpen)
    {sectionValue : Γ((Modules.pushforward (pullback.snd structureMap parameter.hom)).obj
      ((fromSkeleton _).obj lineBundle.val), affineOpen)}
    (generator : Modules.IsFreeGenerator sectionValue)
    {targetParameter : Over (Spec (.of baseField))} (restriction : targetParameter ⟶ parameter)
    [IsAffine targetParameter.left] [Nontrivial Γ(targetParameter.left, ⊤)]
    (contained : ⊤ ≤ restriction.left ⁻¹ᵁ affineOpen) :
    Modules.pullbackSection (baseChangeMap structureMap restriction)
      (show Γ((fromSkeleton _).obj lineBundle.val,
        pullback.snd structureMap parameter.hom ⁻¹ᵁ affineOpen) from sectionValue) ≠ 0 := by
  let projection := pullback.snd structureMap parameter.hom
  let representative := (fromSkeleton _).obj lineBundle.val
  let sourceSection : Γ(representative, projection ⁻¹ᵁ affineOpen) := sectionValue
  let localParameter : Over (Spec (.of baseField)) := Over.mk (affineOpen.ι ≫ parameter.hom)
  let inclusion : localParameter ⟶ parameter := Over.homMk affineOpen.ι
  let localComparison := baseChangeMap structureMap inclusion
  let localProjection := pullback.snd structureMap localParameter.hom
  let localRepresentative := (Modules.pullback localComparison).obj representative
  letI : IsAffine localParameter.left := affine
  letI : IsOpenImmersion inclusion.left :=
    show IsOpenImmersion affineOpen.ι from inferInstance
  letI : representative.IsInvertible := lineBundle.isInvertible
  letI : localRepresentative.IsInvertible :=
    Modules.isInvertible_pullback localComparison representative
  have square := isPullback_baseChangeMap structureMap inclusion
  have squareEquation : localComparison ≫ projection = localProjection ≫ inclusion.left :=
    square.w
  letI : IsOpenImmersion localComparison :=
    Modules.isOpenImmersion_of_isPullback square
  have localFull : ⊤ ≤ localComparison ⁻¹ᵁ projection ⁻¹ᵁ affineOpen := by
    rw [← Scheme.Hom.comp_preimage, square.w, Scheme.Hom.comp_preimage]
    simp [inclusion]
  have rangeContains : projection ⁻¹ᵁ affineOpen ≤ localComparison.opensRange := by
    have imageEquation :=
      IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback square.flip
        (⊤ : localParameter.left.Opens)
    simpa [inclusion] using imageEquation.ge
  let localSection : Γ(localRepresentative, ⊤) :=
    localRepresentative.presheaf.map (homOfLE localFull).op
      (Modules.pullbackSection localComparison sourceSection)
  let scalarMap : Γ(parameter.left, affineOpen) ⟶ Γ(localParameter.left, ⊤) :=
    affineOpen.ι.appLE affineOpen ⊤ (by simp)
  letI : IsIso scalarMap := by
    dsimp only [scalarMap]
    infer_instance
  have unitBijective := Modules.bijective_pullbackUnit_app_of_isOpenImmersion
    localComparison representative rangeContains
  have restrictBijective : Function.Bijective
      (localRepresentative.presheaf.map (homOfLE localFull).op) := by
    have fullEquality : localComparison ⁻¹ᵁ projection ⁻¹ᵁ affineOpen = ⊤ :=
      le_antisymm le_top localFull
    letI : IsIso (homOfLE localFull) :=
      ⟨homOfLE (by rw [fullEquality]), Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    exact ConcreteCategory.bijective_of_isIso _
  have scalarCompatibility (scalar : Γ(parameter.left, affineOpen)) :
      localRepresentative.presheaf.map (homOfLE localFull).op
          (Modules.pullbackSection localComparison
            (scalar • sectionValue : Γ((Modules.pushforward projection).obj representative,
              affineOpen))) =
        scalarMap scalar •
          (show Modules.sectionsModule localProjection localRepresentative ⊤ from localSection) := by
    change localRepresentative.presheaf.map _
      (Modules.pullbackSection localComparison
        (projection.app affineOpen scalar • sourceSection)) = _
    rw [Modules.pullbackSection_smul, Modules.map_smul]
    congr 1
    have leftFull : ⊤ ≤ (localComparison ≫ projection) ⁻¹ᵁ affineOpen := by
      simpa only [Scheme.Hom.comp_preimage] using localFull
    have rightFull : ⊤ ≤ (localProjection ≫ inclusion.left) ⁻¹ᵁ affineOpen := by
      simpa only [squareEquation] using leftFull
    have scalarSquare : projection.app affineOpen ≫
        localComparison.appLE (projection ⁻¹ᵁ affineOpen) ⊤ localFull =
        scalarMap ≫ localProjection.appTop := by
      calc
        _ = (localComparison ≫ projection).appLE affineOpen ⊤ leftFull := by
          rw [Scheme.Hom.app_eq_appLE]
          exact Scheme.Hom.appLE_comp_appLE localComparison projection affineOpen
            (projection ⁻¹ᵁ affineOpen) ⊤ le_rfl localFull
        _ = (localProjection ≫ inclusion.left).appLE affineOpen ⊤ rightFull := by
          simp only [squareEquation]
        _ = scalarMap ≫ localProjection.appLE ⊤ ⊤ (by simp) :=
          (Scheme.Hom.appLE_comp_appLE localProjection inclusion.left
            affineOpen ⊤ ⊤ (by simp [inclusion]) (by simp)).symm
        _ = scalarMap ≫ localProjection.appTop := by
          rw [Scheme.Hom.appLE_top_top_eq_appTop]
    change localComparison.appLE (projection ⁻¹ᵁ affineOpen) ⊤ localFull
        (projection.app affineOpen scalar) =
      (localProjection.appTop ≫
        (pullback structureMap localParameter.hom).presheaf.map (𝟙 (Opposite.op ⊤)))
          (scalarMap scalar)
    rw [CategoryTheory.Functor.map_id
      (pullback structureMap localParameter.hom).presheaf (Opposite.op ⊤), Category.comp_id]
    exact congr($scalarSquare scalar)
  have localGenerator : Function.Bijective (fun scalar : Γ(localParameter.left, ⊤) ↦
      scalar • (show Modules.sectionsModule localProjection localRepresentative ⊤
        from localSection)) := by
    apply (Function.Bijective.of_comp_iff _
      (ConcreteCategory.bijective_of_isIso scalarMap)).mp
    have compositeBijective : Function.Bijective
        (fun scalar : Γ(parameter.left, affineOpen) ↦
          (show Modules.sectionsModule localProjection localRepresentative ⊤ from
            localRepresentative.presheaf.map (homOfLE localFull).op
              (Modules.pullbackSection localComparison (scalar • sectionValue)))) :=
      restrictBijective.comp (unitBijective.comp generator.bijective)
    simpa only [Function.comp_def, scalarCompatibility] using compositeBijective
  let localRestriction : targetParameter ⟶ localParameter := Over.homMk
    (IsOpenImmersion.lift affineOpen.ι restriction.left (by
      rintro imagePoint ⟨point, rfl⟩
      exact ⟨⟨restriction.left point, contained (Set.mem_univ point)⟩, rfl⟩)) (by
        change IsOpenImmersion.lift affineOpen.ι restriction.left _ ≫
          (affineOpen.ι ≫ parameter.hom) = targetParameter.hom
        rw [← Category.assoc, IsOpenImmersion.lift_fac]
        exact restriction.w)
  have restriction_eq : localRestriction ≫ inclusion = restriction := by
    ext
    exact IsOpenImmersion.lift_fac _ _ _
  let changedComparison := baseChangeMap structureMap localRestriction
  have localMembership := IsInvertibleDirectImage.map_of_isProper
    structureMap inclusion membership
  have localVanishing (degree : ℕ) (positive : 0 < degree) :
      IsZero ((Modules.higherDirectImage localProjection degree).obj localRepresentative) :=
    (localMembership.2 degree positive).of_iso
      ((Modules.higherDirectImage localProjection degree).mapIso
        (fromSkeletonToSkeletonIso _).symm)
  have nonzero := affinePullbackSection_ne_zero localProjection localRepresentative
    (Modules.isFlatOver_of_isInvertible localProjection localRepresentative)
    localVanishing (isPullback_baseChangeMap structureMap localRestriction)
    localSection localGenerator
  intro zeroSection
  apply nonzero
  change Modules.pullbackSection (baseChangeMap structureMap restriction) sourceSection = 0
    at zeroSection
  have composition := Modules.pullbackComp_inv_app_pullbackSection
    changedComparison localComparison sourceSection
  have composite_eq : changedComparison ≫ localComparison =
      baseChangeMap structureMap restriction := by
    rw [← baseChangeMap_comp, restriction_eq]
  have compositeZero : Modules.pullbackSection
      (changedComparison ≫ localComparison) sourceSection = 0 := by
    let comparisonIso := (Modules.pullbackCongr composite_eq).app representative
    apply (ConcreteCategory.bijective_of_isIso
      (comparisonIso.hom.app ((changedComparison ≫ localComparison) ⁻¹ᵁ
        (projection ⁻¹ᵁ affineOpen)))).1
    rw [map_zero]
    have compatibility := Modules.pullbackCongr_hom_app_pullbackSection
      composite_eq sourceSection
    rw [zeroSection, map_zero] at compatibility
    exact compatibility
  rw [compositeZero, map_zero] at composition
  dsimp only [localSection]
  rw [Modules.pullbackSection_map, ← composition, map_zero]

private theorem chartPullbackCounit_ne_zero
    (structureMap : sourceScheme ⟶ Spec (.of baseField)) [Flat structureMap]
    [IsProper structureMap] [LocallyOfFinitePresentation structureMap]
    [∀ parameter : Over (Spec (.of baseField)),
      HasInjectiveResolutions (pullback structureMap parameter.hom).Modules]
    {parameter : Over (Spec (.of baseField))}
    {lineBundle : (pullback structureMap parameter.hom).Pic}
    (membership : IsInvertibleDirectImage structureMap parameter lineBundle)
    {affineOpen : parameter.left.Opens} (affine : IsAffineOpen affineOpen)
    {sectionValue : Γ((Modules.pushforward (pullback.snd structureMap parameter.hom)).obj
      ((fromSkeleton _).obj lineBundle.val), affineOpen)}
    (generator : Modules.IsFreeGenerator sectionValue)
    {targetParameter : Over (Spec (.of baseField))} (restriction : targetParameter ⟶ parameter)
    [IsAffine targetParameter.left] [Nontrivial Γ(targetParameter.left, ⊤)]
    (contained : ⊤ ≤ restriction.left ⁻¹ᵁ affineOpen) :
    (Modules.pullback (baseChangeMap structureMap restriction)).map
      ((Modules.pullbackPushforwardAdjunction
        (pullback.snd structureMap parameter.hom)).counit.app
          ((fromSkeleton _).obj lineBundle.val)) ≠ 0 := by
  intro zeroCounit
  apply chartPullbackSection_ne_zero structureMap membership affine generator restriction contained
  let adjunction := Modules.pullbackPushforwardAdjunction
    (pullback.snd structureMap parameter.hom)
  have triangle := adjunction.right_triangle_components ((fromSkeleton _).obj lineBundle.val)
  have evaluates : (adjunction.counit.app ((fromSkeleton _).obj lineBundle.val)).app _
      ((adjunction.unit.app ((Modules.pushforward
        (pullback.snd structureMap parameter.hom)).obj
          ((fromSkeleton _).obj lineBundle.val))).app affineOpen sectionValue) = sectionValue :=
    congr($(congrArg (fun map ↦ Modules.Hom.app map affineOpen) triangle) sectionValue)
  have naturality := Modules.pullbackUnit_naturality_apply
    (baseChangeMap structureMap restriction) (adjunction.counit.app _)
    (pullback.snd structureMap parameter.hom ⁻¹ᵁ affineOpen)
    ((adjunction.unit.app ((Modules.pushforward
      (pullback.snd structureMap parameter.hom)).obj
        ((fromSkeleton _).obj lineBundle.val))).app affineOpen sectionValue)
  erw [zeroCounit, evaluates] at naturality
  exact naturality.symm

/-- The canonical direct-image base-change map of a cohomology-chart class
is invertible for every morphism of parameter schemes. -/
theorem IsInvertibleDirectImage.isIso_pushforwardBaseChange
    (structureMap : sourceScheme ⟶ Spec (.of baseField)) [Flat structureMap]
    [IsProper structureMap] [LocallyOfFinitePresentation structureMap]
    [∀ parameter : Over (Spec (.of baseField)),
      HasInjectiveResolutions (pullback structureMap parameter.hom).Modules]
    {parameter targetParameter : Over (Spec (.of baseField))}
    (restriction : targetParameter ⟶ parameter)
    {lineBundle : (pullback structureMap parameter.hom).Pic}
    (membership : IsInvertibleDirectImage structureMap parameter lineBundle) :
    IsIso ((Modules.pushforwardBaseChange
      (isPullback_baseChangeMap structureMap restriction).w.symm).app
        ((fromSkeleton _).obj lineBundle.val)) := by
  let projection := pullback.snd structureMap parameter.hom
  let changedProjection := pullback.snd structureMap targetParameter.hom
  let comparison := baseChangeMap structureMap restriction
  let representative := (fromSkeleton _).obj lineBundle.val
  let pullbackSquare := Modules.pullbackSquareIso
    (isPullback_baseChangeMap structureMap restriction).w.symm
  let categoricalSquare : TwoSquare (Modules.pullback restriction.left)
      (Modules.pullback projection) (Modules.pullback changedProjection)
      (Modules.pullback comparison) := pullbackSquare.hom
  let adjunction := Modules.pullbackPushforwardAdjunction projection
  let changedAdjunction := Modules.pullbackPushforwardAdjunction changedProjection
  let baseChangeMorphism :
      (Modules.pullback restriction.left).obj ((Modules.pushforward projection).obj representative) ⟶
        (Modules.pushforward changedProjection).obj
          ((Modules.pullback comparison).obj representative) :=
    (Modules.pushforwardBaseChange
      (isPullback_baseChangeMap structureMap restriction).w.symm).app representative
  letI : ((Modules.pushforward projection).obj representative).IsInvertible :=
    IsInvertibleDirectImage.isInvertible_pushforward
      structureMap parameter lineBundle membership
  letI : ((Modules.pullback restriction.left).obj
      ((Modules.pushforward projection).obj representative)).IsInvertible :=
    Modules.isInvertible_pullback restriction.left _
  have pulledMembership := IsInvertibleDirectImage.map_of_isProper
    structureMap restriction membership
  letI : ((Modules.pushforward changedProjection).obj
      ((Modules.pullback comparison).obj representative)).IsInvertible :=
    SheafOfModules.IsInvertible.of_iso.{u, u, u}
      (((Functor.rightDerivedZeroIsoSelf (Modules.pushforward changedProjection)).app _) ≪≫
        (Modules.pushforward changedProjection).mapIso (fromSkeletonToSkeletonIso _))
      (property := pulledMembership.1)
  change IsIso baseChangeMorphism
  refine isIso_of_nonzero_residue_pullbacks baseChangeMorphism fun point zeroFibre ↦ ?_
  obtain ⟨affineOpen, point_mem, _, generatorSection, generator⟩ :=
    Modules.exists_isFreeGenerator ((Modules.pushforward projection).obj representative)
      (x := restriction.left point) (TopologicalSpace.Opens.mem_top _)
  let residueParameter : Over (Spec (.of baseField)) :=
    Over.mk (targetParameter.left.fromSpecResidueField point ≫ targetParameter.hom)
  let residueMap : residueParameter ⟶ targetParameter :=
    Over.homMk (targetParameter.left.fromSpecResidueField point)
  have contained : ⊤ ≤ (residueMap ≫ restriction).left ⁻¹ᵁ affineOpen.1 := by
    intro residuePoint _
    change restriction.left (targetParameter.left.fromSpecResidueField point residuePoint) ∈
      affineOpen.1
    rw [Scheme.fromSpecResidueField_apply]
    exact point_mem
  letI : IsAffine residueParameter.left := inferInstanceAs (IsAffine (Spec _))
  letI : Nontrivial Γ(residueParameter.left, ⊤) :=
    (Scheme.ΓSpecIso (targetParameter.left.residueField point)).commRingCatIsoToRingEquiv.nontrivial
  apply chartPullbackCounit_ne_zero structureMap membership affineOpen.2 generator
    (residueMap ≫ restriction) contained
  let residueComparison := baseChangeMap structureMap residueMap
  let residueProjection := pullback.snd structureMap residueParameter.hom
  let commutes := (isPullback_baseChangeMap structureMap residueMap).w
  let pullbackComparison : Modules.pullback changedProjection ⋙
      Modules.pullback residueComparison ≅ Modules.pullback residueMap.left ⋙
        Modules.pullback residueProjection :=
    Modules.pullbackComp residueComparison changedProjection ≪≫
      Modules.pullbackCongr commutes ≪≫ (Modules.pullbackComp _ residueMap.left).symm
  have pulled_zero : (Modules.pullback residueComparison).map
      ((Modules.pullback changedProjection).map baseChangeMorphism) = 0 := by
    rw [← Functor.comp_map, ← NatIso.naturality_2 pullbackComparison baseChangeMorphism,
      Functor.comp_map]
    erw [zeroFibre]
    rw [Functor.map_zero, zero_comp, comp_zero]
  have counitFactorization : (Modules.pullback comparison).map
      (adjunction.counit.app representative) =
      inv ((pullbackSquare.app ((Modules.pushforward projection).obj representative)).hom) ≫
        (Modules.pullback changedProjection).map baseChangeMorphism ≫
          changedAdjunction.counit.app _ := by
    have mateCounit :
        (Modules.pullback changedProjection).map baseChangeMorphism ≫
            changedAdjunction.counit.app ((Modules.pullback comparison).obj representative) =
          (pullbackSquare.app ((Modules.pushforward projection).obj representative)).hom ≫
            (Modules.pullback comparison).map (adjunction.counit.app representative) :=
      mateEquiv_counit adjunction changedAdjunction categoricalSquare representative
    apply (cancel_epi
      (pullbackSquare.app ((Modules.pushforward projection).obj representative)).hom).mp
    rw [IsIso.hom_inv_id_assoc]
    exact mateCounit.symm
  have counit_zero : (Modules.pullback residueComparison).map
      ((Modules.pullback comparison).map (adjunction.counit.app representative)) = 0 := by
    rw [counitFactorization, Functor.map_comp, Functor.map_comp, pulled_zero,
      zero_comp, comp_zero]
  rw [baseChangeMap_comp, ← NatIso.naturality_1
    (Modules.pullbackComp residueComparison comparison), Functor.comp_map]
  erw [counit_zero]
  rw [zero_comp, comp_zero]

/-- Normalized Picard classes with invertible direct image in degree zero. -/
def picardFunctorInvertibleDirectImage
    (structureMap : sourceScheme ⟶ Spec (.of baseField)) [Flat structureMap]
    [IsProper structureMap] [LocallyOfFinitePresentation structureMap]
    (sectionMorphism : Spec (.of baseField) ⟶ sourceScheme)
    (sectionCondition : sectionMorphism ≫ structureMap = 𝟙 (Spec (.of baseField)))
    [∀ parameter : Over (Spec (.of baseField)),
      HasInjectiveResolutions (pullback structureMap parameter.hom).Modules] :
    Subfunctor (picardFunctorNormalized structureMap sectionMorphism sectionCondition).toFunctor where
  obj parameter := {lineBundle | IsInvertibleDirectImage structureMap parameter.unop
    (lineBundle : (picardPresheaf structureMap).obj parameter)}
  map := by
    rintro ⟨parameter⟩ ⟨targetParameter⟩ ⟨restriction⟩ lineBundle membership
    exact IsInvertibleDirectImage.map_of_isProper structureMap restriction membership

/-- The cohomology chart is representable by open immersions in the
normalized Picard functor. -/
theorem isOpenImmersion_picardFunctorInvertibleDirectImage_ι [IsSepClosed baseField]
    (structureMap : sourceScheme ⟶ Spec (.of baseField))
    [SmoothOfRelativeDimension 1 structureMap] [IsProper structureMap]
    [GeometricallyIntegral structureMap]
    (sectionMorphism : Spec (.of baseField) ⟶ sourceScheme)
    (sectionCondition : sectionMorphism ≫ structureMap = 𝟙 (Spec (.of baseField)))
    [∀ parameter : Over (Spec (.of baseField)),
      HasInjectiveResolutions (pullback structureMap parameter.hom).Modules] :
    (IsOpenImmersion.inverseImage (Over.forget (Spec (.of baseField)))).relative
      uliftYoneda.{u + 1}
        (picardFunctorInvertibleDirectImage structureMap sectionMorphism sectionCondition).ι :=
  relative_isOpenImmersion_of_exists_opens fun _ lineBundle ↦
    exists_opens_isInvertibleDirectImage_map_iff structureMap lineBundle.1

/-- A Hilbert parameter scheme has an open locus where the normalized divisor
class lies in the cohomology chart, universally for all test schemes. -/
theorem exists_opens_hilbertToPicardNormalized_mem_iff [IsSepClosed baseField]
    (structureMap : sourceScheme ⟶ Spec (.of baseField))
    [SmoothOfRelativeDimension 1 structureMap] [IsProper structureMap]
    [GeometricallyIntegral structureMap]
    (sectionMorphism : Spec (.of baseField) ⟶ sourceScheme)
    (sectionCondition : sectionMorphism ≫ structureMap = 𝟙 (Spec (.of baseField)))
    [∀ parameter : Over (Spec (.of baseField)),
      HasInjectiveResolutions (pullback structureMap parameter.hom).Modules]
    (divisorDegree : ℕ) (hilbertScheme : Over (Spec (.of baseField)))
    (representation : (hilbertPresheaf structureMap divisorDegree).RepresentableBy hilbertScheme) :
    ∃ openSubset : hilbertScheme.left.Opens,
      ∀ (parameter : Over (Spec (.of baseField))) (parameterMap : parameter ⟶ hilbertScheme),
        hilbertToPicardNormalized structureMap sectionMorphism sectionCondition divisorDegree
            parameter (representation.homEquiv parameterMap) ∈
          (picardFunctorInvertibleDirectImage structureMap sectionMorphism sectionCondition).obj
            (.op parameter) ↔ Set.range parameterMap.left ⊆ openSubset := by
  let universalDivisor := representation.homEquiv (𝟙 hilbertScheme)
  obtain ⟨openSubset, universal⟩ := exists_opens_of_relative_isOpenImmersion
    (isOpenImmersion_picardFunctorInvertibleDirectImage_ι structureMap sectionMorphism
      sectionCondition) hilbertScheme
    (hilbertToPicardNormalized structureMap sectionMorphism sectionCondition divisorDegree
      hilbertScheme universalDivisor)
  refine ⟨openSubset, fun parameter parameterMap ↦ ?_⟩
  have divisorComparison := representation.homEquiv_comp parameterMap (𝟙 hilbertScheme)
  rw [Category.comp_id] at divisorComparison
  have membership := universal parameter parameterMap
  rw [hilbertToPicardNormalized_naturality, ← divisorComparison] at membership
  exact membership

/-- Evaluation of a chart class is nonzero on every fibre over the parameter scheme. -/
theorem IsInvertibleDirectImage.pullback_fiberι_directImageCounit_ne_zero
    (structureMap : sourceScheme ⟶ Spec (.of baseField)) [Flat structureMap]
    [IsProper structureMap] [LocallyOfFinitePresentation structureMap]
    [∀ parameter : Over (Spec (.of baseField)),
      HasInjectiveResolutions (pullback structureMap parameter.hom).Modules]
    (parameter : Over (Spec (.of baseField)))
    (lineBundle : (pullback structureMap parameter.hom).Pic)
    (membership : IsInvertibleDirectImage structureMap parameter lineBundle)
    (point : parameter.left) :
    (Modules.pullback ((pullback.snd structureMap parameter.hom).fiberι point)).map
      (Pic.directImageCounit structureMap parameter lineBundle) ≠ 0 := by
  let residueParameter : Over (Spec (.of baseField)) :=
    Over.mk (parameter.left.fromSpecResidueField point ≫ parameter.hom)
  let restriction : residueParameter ⟶ parameter :=
    Over.homMk (parameter.left.fromSpecResidueField point)
  let residueClass : (pullback structureMap residueParameter.hom).Pic :=
    Pic.map (baseChangeMap structureMap restriction) lineBundle
  have residueMembership : IsInvertibleDirectImage structureMap residueParameter residueClass :=
    IsInvertibleDirectImage.map_of_isProper structureMap restriction membership
  letI : ((fromSkeleton _).obj lineBundle.val).IsInvertible := lineBundle.isInvertible
  letI : ((fromSkeleton _).obj residueClass.val).IsInvertible := residueClass.isInvertible
  letI : ((Modules.pushforward (pullback.snd structureMap parameter.hom)).obj
      ((fromSkeleton _).obj lineBundle.val)).IsInvertible :=
    IsInvertibleDirectImage.isInvertible_pushforward structureMap parameter lineBundle membership
  letI : ((Modules.pushforward (pullback.snd structureMap residueParameter.hom)).obj
      ((fromSkeleton _).obj residueClass.val)).IsInvertible :=
    IsInvertibleDirectImage.isInvertible_pushforward structureMap residueParameter residueClass
      residueMembership
  letI : IsIso ((Modules.pushforwardBaseChange
      (isPullback_baseChangeMap structureMap restriction).w.symm).app
        ((fromSkeleton _).obj lineBundle.val)) :=
    IsInvertibleDirectImage.isIso_pushforwardBaseChange structureMap restriction membership
  letI : Nonempty residueParameter.left :=
    ⟨(IsLocalRing.closedPoint (parameter.left.residueField point) :
      Spec (parameter.left.residueField point))⟩
  have residueNonzero :
      (Pic.directImageCounit structureMap residueParameter residueClass).zeroLocus ≠ ⊥ := by
    rw [Ne, Modules.Hom.zeroLocus_eq_bot_iff]
    exact Pic.directImageCounit_ne_zero structureMap residueParameter residueClass
  let fibreIso : (pullback.snd structureMap parameter.hom).fiber point ≅
      pullback structureMap residueParameter.hom :=
    pullbackLeftPullbackSndIso structureMap parameter.hom
      (parameter.left.fromSpecResidueField point)
  have fibreEquation : fibreIso.hom ≫ baseChangeMap structureMap restriction =
      (pullback.snd structureMap parameter.hom).fiberι point := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
      exact pullbackLeftPullbackSndIso_hom_fst _ _ _
    · simp [fibreIso, Scheme.Hom.fiberι, restriction, residueParameter, pullback.condition]
  have comparison :
      (Pic.directImageCounit structureMap parameter lineBundle).zeroLocus.comap
          (baseChangeMap structureMap restriction) =
        (Pic.directImageCounit structureMap residueParameter residueClass).zeroLocus :=
    comap_zeroLocus_directImageCounit structureMap restriction lineBundle
  intro vanishing
  apply residueNonzero
  have restrictedZero :
      ((Pic.directImageCounit structureMap parameter lineBundle).zeroLocus.comap
        (baseChangeMap structureMap restriction)).comap fibreIso.hom = ⊥ := by
    rw [← IdealSheafData.comap_comp, fibreEquation, Modules.Hom.comap_zeroLocus,
      Modules.Hom.zeroLocus_eq_bot_iff]
    exact vanishing
  rw [← comparison, ← IdealSheafData.comap_id (IdealSheafData.comap _ _),
    ← fibreIso.inv_hom_id, IdealSheafData.comap_comp, restrictedZero,
    IdealSheafData.comap_bot]

/-- On a proper smooth geometrically integral curve, evaluation of a chart class
defines a relative effective Cartier divisor that is finite, flat and locally
of finite presentation over the arbitrary parameter scheme. -/
theorem IsInvertibleDirectImage.isInvertible_zeroLocus_directImageCounit_and_isFinite
    (structureMap : sourceScheme ⟶ Spec (.of baseField)) [IsProper structureMap]
    [SmoothOfRelativeDimension 1 structureMap] [GeometricallyIntegral structureMap]
    [∀ parameter : Over (Spec (.of baseField)),
      HasInjectiveResolutions (pullback structureMap parameter.hom).Modules]
    (parameter : Over (Spec (.of baseField)))
    (lineBundle : (pullback structureMap parameter.hom).Pic)
    (membership : IsInvertibleDirectImage structureMap parameter lineBundle) :
    letI := IsInvertibleDirectImage.isInvertible_pushforward
      structureMap parameter lineBundle membership
    (Pic.directImageCounit structureMap parameter lineBundle).zeroLocus.IsInvertible ∧
      IsFinite ((Pic.directImageCounit structureMap parameter lineBundle).zeroLocus.subschemeι ≫
        pullback.snd structureMap parameter.hom) ∧
      Flat ((Pic.directImageCounit structureMap parameter lineBundle).zeroLocus.subschemeι ≫
        pullback.snd structureMap parameter.hom) ∧
      LocallyOfFinitePresentation
        ((Pic.directImageCounit structureMap parameter lineBundle).zeroLocus.subschemeι ≫
          pullback.snd structureMap parameter.hom) := by
  let projection : pullback structureMap parameter.hom ⟶ parameter.left :=
    pullback.snd structureMap parameter.hom
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  letI : SmoothOfRelativeDimension 1 projection :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  letI : IsProper projection :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  letI : GeometricallyIntegral projection := inferInstance
  letI : ((fromSkeleton _).obj lineBundle.val).IsInvertible := lineBundle.isInvertible
  letI : ((Modules.pushforward projection).obj
      ((fromSkeleton _).obj lineBundle.val)).IsInvertible :=
    IsInvertibleDirectImage.isInvertible_pushforward structureMap parameter lineBundle membership
  exact Modules.Hom.isInvertible_zeroLocus_and_isFinite projection
    (Pic.directImageCounit structureMap parameter lineBundle)
    (fun point ↦ inferInstance)
    (fun point ↦ IsInvertibleDirectImage.pullback_fiberι_directImageCounit_ne_zero
      structureMap parameter lineBundle membership point)

end AlgebraicGeometry
