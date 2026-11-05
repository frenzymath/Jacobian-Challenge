import Jacobian.Algebra.Homology.DerivedCategory.Perfect.FiniteFree
import Jacobian.Algebra.Homology.DerivedCategory.Perfect.OfFlat
import Jacobian.Algebra.Homology.Embedding.Map
import Jacobian.AlgebraicGeometry.BasicOpen
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechFinite
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechFlat
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.FreeComplexComparison
import Mathlib.Algebra.Homology.Embedding.HomEquiv
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Local finite free complexes for proper flat families

A finitely presented module, flat over a Noetherian affine base, on a proper
scheme has a local bounded finite free complex computing all higher direct
images after arbitrary base change. The construction uses the bounded flat
Čech truncation, its finite homology, and a finite free ring model. The actual
comparison with the Čech resolution supplies the higher-direct-image
isomorphisms; no model or perfectness hypothesis is required from the caller.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory Limits TensorProduct

namespace HomologicalComplex

section Restriction

variable {sourceIndex targetIndex : Type*}
  {sourceShape : ComplexShape sourceIndex} {targetShape : ComplexShape targetIndex}
  (embedding : sourceShape.Embedding targetShape) [embedding.IsRelIff]
  {category : Type*} [Category* category]

section HasZero

variable [HasZeroMorphisms category] [HasZeroObject category]

private lemma hasLift_restriction_id (complex : HomologicalComplex category targetShape)
    [complex.IsStrictlySupported embedding] :
    embedding.HasLift (𝟙 (complex.restriction embedding)) :=
  fun _ boundary position outside ↦
    (complex.isZero_X_of_isStrictlySupported embedding position
      (boundary.notMem outside)).eq_of_src _ _

private instance isIso_liftExtend_restriction_id
    (complex : HomologicalComplex category targetShape)
    [complex.IsStrictlySupported embedding] :
    IsIso (embedding.liftExtend (𝟙 (complex.restriction embedding))
      (hasLift_restriction_id embedding complex)) := by
  have componentIso (position : targetIndex) :
      IsIso ((embedding.liftExtend (𝟙 (complex.restriction embedding))
        (hasLift_restriction_id embedding complex)).f position) := by
    by_cases inImage : ∃ index, embedding.f index = position
    · obtain ⟨index, rfl⟩ := inImage
      rw [embedding.isIso_liftExtend_f_iff _ _ rfl]
      infer_instance
    · have sourceZero := complex.isZero_X_of_isStrictlySupported embedding position
        (by simpa using inImage)
      have targetZero := (complex.restriction embedding).isZero_extend_X embedding position
        (by simpa using inImage)
      exact ⟨⟨0, sourceZero.eq_of_src _ _, targetZero.eq_of_src _ _⟩⟩
  exact Hom.isIso_of_components _

private def supportedRestrictionIso (complex : HomologicalComplex category targetShape)
    [complex.IsStrictlySupported embedding] :
    complex ≅ (complex.restriction embedding).extend embedding :=
  asIso (embedding.liftExtend (𝟙 (complex.restriction embedding))
    (hasLift_restriction_id embedding complex))

private lemma homRestrict_map_comp_mapExtendIso
    {targetCategory : Type*} [Category* targetCategory] [HasZeroMorphisms targetCategory]
    [HasZeroObject targetCategory] (functor : category ⥤ targetCategory)
    [functor.PreservesZeroMorphisms] {source : HomologicalComplex category targetShape}
    {target : HomologicalComplex category sourceShape}
    (comparison : source ⟶ target.extend embedding) :
    embedding.homRestrict ((functor.mapHomologicalComplex targetShape).map comparison ≫
        (target.mapExtendIso embedding functor).hom) =
      ((functor.mapHomologicalComplex sourceShape).map (embedding.homRestrict comparison) :
        (functor.mapHomologicalComplex sourceShape).obj (source.restriction embedding) ⟶ _) := by
  ext position
  simp [embedding.homRestrict_f _ rfl, mapExtendIso,
    mapExtendX_hom_eq _ _ (embedding.r_f position), restrictionXIso, extendXIso,
    extend.XIso, eqToHom_map]

end HasZero

section Abelian

variable [Abelian category]

private lemma quasiIso_homRestrict_iff
    {source : HomologicalComplex category targetShape} [source.IsStrictlySupported embedding]
    {target : HomologicalComplex category sourceShape}
    (comparison : source ⟶ target.extend embedding) :
    QuasiIso comparison ↔ QuasiIso (embedding.homRestrict comparison) := by
  have decomposition : comparison = (supportedRestrictionIso embedding source).hom ≫
      extendMap (embedding.homRestrict comparison) embedding := by
    apply (embedding.homEquiv source target).injective
    ext position
    simp only [ComplexShape.Embedding.homEquiv_apply_coe, supportedRestrictionIso, asIso_hom,
      ComplexShape.Embedding.homRestrict_comp_extendMap,
      ComplexShape.Embedding.homRestrict_liftExtend, Category.id_comp]
  conv_lhs => rw [decomposition]
  rw [quasiIso_iff_comp_left, quasiIso_extendMap_iff]

end Abelian

end Restriction

end HomologicalComplex

namespace CochainComplex

private theorem exists_free_away_universal_comparison
    {coefficients : Type u} [CommRing coefficients]
    [HasDerivedCategory.{w} (ModuleCat.{u} coefficients)]
    (target : CochainComplex (ModuleCat.{u} coefficients) ℕ)
    (complex : CochainComplex (ModuleCat.{u} coefficients) ℤ) (upperBound : ℤ)
    [complex.IsStrictlyGE 0] [complex.IsStrictlyLE upperBound]
    (flat : ∀ degree, Module.Flat coefficients (complex.X degree))
    (perfect : (DerivedCategory.Q.obj complex).IsPerfect)
    (comparison : complex ⟶ target.extend ComplexShape.embeddingUpNat)
    (universal : ∀ (extensionRing : Type u) [CommRing extensionRing]
      [Algebra coefficients extensionRing],
      QuasiIso (((ModuleCat.extendScalars (algebraMap coefficients extensionRing)).mapHomologicalComplex
        (.up ℤ)).map comparison))
    (prime : Ideal coefficients) [prime.IsPrime] :
    ∃ denominator ∉ prime,
      ∃ (model : CochainComplex (ModuleCat.{u} (Localization.Away denominator)) ℤ)
        (_ : model.IsStrictlyGE 0) (_ : model.IsStrictlyLE upperBound),
        (∀ degree, Module.Free (Localization.Away denominator) (model.X degree) ∧
          Module.Finite (Localization.Away denominator) (model.X degree)) ∧
        ∃ modelComparison : model.restriction ComplexShape.embeddingUpNat ⟶
            ((ModuleCat.extendScalars (algebraMap coefficients
              (Localization.Away denominator))).mapHomologicalComplex _).obj target,
          ∀ (extensionRing : Type u) [CommRing extensionRing]
            [Algebra (Localization.Away denominator) extensionRing],
            QuasiIso (((ModuleCat.extendScalars (algebraMap
              (Localization.Away denominator) extensionRing)).mapHomologicalComplex _).map
                modelComparison) := by
  obtain ⟨denominator, notMem, model, below, above, freeFinite, modelComparison, modelQuasiIso⟩ :=
    DerivedCategory.exists_quasiIso_free_away_of_isPerfect complex 0 upperBound flat perfect prime
  let embedding := ComplexShape.embeddingUpNat
  let extension := ModuleCat.extendScalars (algebraMap coefficients (Localization.Away denominator))
  let extendedComplex : CochainComplex (ModuleCat.{u} (Localization.Away denominator)) ℤ :=
    (extension.mapHomologicalComplex (.up ℤ)).obj complex
  haveI : model.IsStrictlyGE 0 := below
  haveI : model.IsStrictlyLE upperBound := above
  refine ⟨denominator, notMem, model, below, above, freeFinite,
    embedding.homRestrict (modelComparison ≫ (extension.mapHomologicalComplex _).map comparison ≫
      (target.mapExtendIso embedding extension).hom), fun extensionRing _ _ ↦ ?_⟩
  let furtherExtension := ModuleCat.extendScalars
    (algebraMap (Localization.Away denominator) extensionRing)
  let extendedModel : CochainComplex (ModuleCat.{u} extensionRing) ℤ :=
    (furtherExtension.mapHomologicalComplex (.up ℤ)).obj model
  letI : Algebra coefficients extensionRing :=
    ((algebraMap (Localization.Away denominator) extensionRing).comp
      (algebraMap coefficients (Localization.Away denominator))).toAlgebra
  haveI : extendedModel.IsStrictlyGE 0 := by
    rw [isStrictlyGE_iff]
    intro degree negative
    exact furtherExtension.map_isZero (model.isZero_of_isStrictlyGE 0 degree negative)
  haveI : extendedModel.IsStrictlySupported embedding :=
    ⟨fun degree outside ↦ CochainComplex.isZero_of_isStrictlyGE _ 0 degree (by
      by_contra nonnegative
      exact outside degree.toNat (by simp [embedding, Int.toNat_of_nonneg (not_lt.mp nonnegative)]))⟩
  rw [← HomologicalComplex.homRestrict_map_comp_mapExtendIso,
    ← HomologicalComplex.quasiIso_homRestrict_iff]
  have modelFlat (degree : ℤ) : Module.Flat (Localization.Away denominator) (model.X degree) := by
    haveI := (freeFinite degree).1
    infer_instance
  have extendedFlat (degree : ℤ) : Module.Flat (Localization.Away denominator)
      (extendedComplex.X degree) := by
    haveI := flat degree
    exact Module.Flat.of_linearEquiv
      (ModuleCat.tensorEquivExtendScalars coefficients (Localization.Away denominator)
        (complex.X degree)).symm
  haveI : extendedComplex.IsStrictlyLE upperBound := by
    rw [isStrictlyLE_iff]
    intro degree aboveBound
    exact extension.map_isZero (complex.isZero_of_isStrictlyLE upperBound degree aboveBound)
  haveI : QuasiIso ((furtherExtension.mapHomologicalComplex (.up ℤ)).map modelComparison) :=
    quasiIso_extendScalars_of_boundedAbove_flat modelComparison upperBound modelFlat extendedFlat
      modelQuasiIso (algebraMap (Localization.Away denominator) extensionRing)
  let associativity := Functor.mapHomologicalComplexCompIso
    (ModuleCat.extendScalarsComp (algebraMap coefficients (Localization.Away denominator))
      (algebraMap (Localization.Away denominator) extensionRing)).symm (.up ℤ)
  haveI : QuasiIso ((furtherExtension.mapHomologicalComplex (.up ℤ)).map
      ((extension.mapHomologicalComplex (.up ℤ)).map comparison)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (associativity.app complex) (associativity.app (target.extend embedding))
        (associativity.hom.naturality comparison).symm)).mpr (universal extensionRing)
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  infer_instance

end CochainComplex

namespace AlgebraicGeometry.Scheme.Modules

private lemma exists_finite_nonempty_affine_cover (scheme : Scheme.{u}) [CompactSpace scheme] :
    ∃ (coverIndex : Type u) (_ : Finite coverIndex) (_ : Nonempty coverIndex)
      (cover : coverIndex → scheme.Opens),
      (∀ index, IsAffineOpen (cover index)) ∧ iSup cover = ⊤ := by
  obtain ⟨affines, finiteAffines, covering⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : scheme.Opens))).mp
      (by simpa using isCompact_univ)
  haveI : Finite affines := finiteAffines
  refine ⟨Option affines, inferInstance, inferInstance,
    fun index ↦ index.elim ⊥ fun affine ↦ affine.1.1, ?_, ?_⟩
  · rintro (_ | affine)
    exacts [isAffineOpen_bot scheme, affine.1.2]
  · refine le_antisymm le_top ?_
    rw [covering]
    exact iSup₂_le fun affine membership ↦
      le_iSup_of_le (some ⟨affine, membership⟩) le_rfl

/-- Near every point of a Noetherian spectrum, a proper family with finitely
presented flat coefficients has a bounded finite free complex computing its
higher direct images after arbitrary Cartesian base change. -/
theorem exists_isFiniteFreeComplex_higherDirectImage_of_isProper
    (baseRing : Type u) [CommRing baseRing] [IsNoetherianRing baseRing]
    {sourceScheme : Scheme.{u}} (sourceMap : sourceScheme ⟶ Spec (.of baseRing))
    [IsProper sourceMap] (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsFinitePresentation]
    (flat : moduleSheaf.IsFlatOver sourceMap) (point : Spec (.of baseRing)) :
    ∃ (denominator : Γ(Spec (.of baseRing), ⊤))
      (model : CochainComplex ((Spec (.of baseRing)).basicOpen denominator).toScheme.Modules ℤ)
      (bound : ℕ),
      point ∈ (Spec (.of baseRing)).basicOpen denominator ∧ IsFiniteFreeComplex model bound ∧
      ∀ {targetScheme pulledScheme : Scheme.{u}}
        (baseChange : targetScheme ⟶ ((Spec (.of baseRing)).basicOpen denominator).toScheme)
        (pullbackMap : pulledScheme ⟶ sourceScheme) (pulledMap : pulledScheme ⟶ targetScheme)
        [HasInjectiveResolutions pulledScheme.Modules],
        IsPullback pullbackMap pulledMap sourceMap
          (baseChange ≫ ((Spec (.of baseRing)).basicOpen denominator).ι) →
        ∀ degree : ℕ,
          Nonempty ((((pullback baseChange).mapHomologicalComplex _).obj model).homology degree ≅
            (higherDirectImage pulledMap degree).obj ((pullback pullbackMap).obj moduleSheaf)) := by
  classical
  let baseScheme := Spec (.of baseRing)
  haveI : CompactSpace sourceScheme := QuasiCompact.compactSpace_of_compactSpace sourceMap
  obtain ⟨coverIndex, finiteCover, nonemptyCover, cover, affine, covering⟩ :=
    exists_finite_nonempty_affine_cover sourceScheme
  letI : Finite coverIndex := finiteCover
  letI : Nonempty coverIndex := nonemptyCover
  letI : Fintype coverIndex := Fintype.ofFinite coverIndex
  let coefficients := Γ(baseScheme, ⊤)
  letI : IsNoetherianRing coefficients := isNoetherianRing_of_ringEquiv baseRing
    (Scheme.ΓSpecIso (.of baseRing)).symm.commRingCatIsoToRingEquiv
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} coefficients) :=
    HasDerivedCategory.standard (ModuleCat.{u} coefficients)
  let complex : CochainComplex (ModuleCat.{u} coefficients) ℤ :=
    cechModuleComplexTrunc sourceMap moduleSheaf cover
  let upperBound : ℤ := (Fintype.card coverIndex : ℤ) - 1
  haveI : complex.IsStrictlyGE 0 := inferInstanceAs
    ((cechModuleComplexTrunc sourceMap moduleSheaf cover).IsStrictlyGE 0)
  haveI : complex.IsStrictlyLE upperBound := by
    dsimp only [complex, cechModuleComplexTrunc, upperBound]
    infer_instance
  have complexFlat (degree : ℤ) : Module.Flat coefficients (complex.X degree) :=
    flat_cechModuleComplexTrunc_X sourceMap moduleSheaf cover affine covering flat degree
  have complexFinite (degree : ℤ) : Module.Finite coefficients (complex.homology degree) :=
    finite_homology_cechModuleComplexTrunc_of_isProper sourceMap moduleSheaf cover affine covering
      degree
  have finiteDerived (degree : ℤ) : Module.Finite coefficients
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} coefficients) degree).obj
        (DerivedCategory.Q.obj complex)) := by
    haveI : Module.Finite coefficients (complex.homology degree) := complexFinite degree
    exact Module.Finite.equiv (R := coefficients) (M := complex.homology degree)
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} coefficients) degree).app
        complex).toLinearEquiv.symm
  have perfect : (DerivedCategory.Q.obj complex).IsPerfect :=
    DerivedCategory.isPerfect_of_flat_of_finite_homology complex 0 upperBound complexFlat
      (Iso.refl _) finiteDerived
  let primePoint : PrimeSpectrum coefficients := baseScheme.toSpecΓ.base point
  obtain ⟨denominator, notMem, ringModel, below, above, freeFinite, comparison, universal⟩ :=
    CochainComplex.exists_free_away_universal_comparison
      (cechModuleComplexNat sourceMap moduleSheaf cover) complex upperBound complexFlat perfect
      ((cechModuleComplex sourceMap moduleSheaf cover).ιTruncLE upperBound)
      (fun extensionRing _ _ ↦ quasiIso_extendScalars_ιTruncLE_cechModuleComplex sourceMap
        moduleSheaf cover affine covering flat extensionRing) primePoint.asIdeal
  have membership : point ∈ baseScheme.basicOpen denominator := by
    rw [← baseScheme.toSpecΓ_preimage_basicOpen]
    exact notMem
  haveI : ringModel.IsStrictlyGE 0 := below
  haveI : ringModel.IsStrictlyLE upperBound := above
  let localCoefficients := Localization.Away denominator
  haveI : Nontrivial localCoefficients := by
    have primeLocalized := IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers denominator) localCoefficients primePoint.asIdeal primePoint.isPrime
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime denominator).mpr notMem)
    refine nontrivial_of_ne (0 : localCoefficients) 1 fun equality ↦
      primeLocalized.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    rw [← equality]
    exact Ideal.zero_mem _
  haveI (degree : ℤ) : Module.Free localCoefficients (ringModel.X degree) :=
    (freeFinite degree).1
  haveI (degree : ℤ) : Module.Finite localCoefficients (ringModel.X degree) :=
    (freeFinite degree).2
  let ranks : ℤ → ℕ := fun degree ↦ Module.finrank localCoefficients (ringModel.X degree)
  let basis (degree : ℤ) :
      Module.Basis (ULift.{u} (Fin (ranks degree))) localCoefficients (ringModel.X degree) :=
    (Module.finBasis localCoefficients (ringModel.X degree)).reindex Equiv.ulift.symm
  let bound : ℕ := upperBound.toNat
  have ranksZero (degree : ℤ) (outside : degree < 0 ∨ (bound : ℤ) < degree) :
      ranks degree = 0 := by
    haveI : Subsingleton (ringModel.X degree) := by
      apply ModuleCat.subsingleton_of_isZero
      rcases outside with negative | aboveBound
      · exact ringModel.isZero_of_isStrictlyGE 0 degree negative
      · exact ringModel.isZero_of_isStrictlyLE upperBound degree (by dsimp [bound] at aboveBound; omega)
    exact Module.finrank_zero_of_subsingleton
  let openSubset := baseScheme.basicOpen denominator
  let scalarMap : localCoefficients →+* Γ(openSubset.toScheme, ⊤) :=
    Localization.awayLift openSubset.ι.appTop.hom denominator
      (baseScheme.isUnit_ι_appTop_basicOpen denominator)
  have scalarMap_comp : scalarMap.comp (algebraMap coefficients localCoefficients) =
      openSubset.ι.appTop.hom := IsLocalization.Away.lift_comp _ _
  refine ⟨denominator, freeComplexOfBasis ringModel basis scalarMap, bound, membership,
    isFiniteFreeComplex_freeComplexOfBasis ringModel basis scalarMap bound ranksZero, ?_⟩
  intro targetScheme pulledScheme baseChange pullbackMap pulledMap _ square degree
  letI : Algebra localCoefficients Γ(targetScheme, ⊤) :=
    (baseChange.appTop.hom.comp scalarMap).toAlgebra
  letI : Algebra coefficients Γ(targetScheme, ⊤) :=
    (baseChange ≫ openSubset.ι).appTop.hom.toAlgebra
  haveI : IsScalarTower coefficients localCoefficients Γ(targetScheme, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun scalar ↦ by
      change (baseChange ≫ openSubset.ι).appTop scalar =
        baseChange.appTop (scalarMap (algebraMap coefficients localCoefficients scalar))
      rw [← RingHom.comp_apply scalarMap, scalarMap_comp, Scheme.Hom.comp_appTop]
      rfl
  have compatible : algebraMap coefficients Γ(targetScheme, ⊤) =
      ((baseChange ≫ openSubset.ι).appLE ⊤ ⊤
        (le_top.trans (baseChange ≫ openSubset.ι).preimage_top.ge)).hom := by
    rw [RingHom.algebraMap_toAlgebra, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have negativeEmpty (position : ℤ) (negative : position < 0) :
      IsEmpty (ULift.{u} (Fin (ranks position))) := by
    rw [ranksZero position (Or.inl negative)]
    infer_instance
  obtain ⟨homologyComparison⟩ := nonempty_homology_freeComplexOfBasis_iso square moduleSheaf cover
    compatible ringModel basis comparison
    (isAffineOpen_iInf_of_isSeparated sourceMap cover affine) covering negativeEmpty universal degree
  let pullbackComparison :
      ((pullback baseChange).mapHomologicalComplex _).obj
          (freeComplexOfBasis ringModel basis scalarMap) ≅
        freeComplexOfBasis ringModel basis (algebraMap localCoefficients Γ(targetScheme, ⊤)) :=
    pullbackFreeComplexIso _ _ baseChange ≪≫ eqToIso (by
      unfold freeComplexOfBasis
      congr 1)
  exact ⟨(HomologicalComplex.homologyFunctor targetScheme.Modules (.up ℤ) (degree : ℤ)).mapIso
    pullbackComparison ≪≫ homologyComparison⟩

end AlgebraicGeometry.Scheme.Modules
