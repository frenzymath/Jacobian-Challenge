import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.GlobalSections
import Jacobian.RingTheory.GradedAlgebra.HomogeneousLocalization.Transition
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Morphisms to projective spectra from global sections

The morphism induced by a graded ring map to global sections is natural in the
source and unchanged by homogeneous unit rescaling. On affine sources, ring
generation by homogeneous images gives a closed immersion into a standard chart.
-/

noncomputable section

set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical morphism `sourceScheme.basicOpen sectionValue ⟶ Spec Γ(sourceScheme, ⊤)[1/sectionValue]`, composed with `Spec` of the
localization map, is the composite `sourceScheme.basicOpen sectionValue ⟶ sourceScheme ⟶ Spec Γ(sourceScheme, ⊤)`. -/
@[reassoc]
private lemma resLE_toSpecΓ_basicOpenIsoSpecAway_hom_SpecMap (sourceScheme : Scheme.{u}) (sectionValue : Γ(sourceScheme, ⊤)) :
    sourceScheme.toSpecΓ.resLE (PrimeSpectrum.basicOpen sectionValue) (sourceScheme.basicOpen sectionValue)
        (sourceScheme.toSpecΓ_preimage_basicOpen sectionValue).ge ≫ (basicOpenIsoSpecAway sectionValue).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(sourceScheme, ⊤) (Localization.Away sectionValue))) =
      (sourceScheme.basicOpen sectionValue).ι ≫ sourceScheme.toSpecΓ := by
  rw [basicOpenIsoSpecAway_hom_SpecMap, Scheme.Hom.resLE_comp_ι]

namespace Proj

variable {gradedPieceType gradedRing : Type u} [CommRing gradedRing]
    [SetLike gradedPieceType gradedRing] [AddSubgroupClass gradedPieceType gradedRing]
    (grading : ℕ → gradedPieceType) [GradedRing grading]
    {sourceScheme targetScheme : Scheme.{u}}

section fromOfGlobalSections

/-- The morphism `sourceScheme ⟶ Proj grading` induced by `sectionMap : gradedRing →+* Γ(sourceScheme, ⊤)` restricted to `D(sectionMap homogeneousElement)`
is `Proj.toBasicOpenOfGlobalSections`. -/
@[reassoc]
lemma ι_comp_fromOfGlobalSections (sectionMap : gradedRing →+* Γ(sourceScheme, ⊤))
    (hf : (HomogeneousIdeal.irrelevant grading).toIdeal.map sectionMap = ⊤) {homogeneousElement : gradedRing} {formDegree : ℕ} (hn : 0 < formDegree)
    (hr : homogeneousElement ∈ grading formDegree) :
    (sourceScheme.basicOpen (sectionMap homogeneousElement)).ι ≫ fromOfGlobalSections grading sectionMap hf =
      toBasicOpenOfGlobalSections grading sectionMap rfl hn hr ≫ (basicOpen grading homogeneousElement).ι := by
  rw [← Scheme.Hom.resLE_comp_ι (fromOfGlobalSections grading sectionMap hf)
    (fromOfGlobalSections_preimage_basicOpen grading sectionMap hf hn hr).ge,
    fromOfGlobalSections_resLE]

section naturality

variable (sourceMap : targetScheme ⟶ sourceScheme) (sectionMap : gradedRing →+* Γ(sourceScheme, ⊤))

/-- If the image of the irrelevant ideal under `sectionMap : gradedRing →+* Γ(sourceScheme, ⊤)` generates the unit ideal,
the same holds after composing with the restriction along a morphism of schemes. -/
lemma map_irrelevant_comp_appTop_eq_top
    (hf : (HomogeneousIdeal.irrelevant grading).toIdeal.map sectionMap = ⊤) :
    (HomogeneousIdeal.irrelevant grading).toIdeal.map (sourceMap.appTop.hom.comp sectionMap) = ⊤ := by
  rw [← Ideal.map_map, hf, Ideal.map_top]

/-- The basic open of `Γ(sourceMap) (sectionMap homogeneousElement)` in `targetScheme` is contained in (in fact equal to) the preimage of
the basic open of `sectionMap homogeneousElement` in `sourceScheme`. -/
private lemma basicOpen_comp_appTop_le_preimage (homogeneousElement : gradedRing) :
    targetScheme.basicOpen ((sourceMap.appTop.hom.comp sectionMap) homogeneousElement) ≤ sourceMap ⁻¹ᵁ sourceScheme.basicOpen (sectionMap homogeneousElement) :=
  (Scheme.preimage_basicOpen_top sourceMap (sectionMap homogeneousElement)).ge

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of `Proj.toBasicOpenOfGlobalSections` in the source scheme, after identifying
`D₊(denominator)` with `Spec (A_t)₀`. -/
@[reassoc]
private lemma resLE_toSpecΓ_comp_SpecMap_map (denominator : gradedRing) :
    sourceMap.resLE (sourceScheme.basicOpen (sectionMap denominator)) (targetScheme.basicOpen ((sourceMap.appTop.hom.comp sectionMap) denominator))
        (basicOpen_comp_appTop_le_preimage sourceMap sectionMap denominator) ≫
      (sourceScheme.toSpecΓ.resLE (PrimeSpectrum.basicOpen (sectionMap denominator)) (sourceScheme.basicOpen (sectionMap denominator))
          (sourceScheme.toSpecΓ_preimage_basicOpen (sectionMap denominator)).ge ≫
        (basicOpenIsoSpecAway (sectionMap denominator)).hom ≫
          Spec.map (CommRingCat.ofHom
            (IsLocalization.map (S := Localization.Away denominator) (T := Submonoid.powers (sectionMap denominator))
              (Localization.Away (sectionMap denominator)) sectionMap
              (Submonoid.powers_le.mpr (Submonoid.mem_powers _))))) =
      targetScheme.toSpecΓ.resLE (PrimeSpectrum.basicOpen ((sourceMap.appTop.hom.comp sectionMap) denominator))
          (targetScheme.basicOpen ((sourceMap.appTop.hom.comp sectionMap) denominator))
          (targetScheme.toSpecΓ_preimage_basicOpen _).ge ≫
        (basicOpenIsoSpecAway ((sourceMap.appTop.hom.comp sectionMap) denominator)).hom ≫
          Spec.map (CommRingCat.ofHom (IsLocalization.map (S := Localization.Away denominator)
            (T := Submonoid.powers ((sourceMap.appTop.hom.comp sectionMap) denominator))
            (Localization.Away ((sourceMap.appTop.hom.comp sectionMap) denominator)) (sourceMap.appTop.hom.comp sectionMap)
            (Submonoid.powers_le.mpr (Submonoid.mem_powers _)))) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap gradedRing (Localization.Away denominator))))]
  have e1 : ∀ {coordinateRing : Type u} [CommRing coordinateRing] (ringMap : gradedRing →+* coordinateRing) (homogeneousElement : coordinateRing)
      (compatibility : Submonoid.powers denominator ≤ (Submonoid.powers homogeneousElement).comap ringMap),
      Spec.map (CommRingCat.ofHom
          (IsLocalization.map (S := Localization.Away denominator) (Localization.Away homogeneousElement) ringMap compatibility)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap gradedRing (Localization.Away denominator))) =
      Spec.map (CommRingCat.ofHom (algebraMap coordinateRing (Localization.Away homogeneousElement))) ≫
        Spec.map (CommRingCat.ofHom ringMap) := by
    intro coordinateRing _ ringMap homogeneousElement compatibility
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact IsLocalization.map_comp _
  simp only [Category.assoc, e1, resLE_toSpecΓ_basicOpenIsoSpecAway_hom_SpecMap_assoc,
    Scheme.Hom.resLE_comp_ι_assoc, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom,
    ← Scheme.toSpecΓ_naturality_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of `Proj.toBasicOpenOfGlobalSections` in the source scheme. -/
@[reassoc]
lemma resLE_toBasicOpenOfGlobalSections {denominator : gradedRing} {degree : ℕ} (h0d : 0 < degree) (hd : denominator ∈ grading degree) :
    sourceMap.resLE (sourceScheme.basicOpen (sectionMap denominator)) (targetScheme.basicOpen ((sourceMap.appTop.hom.comp sectionMap) denominator))
        (basicOpen_comp_appTop_le_preimage sourceMap sectionMap denominator) ≫
      toBasicOpenOfGlobalSections grading sectionMap rfl h0d hd =
      toBasicOpenOfGlobalSections grading (sourceMap.appTop.hom.comp sectionMap) rfl h0d hd := by
  rw [← cancel_mono (basicOpenIsoSpec grading denominator hd h0d).hom, Category.assoc,
    toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom grading sectionMap rfl h0d hd
      (Submonoid.powers_le.mpr (Submonoid.mem_powers _)),
    toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom grading (sourceMap.appTop.hom.comp sectionMap) rfl h0d hd
      (Submonoid.powers_le.mpr (Submonoid.mem_powers _)),
    CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_comp, Spec.map_comp,
    resLE_toSpecΓ_comp_SpecMap_map_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- The morphism `sourceScheme ⟶ Proj grading` induced by element ring homomorphism `sectionMap : gradedRing →+* Γ(sourceScheme, ⊤)` is natural
in `sourceScheme`: precomposing with `sourceMap : targetScheme ⟶ sourceScheme` gives the morphism induced by `Γ(sourceMap) ∘ sectionMap`. -/
@[reassoc]
lemma comp_fromOfGlobalSections
    (hf : (HomogeneousIdeal.irrelevant grading).toIdeal.map sectionMap = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant grading).toIdeal.map (sourceMap.appTop.hom.comp sectionMap) = ⊤) :
    sourceMap ≫ fromOfGlobalSections grading sectionMap hf =
      fromOfGlobalSections grading (sourceMap.appTop.hom.comp sectionMap) hf' := by
  refine (openCoverOfMapIrrelevantEqTop grading (sourceMap.appTop.hom.comp sectionMap) hf').hom_ext _ _ fun formDegree ↦ ?_
  obtain ⟨formDegree, homogeneousElement, hn, hr⟩ := formDegree
  have key : (targetScheme.basicOpen ((sourceMap.appTop.hom.comp sectionMap) homogeneousElement)).ι ≫ sourceMap ≫ fromOfGlobalSections grading sectionMap hf =
      toBasicOpenOfGlobalSections grading (sourceMap.appTop.hom.comp sectionMap) rfl hn hr ≫ (basicOpen grading homogeneousElement).ι := by
    rw [← Category.assoc,
      ← Scheme.Hom.resLE_comp_ι sourceMap (basicOpen_comp_appTop_le_preimage sourceMap sectionMap homogeneousElement),
      Category.assoc, ι_comp_fromOfGlobalSections grading sectionMap hf hn hr,
      resLE_toBasicOpenOfGlobalSections_assoc]
  exact key.trans (ι_comp_fromOfGlobalSections grading (sourceMap.appTop.hom.comp sectionMap) hf' hn hr).symm

end naturality

section unitPowMul

set_option backward.isDefEq.respectTransparency.types false in
/-- Rescaling `sectionMap` in degree `formDegree` by the `formDegree`-th power of a unit does not change
`Proj.toBasicOpenOfGlobalSections`. -/
lemma toBasicOpenOfGlobalSections_eq_of_unit_pow_mul (unitValue : Γ(sourceScheme, ⊤)ˣ) (sectionMap otherSectionMap : gradedRing →+* Γ(sourceScheme, ⊤))
    (hff' : ∀ (formDegree : ℕ) (element : gradedRing), element ∈ grading formDegree → otherSectionMap element = (unitValue : Γ(sourceScheme, ⊤)) ^ formDegree * sectionMap element)
    {denominator : gradedRing} {degree : ℕ} (h0d : 0 < degree) (hd : denominator ∈ grading degree)
    (hbo : sourceScheme.basicOpen (sectionMap denominator) = sourceScheme.basicOpen (otherSectionMap denominator)) :
    toBasicOpenOfGlobalSections grading sectionMap rfl h0d hd =
      sourceScheme.homOfLE hbo.le ≫ toBasicOpenOfGlobalSections grading otherSectionMap rfl h0d hd := by
  have hft : otherSectionMap denominator = (unitValue : Γ(sourceScheme, ⊤)) ^ degree * sectionMap denominator := hff' degree denominator hd
  have hunit : ∀ elementValue : Submonoid.powers (otherSectionMap denominator),
      IsUnit (algebraMap Γ(sourceScheme, ⊤) (Localization.Away (sectionMap denominator)) (elementValue : Γ(sourceScheme, ⊤))) := by
    rintro ⟨elementValue, exponent, rfl⟩
    change IsUnit (algebraMap Γ(sourceScheme, ⊤) (Localization.Away (sectionMap denominator)) (otherSectionMap denominator ^ exponent))
    rw [hft, mul_pow, map_mul]
    exact (((unitValue.isUnit.pow degree).pow exponent).map _).mul
      (IsLocalization.map_units _ (⟨sectionMap denominator ^ exponent, exponent, rfl⟩ : Submonoid.powers (sectionMap denominator)))
  set localizationMap : Localization.Away (otherSectionMap denominator) →+* Localization.Away (sectionMap denominator) :=
    IsLocalization.lift (M := Submonoid.powers (otherSectionMap denominator)) hunit with hε
  have ha : sourceScheme.homOfLE hbo.le ≫ sourceScheme.toSpecΓ.resLE (PrimeSpectrum.basicOpen (otherSectionMap denominator))
        (sourceScheme.basicOpen (otherSectionMap denominator)) (sourceScheme.toSpecΓ_preimage_basicOpen (otherSectionMap denominator)).ge ≫
        (basicOpenIsoSpecAway (otherSectionMap denominator)).hom =
      sourceScheme.toSpecΓ.resLE (PrimeSpectrum.basicOpen (sectionMap denominator)) (sourceScheme.basicOpen (sectionMap denominator))
          (sourceScheme.toSpecΓ_preimage_basicOpen (sectionMap denominator)).ge ≫
        (basicOpenIsoSpecAway (sectionMap denominator)).hom ≫ Spec.map (CommRingCat.ofHom localizationMap) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(sourceScheme, ⊤) (Localization.Away (otherSectionMap denominator)))))]
    simp only [Category.assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hε, IsLocalization.lift_comp,
      resLE_toSpecΓ_basicOpenIsoSpecAway_hom_SpecMap,
      resLE_toSpecΓ_basicOpenIsoSpecAway_hom_SpecMap, Scheme.homOfLE_ι_assoc]
  have hb : localizationMap.comp ((IsLocalization.map (S := Localization.Away denominator)
        (T := Submonoid.powers (otherSectionMap denominator)) (Localization.Away (otherSectionMap denominator)) otherSectionMap
        (Submonoid.powers_le.mpr (Submonoid.mem_powers _))).comp
        (algebraMap (Away grading denominator) (Localization.Away denominator))) =
      (IsLocalization.map (S := Localization.Away denominator) (T := Submonoid.powers (sectionMap denominator))
        (Localization.Away (sectionMap denominator)) sectionMap
        (Submonoid.powers_le.mpr (Submonoid.mem_powers _))).comp
        (algebraMap (Away grading denominator) (Localization.Away denominator)) := by
    ext fraction
    obtain ⟨exponent, element, hak, rfl⟩ := HomogeneousLocalization.Away.mk_surjective grading hd fraction
    have hval : algebraMap (Away grading denominator) (Localization.Away denominator)
        (HomogeneousLocalization.Away.mk grading hd exponent element hak) =
        IsLocalization.mk' (Localization.Away denominator) element
          (⟨denominator ^ exponent, exponent, rfl⟩ : Submonoid.powers denominator) := by
      rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
        Localization.mk_eq_mk']
    simp only [RingHom.coe_comp, Function.comp_apply, hval, IsLocalization.map_mk', hε,
      IsLocalization.lift_mk'_spec]
    rw [hff' _ _ hak, hff' _ _ (SetLike.pow_mem_graded exponent hd), map_mul, map_mul, mul_assoc,
      IsLocalization.mk'_spec'_mk]
  rw [← cancel_mono (basicOpenIsoSpec grading denominator hd h0d).hom, Category.assoc,
    toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom grading sectionMap rfl h0d hd
      (Submonoid.powers_le.mpr (Submonoid.mem_powers _)),
    toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom grading otherSectionMap rfl h0d hd
      (Submonoid.powers_le.mpr (Submonoid.mem_powers _)),
    reassoc_of% ha, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hb]

/-- Rescaling `sectionMap` in degree `formDegree` by the `formDegree`-th power of element unit of `Γ(sourceScheme, ⊤)` does not change the
induced morphism `sourceScheme ⟶ Proj grading`. -/
lemma fromOfGlobalSections_eq_of_unit_pow_mul (unitValue : Γ(sourceScheme, ⊤)ˣ) (sectionMap otherSectionMap : gradedRing →+* Γ(sourceScheme, ⊤))
    (hff' : ∀ (formDegree : ℕ) (element : gradedRing), element ∈ grading formDegree → otherSectionMap element = (unitValue : Γ(sourceScheme, ⊤)) ^ formDegree * sectionMap element)
    (hf : (HomogeneousIdeal.irrelevant grading).toIdeal.map sectionMap = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant grading).toIdeal.map otherSectionMap = ⊤) :
    fromOfGlobalSections grading sectionMap hf = fromOfGlobalSections grading otherSectionMap hf' := by
  refine (openCoverOfMapIrrelevantEqTop grading sectionMap hf).hom_ext _ _ fun formDegree ↦ ?_
  obtain ⟨formDegree, homogeneousElement, hn, hr⟩ := formDegree
  have hbo : sourceScheme.basicOpen (sectionMap homogeneousElement) = sourceScheme.basicOpen (otherSectionMap homogeneousElement) := by
    rw [hff' formDegree homogeneousElement hr, Scheme.basicOpen_mul,
      Scheme.basicOpen_of_isUnit _ ((unitValue.isUnit.pow formDegree : IsUnit ((unitValue : Γ(sourceScheme, ⊤)) ^ formDegree))), top_inf_eq]
  simp only [openCoverOfMapIrrelevantEqTop, Scheme.openCoverOfIsOpenCover_f]
  rw [ι_comp_fromOfGlobalSections grading sectionMap hf hn hr,
    toBasicOpenOfGlobalSections_eq_of_unit_pow_mul grading unitValue sectionMap otherSectionMap hff' hn hr hbo, Category.assoc,
    ← ι_comp_fromOfGlobalSections grading otherSectionMap hf' hn hr, Scheme.homOfLE_ι_assoc]

end unitPowMul

end fromOfGlobalSections

section Cocycle

variable {degree : ℕ} (hd : 0 < degree) {firstDenominator secondDenominator : gradedRing} (first_homogeneous : firstDenominator ∈ grading degree) (second_homogeneous : secondDenominator ∈ grading degree) {sourceScheme : Scheme.{u}}
  (firstMap : sourceScheme ⟶ Spec (.of <| Away grading firstDenominator)) (secondMap : sourceScheme ⟶ Spec (.of <| Away grading secondDenominator))
  (compatibility : firstMap ≫ awayι grading firstDenominator first_homogeneous hd = secondMap ≫ awayι grading secondDenominator second_homogeneous hd)

include compatibility

/-- **The transition cocycle between two standard charts of `Proj grading`.** If a scheme `sourceScheme` maps
to the charts `Spec (A_f)₀` and `Spec (A_g)₀` compatibly over `Proj grading`, then the section
`numerator / secondDenominator` of the second chart pulls back to the product of the pullback of `numerator / firstDenominator` from the
first chart with the pullback of the transition function `firstDenominator / secondDenominator`. -/
lemma appTop_awayMk_eq_mul (hf' : firstDenominator ∈ grading (1 • degree)) (numerator : gradedRing) (hx : numerator ∈ grading (1 • degree)) :
    ((Scheme.ΓSpecIso _).inv ≫ secondMap.appTop).hom (Away.mk grading second_homogeneous 1 numerator hx) =
      ((Scheme.ΓSpecIso _).inv ≫ firstMap.appTop).hom (Away.mk grading first_homogeneous 1 numerator hx) *
        ((Scheme.ΓSpecIso _).inv ≫ secondMap.appTop).hom (Away.mk grading second_homogeneous 1 firstDenominator hf') := by
  set overlapMap : sourceScheme ⟶ Spec (.of <| Away grading (firstDenominator * secondDenominator)) :=
    Limits.pullback.lift firstMap secondMap compatibility ≫ (pullbackAwayιIso grading first_homogeneous hd second_homogeneous hd rfl).hom with hw
  have key : ∀ {coordinateRing : CommRingCat.{u}} (ringMap : coordinateRing ⟶ .of (Away grading (firstDenominator * secondDenominator))) (chartMap : sourceScheme ⟶ Spec coordinateRing),
      overlapMap ≫ Spec.map ringMap = chartMap → ∀ coordinateValue, ((Scheme.ΓSpecIso coordinateRing).inv ≫ chartMap.appTop).hom coordinateValue =
        ((Scheme.ΓSpecIso _).inv ≫ overlapMap.appTop).hom (ringMap.hom coordinateValue) := by
    rintro coordinateRing ringMap chartMap rfl coordinateValue
    have hφ : (Scheme.ΓSpecIso coordinateRing).inv ≫ (overlapMap ≫ Spec.map ringMap).appTop =
        ringMap ≫ (Scheme.ΓSpecIso _).inv ≫ overlapMap.appTop := by
      rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
        Category.assoc]
    rw [hφ]
    rfl
  have ha := key (CommRingCat.ofHom (awayMap grading second_homogeneous rfl)) firstMap <| by
    rw [hw, Category.assoc, pullbackAwayιIso_hom_SpecMap_awayMap_left, Limits.pullback.lift_fst]
  have hb := key (CommRingCat.ofHom (awayMap grading first_homogeneous (mul_comm firstDenominator secondDenominator))) secondMap <| by
    rw [hw, Category.assoc, pullbackAwayιIso_hom_SpecMap_awayMap_right, Limits.pullback.lift_snd]
  rw [hb _, hb _, ha _, ← map_mul]
  exact congrArg _ (awayMap_mk_one_eq_mul grading first_homogeneous second_homogeneous hx)

/-- The transition function `firstDenominator / secondDenominator` between two standard charts of `Proj grading` becomes a unit on
any scheme mapping to both charts compatibly over `Proj grading`. -/
lemma isUnit_appTop_awayMk (hf' : firstDenominator ∈ grading (1 • degree)) (hg' : secondDenominator ∈ grading (1 • degree)) :
    IsUnit (((Scheme.ΓSpecIso _).inv ≫ secondMap.appTop).hom (Away.mk grading second_homogeneous 1 firstDenominator hf')) := by
  have selfRatio : Away.mk grading second_homogeneous 1 secondDenominator hg' = 1 := by
    apply val_injective
    rw [Away.val_mk, val_one]
    simpa only [pow_one] using Localization.mk_self
      (⟨secondDenominator ^ 1, 1, rfl⟩ : Submonoid.powers secondDenominator)
  have h1 : ((Scheme.ΓSpecIso _).inv ≫ secondMap.appTop).hom (Away.mk grading second_homogeneous 1 firstDenominator hf') *
      ((Scheme.ΓSpecIso _).inv ≫ firstMap.appTop).hom (Away.mk grading first_homogeneous 1 secondDenominator hg') = 1 := by
    rw [mul_comm, ← appTop_awayMk_eq_mul grading hd first_homogeneous second_homogeneous firstMap secondMap compatibility hf' secondDenominator hg']
    simp [selfRatio]
  exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end Cocycle

set_option backward.isDefEq.respectTransparency.types false in
/-- **A criterion for a morphism into `Proj grading` to factor as a closed immersion into an affine
chart.** If `sourceScheme` is affine and the homogeneous element `denominator` of positive degree pulls back to `1`
under `sectionMap : gradedRing →+* Γ(sourceScheme, ⊤)`, the morphism `sourceScheme ⟶ Proj grading` attached to `sectionMap` factors through
`Spec (A_t)₀`, and the factorization is a closed immersion as soon as `Γ(sourceScheme, ⊤)` is generated as
a ring by the images under `sectionMap` of the homogeneous elements of degree a multiple of `deg denominator`. -/
theorem exists_isClosedImmersion_of_fromOfGlobalSections {sourceScheme : Scheme.{u}} [IsAffine sourceScheme]
    (sectionMap : gradedRing →+* Γ(sourceScheme, ⊤)) (hf : (HomogeneousIdeal.irrelevant grading).toIdeal.map sectionMap = ⊤)
    {denominator : gradedRing} {degree : ℕ} (h0d : 0 < degree) (hd : denominator ∈ grading degree) (ht : sectionMap denominator = 1)
    (hgen : Subring.closure {fraction : Γ(sourceScheme, ⊤) | ∃ exponent : ℕ, ∃ element ∈ grading (exponent • degree), sectionMap element = fraction} = ⊤) :
    ∃ chartMap : sourceScheme ⟶ Spec (.of (Away grading denominator)), IsClosedImmersion chartMap ∧
      chartMap ≫ awayι grading denominator hd h0d = fromOfGlobalSections grading sectionMap hf := by
  have hbo : sourceScheme.basicOpen (sectionMap denominator) = ⊤ := by rw [ht]; exact sourceScheme.basicOpen_one
  have hι : IsIso (sourceScheme.basicOpen (sectionMap denominator)).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ ((Scheme.Opens.opensRange_ι _).trans hbo)
  have hxle : Submonoid.powers denominator ≤ (Submonoid.powers (sectionMap denominator)).comap sectionMap :=
    Submonoid.powers_le.mpr (Submonoid.mem_powers _)
  set coordinateMap : Away grading denominator →+* Localization.Away (sectionMap denominator) :=
    (IsLocalization.map (S := Localization.Away denominator) (Localization.Away (sectionMap denominator)) sectionMap hxle).comp
      (algebraMap (Away grading denominator) (Localization.Away denominator)) with hΘdef
  have hu : IsUnit (sectionMap denominator) := ht ▸ isUnit_one
  have hbij : Function.Bijective (algebraMap Γ(sourceScheme, ⊤) (Localization.Away (sectionMap denominator))) := by
    have hle : Submonoid.powers (sectionMap denominator) ≤ IsUnit.submonoid Γ(sourceScheme, ⊤) := by
      rintro _ ⟨exponent, rfl⟩
      exact hu.pow exponent
    exact (IsLocalization.atUnits Γ(sourceScheme, ⊤) (Submonoid.powers (sectionMap denominator))
      (S := Localization.Away (sectionMap denominator)) hle).bijective
  have hisoalg : IsIso (CommRingCat.ofHom (algebraMap Γ(sourceScheme, ⊤) (Localization.Away (sectionMap denominator)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have hcomp : IsIso (sourceScheme.toSpecAway (sectionMap denominator) ≫ Spec.map (CommRingCat.ofHom
      (algebraMap Γ(sourceScheme, ⊤) (Localization.Away (sectionMap denominator))))) := by
    rw [Scheme.toSpecAway_SpecMap_algebraMap]
    infer_instance
  have hisoaway : IsIso (sourceScheme.toSpecAway (sectionMap denominator)) :=
    IsIso.of_isIso_comp_right (sourceScheme.toSpecAway (sectionMap denominator)) (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(sourceScheme, ⊤) (Localization.Away (sectionMap denominator)))))
  have hΘmk : ∀ (exponent : ℕ) (element : gradedRing) (ha : element ∈ grading (exponent • degree)),
      coordinateMap (Away.mk grading hd exponent element ha) = algebraMap Γ(sourceScheme, ⊤) (Localization.Away (sectionMap denominator)) (sectionMap element) := by
    intro exponent element ha
    rw [hΘdef, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
      IsLocalization.mk'_eq_iff_eq_mul]
    simp [ht]
  have hΘsurj : Function.Surjective coordinateMap := by
    intro fraction
    obtain ⟨preimageElement, rfl⟩ := hbij.2 fraction
    have hmem : preimageElement ∈ Subring.comap (algebraMap Γ(sourceScheme, ⊤) (Localization.Away (sectionMap denominator))) coordinateMap.range := by
      refine Subring.closure_le.mpr ?_ (hgen ▸ Subring.mem_top preimageElement)
      rintro _ ⟨exponent, element, ha, rfl⟩
      exact ⟨Away.mk grading hd exponent element ha, hΘmk exponent element ha⟩
    exact hmem
  refine ⟨inv (sourceScheme.basicOpen (sectionMap denominator)).ι ≫ sourceScheme.toSpecAway (sectionMap denominator) ≫
    Spec.map (CommRingCat.ofHom coordinateMap), ?_, ?_⟩
  · have : IsClosedImmersion (Spec.map (CommRingCat.ofHom coordinateMap)) :=
      IsClosedImmersion.spec_of_surjective _ hΘsurj
    infer_instance
  · have key : sourceScheme.toSpecAway (sectionMap denominator) ≫ Spec.map (CommRingCat.ofHom coordinateMap) =
        toBasicOpenOfGlobalSections grading sectionMap rfl h0d hd ≫ (basicOpenIsoSpec grading denominator hd h0d).hom := by
      rw [toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom grading sectionMap rfl h0d hd hxle,
        Scheme.toSpecAway, Category.assoc]
    have hbi : (basicOpenIsoSpec grading denominator hd h0d).hom ≫ awayι grading denominator hd h0d = (basicOpen grading denominator).ι := by
      rw [← basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
    rw [key, Category.assoc, Category.assoc, hbi,
      ← ι_comp_fromOfGlobalSections grading sectionMap hf h0d hd, IsIso.inv_hom_id_assoc]

end Proj

end AlgebraicGeometry
