import Jacobian.AlgebraicGeometry.ProjectiveSpace.SectionsNaturality
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Charts
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Twist
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
import Jacobian.AlgebraicGeometry.Modules.HomSection
import Jacobian.AlgebraicGeometry.Modules.RestrictionIsomorphism
import Jacobian.AlgebraicGeometry.Modules.TensorSection
import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Gluing
import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Hom
import Jacobian.AlgebraicGeometry.Scheme.GluingMorphisms

/-!
# Projective morphisms from generators of an invertible module

A family of global sections which freely generates a module on an open cover
constructs a morphism to projective space and identifies the pullback of
`𝒪(1)` with that module. The construction glues the affine coordinate ratios.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

namespace Proj

section ChartSections

variable {gradedPieces gradedRing : Type u} [CommRing gradedRing]
  [SetLike gradedPieces gradedRing] [AddSubgroupClass gradedPieces gradedRing]
  (grading : ℕ → gradedPieces) [GradedRing grading]

/-- The affine chart of Proj pulls its localized coordinate sections back to the corresponding
fractions. -/
private lemma awayToSection_awayι_appLE {denominator : gradedRing} {degree : ℕ} (hd : denominator ∈
  grading degree) (h0d : 0 < degree) :
    awayToSection grading denominator ≫ (awayι grading denominator hd h0d).appLE (basicOpen grading
      denominator) ⊤
      (by rw [← opensRange_awayι grading denominator hd h0d]; exact (Scheme.Hom.preimage_opensRange
        _).ge) =
      (Scheme.ΓSpecIso _).inv := by
  have key : (basicOpenIsoSpec grading denominator hd h0d).hom.app ⊤ = (Scheme.ΓSpecIso _).hom ≫
      awayToSection grading denominator ≫ (basicOpen grading denominator).topIso.inv := by
    rw [basicOpenIsoSpec_hom]
    exact basicOpenToSpec_app_top grading denominator
  have hι : (basicOpenIsoSpec grading denominator hd h0d).hom ≫ awayι grading denominator hd h0d =
    (basicOpen grading denominator).ι := by
    rw [← basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have hcongr : ∀ {sectionMap otherMap : (basicOpen grading denominator).toScheme ⟶ Proj grading}
    (equality : sectionMap = otherMap) (targetScheme) (exponent),
      sectionMap.appLE (basicOpen grading denominator) targetScheme exponent = otherMap.appLE
        (basicOpen grading denominator) targetScheme (equality ▸ exponent) := by
    rintro sectionMap otherMap rfl targetScheme exponent
    rfl
  rw [← cancel_mono ((basicOpenIsoSpec grading denominator hd h0d).hom.appTop), Category.assoc,
    Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, hcongr hι,
    ← Scheme.Hom.app_eq_appLE, key, Iso.inv_hom_id_assoc]
  congr 1

/-- Pullback through an affine chart of Proj evaluates localized sections by the chart map. -/
private lemma comp_awayι_appLE_awayToSection {targetScheme : Scheme.{u}} {denominator : gradedRing}
  {degree : ℕ} (hd : denominator ∈ grading degree)
    (h0d : 0 < degree) (numerator : targetScheme ⟶ Spec (.of (Away grading denominator))) (exponent)
      (fraction : Away grading denominator) :
    (numerator ≫ awayι grading denominator hd h0d).appLE (basicOpen grading denominator) ⊤ exponent
      (awayToSection grading denominator fraction) =
      ((Scheme.ΓSpecIso _).inv ≫ numerator.appTop) fraction := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, ← awayToSection_awayι_appLE grading hd h0d,
    Category.assoc, Scheme.Hom.appLE_comp_appLE]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- If a positive-degree homogeneous element maps to one, the induced morphism to Proj factors
through its affine chart, with the prescribed action on fractions. -/
private lemma exists_comp_awayι_eq_fromOfGlobalSections {sourceScheme : Scheme.{u}} (sectionMap :
  gradedRing →+* Γ(sourceScheme, ⊤))
    (hf : (HomogeneousIdeal.irrelevant grading).toIdeal.map sectionMap = ⊤) {denominator :
      gradedRing} {degree : ℕ} (h0d : 0 < degree)
    (hd : denominator ∈ grading degree) (ht : sectionMap denominator = 1) :
    ∃ chartMap : sourceScheme ⟶ Spec (.of (Away grading denominator)), chartMap ≫ awayι grading
      denominator hd h0d = fromOfGlobalSections grading sectionMap hf ∧
      ∀ (exponent : ℕ) (numerator : gradedRing) (ha : numerator ∈ grading (exponent • degree)),
        ((Scheme.ΓSpecIso _).inv ≫ chartMap.appTop) (Away.mk grading hd exponent numerator ha) =
          sectionMap numerator := by
  have hbo : sourceScheme.basicOpen (sectionMap denominator) = ⊤ := by rw [ht]; exact
    sourceScheme.basicOpen_one
  have hι : IsIso (sourceScheme.basicOpen (sectionMap denominator)).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ ((Scheme.Opens.opensRange_ι _).trans hbo)
  have hxle : Submonoid.powers denominator ≤ (Submonoid.powers (sectionMap denominator)).comap
    sectionMap :=
    Submonoid.powers_le.mpr (Submonoid.mem_powers _)
  set localizationMap : Away grading denominator →+* Localization.Away (sectionMap denominator) :=
    (IsLocalization.map (S := Localization.Away denominator) (Localization.Away (sectionMap
      denominator)) sectionMap hxle).comp
      (algebraMap (Away grading denominator) (Localization.Away denominator)) with hΘdef
  have hΘmk : ∀ (exponent : ℕ) (numerator : gradedRing) (ha : numerator ∈ grading (exponent •
    degree)),
      localizationMap (Away.mk grading hd exponent numerator ha) = algebraMap Γ(sourceScheme, ⊤)
        (Localization.Away (sectionMap denominator)) (sectionMap numerator) := by
    intro exponent numerator ha
    rw [hΘdef, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
      IsLocalization.mk'_eq_iff_eq_mul]
    simp [ht]
  refine ⟨inv (sourceScheme.basicOpen (sectionMap denominator)).ι ≫ sourceScheme.toSpecAway
    (sectionMap denominator) ≫
    Spec.map (CommRingCat.ofHom localizationMap), ?_, fun exponent numerator ha ↦ ?_⟩
  · have key : sourceScheme.toSpecAway (sectionMap denominator) ≫ Spec.map (CommRingCat.ofHom
    localizationMap) =
        toBasicOpenOfGlobalSections grading sectionMap rfl h0d hd ≫ (basicOpenIsoSpec grading
          denominator hd h0d).hom := by
      rw [toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom grading sectionMap rfl h0d hd hxle,
        Scheme.toSpecAway, Category.assoc]
    have hbi : (basicOpenIsoSpec grading denominator hd h0d).hom ≫ awayι grading denominator hd h0d
      = (basicOpen grading denominator).ι := by
      rw [← basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
    rw [Category.assoc, key, Category.assoc, hbi,
      ← ι_comp_fromOfGlobalSections grading sectionMap hf h0d hd, IsIso.inv_hom_id_assoc]
  · have e1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom localizationMap)
    have e2 := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap Γ(sourceScheme, ⊤) (Localization.Away (sectionMap
        denominator))))
    have e3 : inv (sourceScheme.basicOpen (sectionMap denominator)).ι ≫ sourceScheme.toSpecAway
      (sectionMap denominator) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(sourceScheme, ⊤) (Localization.Away (sectionMap
          denominator)))) =
        sourceScheme.toSpecΓ := by
      rw [Scheme.toSpecAway_SpecMap_algebraMap, IsIso.inv_hom_id_assoc]
    have e5 : CommRingCat.ofHom (algebraMap Γ(sourceScheme, ⊤) (Localization.Away (sectionMap
      denominator))) ≫
        (Scheme.ΓSpecIso _).inv ≫ (sourceScheme.toSpecAway (sectionMap denominator)).appTop ≫
          (inv (sourceScheme.basicOpen (sectionMap denominator)).ι).appTop = 𝟙 _ := by
      rw [reassoc_of% e2, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
        Category.assoc, e3, Scheme.toSpecΓ_appTop]
      exact (Scheme.ΓSpecIso Γ(sourceScheme, ⊤)).inv_hom_id
    simp only [Scheme.Hom.comp_appTop]
    rw [← Category.assoc, ← Category.assoc, ← e1, Category.assoc, Category.assoc,
      ConcreteCategory.comp_apply]
    erw [hΘmk]
    exact congrArg (fun sectionEndomorphism : Γ(sourceScheme, ⊤) ⟶ Γ(sourceScheme, ⊤) ↦
      sectionEndomorphism (sectionMap numerator)) e5

end ChartSections

end Proj

namespace ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

open Scheme.Modules

private lemma isFreeGenerator_of_restrict_iso {sourceScheme : Scheme.{u}}
    {moduleSheaf : sourceScheme.Modules} (moduleMap : Scheme.Modules.unit sourceScheme ⟶ moduleSheaf)
    {openSubset : sourceScheme.Opens} [IsIso ((restrictFunctor openSubset.ι).map moduleMap)] :
    IsFreeGenerator (moduleSheaf.presheaf.map
      (homOfLE (le_top : openSubset ≤ ⊤)).op
      (moduleMap.app ⊤ (Scheme.Modules.unitSectionsEquiv ⊤ (1 : Γ(sourceScheme, ⊤))))) := by
  intro smallerOpen inclusion
  have formula : (fun scalar : Γ(sourceScheme, smallerOpen) ↦
      scalar • moduleSheaf.presheaf.map (homOfLE inclusion).op
        (moduleSheaf.presheaf.map (homOfLE (le_top : openSubset ≤ ⊤)).op
          (moduleMap.app ⊤ (Scheme.Modules.unitSectionsEquiv ⊤ (1 : Γ(sourceScheme, ⊤)))))) =
      moduleMap.app smallerOpen := by
    funext scalar
    rw [presheaf_map_homOfLE_map_homOfLE]
    erw [← Hom.app_presheaf_map, ← Hom.app_smul]
    congr 1
    change scalar * sourceScheme.presheaf.map _ 1 = scalar
    rw [map_one, mul_one]
  rw [formula]
  exact bijective_app_of_isIso_restrict moduleMap inclusion

private lemma isIso_restrict_pullbackUnit_comp {sourceScheme targetScheme : Scheme.{u}}
    (baseMap : sourceScheme ⟶ targetScheme) {moduleSheaf : targetScheme.Modules}
    (moduleMap : Scheme.Modules.unit targetScheme ⟶ moduleSheaf) (openSubset : targetScheme.Opens)
    [IsIso ((restrictFunctor openSubset.ι).map moduleMap)] :
    IsIso ((restrictFunctor (baseMap ⁻¹ᵁ openSubset).ι).map
      ((pullbackObjUnitIso baseMap).inv ≫ (Scheme.Modules.pullback baseMap).map moduleMap)) := by
  have := isIso_restrict_pullback_map baseMap moduleMap openSubset
  have : IsIso ((restrictFunctor (baseMap ⁻¹ᵁ openSubset).ι).map
      (pullbackObjUnitIso baseMap).inv) :=
    ((restrictFunctor _).mapIso (pullbackObjUnitIso baseMap).symm).isIso_hom
  erw [Functor.map_comp]
  exact IsIso.comp_isIso

private lemma isFreeGenerator_pullbackSection_of_restrict_iso
    {sourceScheme targetScheme : Scheme.{u}} (baseMap : sourceScheme ⟶ targetScheme)
    {moduleSheaf : targetScheme.Modules} (moduleMap : Scheme.Modules.unit targetScheme ⟶ moduleSheaf)
    {openSubset : targetScheme.Opens} [IsIso ((restrictFunctor openSubset.ι).map moduleMap)] :
    IsFreeGenerator (((Scheme.Modules.pullback baseMap).obj moduleSheaf).presheaf.map
      (homOfLE (baseMap.preimage_mono (le_top : openSubset ≤ ⊤))).op
      (pullbackSection baseMap (moduleMap.app ⊤ (1 : Γ(targetScheme, ⊤))))) := by
  haveI : IsIso ((restrictFunctor (baseMap ⁻¹ᵁ openSubset).ι).map
      ((pullbackObjUnitIso baseMap).inv ≫ (Scheme.Modules.pullback baseMap).map moduleMap)) :=
    isIso_restrict_pullbackUnit_comp baseMap moduleMap openSubset
  rw [pullbackSection_app_one]
  exact isFreeGenerator_of_restrict_iso (sourceScheme := sourceScheme)
    (moduleSheaf := (Scheme.Modules.pullback baseMap).obj moduleSheaf)
    (openSubset := baseMap ⁻¹ᵁ openSubset)
    ((pullbackObjUnitIso baseMap).inv ≫ (Scheme.Modules.pullback baseMap).map moduleMap)

private lemma pullbackSection_map_eq_smul {sourceScheme targetScheme : Scheme.{u}}
    (baseMap : sourceScheme ⟶ targetScheme) {moduleSheaf : targetScheme.Modules}
    {largerOpen smallerOpen : targetScheme.Opens} (inclusion : smallerOpen ≤ largerOpen)
    {sectionValue otherSection : Γ(moduleSheaf, largerOpen)} {scalar : Γ(targetScheme, smallerOpen)}
    (relation : moduleSheaf.presheaf.map (homOfLE inclusion).op sectionValue =
      scalar • moduleSheaf.presheaf.map (homOfLE inclusion).op otherSection) :
    ((Scheme.Modules.pullback baseMap).obj moduleSheaf).presheaf.map
        (homOfLE (baseMap.preimage_mono inclusion)).op (pullbackSection baseMap sectionValue) =
      baseMap.app smallerOpen scalar • ((Scheme.Modules.pullback baseMap).obj moduleSheaf).presheaf.map
        (homOfLE (baseMap.preimage_mono inclusion)).op (pullbackSection baseMap otherSection) := by
  rw [← pullbackSection_map baseMap inclusion, ← pullbackSection_map baseMap inclusion,
    relation, pullbackSection_smul]

private lemma homOfLE_appTop_topIso_inv {sourceScheme : Scheme.{u}}
    {smallerOpen largerOpen : sourceScheme.Opens} (inclusion : smallerOpen ≤ largerOpen)
    (sectionValue : Γ(sourceScheme, largerOpen)) :
    (sourceScheme.homOfLE inclusion).appTop (largerOpen.topIso.inv sectionValue) =
      smallerOpen.topIso.inv (sourceScheme.presheaf.map (homOfLE inclusion).op sectionValue) := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
  change (sourceScheme.presheaf.map _ ≫ sourceScheme.presheaf.map _) sectionValue =
    (sourceScheme.presheaf.map _ ≫ sourceScheme.presheaf.map _) sectionValue
  rw [← Functor.map_comp]
  erw [← Functor.map_comp]
  rfl

section CoordinateSections

variable (coordinates : Type u) (baseScheme : Scheme.{u}) {sourceScheme : Scheme.{u}}

/-- The homogeneous coordinate section of `𝒪(1)` on relative projective space. -/
def twistOneSection (coordinate : coordinates) : Γ(twist coordinates baseScheme 1, ⊤) :=
  pullbackSection (toIntegralModel coordinates baseScheme)
    (Hom.app (Proj.unitToTwist (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinate)) ⊤
      (1 : Γ(Proj (homogeneousSubmodule coordinates (ULift.{u} ℤ)), ⊤)))

variable {coordinates baseScheme}

/-- The pullback of the global section `Tᵢ` of `𝒪(1)` along a morphism `baseMap : sourceScheme ⟶ ℙ(coordinates; baseScheme)` is a
free generator of `baseMap^* 𝒪(1)` over the preimage of the standard open `D₊(Tᵢ)`. -/
lemma isFreeGenerator_pullbackSection_twistOneSection (baseMap : sourceScheme ⟶ ℙ(coordinates;
  baseScheme)) (coordinate : coordinates) :
    IsFreeGenerator (((Scheme.Modules.pullback baseMap).obj (twist coordinates baseScheme
      1)).presheaf.map
      (homOfLE (baseMap.preimage_mono (le_top : toIntegralModel coordinates baseScheme ⁻¹ᵁ
        Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ)) (MvPolynomial.X coordinate)
          ≤ ⊤))).op
      (pullbackSection baseMap (twistOneSection coordinates baseScheme coordinate))) := by
  have := isIso_restrict_pullbackUnit_comp
    (toIntegralModel coordinates baseScheme)
    (Proj.unitToTwist (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinate))
    (Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ)) (MvPolynomial.X coordinate))
  have pullbackFormula := pullbackSection_app_one (toIntegralModel coordinates baseScheme)
    (Proj.unitToTwist (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinate))
  rw [twistOneSection]
  erw [pullbackFormula]
  exact isFreeGenerator_pullbackSection_of_restrict_iso _ _

/-- **The transition rule** `Tᵢ = (Tᵢ / Tⱼ) • Tⱼ` over `D₊(Tⱼ)`, pulled back along a morphism
`baseMap : sourceScheme ⟶ ℙ(coordinates; baseScheme)`. -/
lemma pullbackSection_twistOneSection_map_eq_smul (baseMap : sourceScheme ⟶ ℙ(coordinates;
  baseScheme)) (coordinate otherCoordinate : coordinates) :
    ((Scheme.Modules.pullback baseMap).obj (twist coordinates baseScheme 1)).presheaf.map
        (homOfLE (baseMap.preimage_mono (le_top : toIntegralModel coordinates baseScheme ⁻¹ᵁ
          Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ)) (MvPolynomial.X
            otherCoordinate) ≤ ⊤))).op
        (pullbackSection baseMap (twistOneSection coordinates baseScheme coordinate)) =
      baseMap.app (toIntegralModel coordinates baseScheme ⁻¹ᵁ
          Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ)) (MvPolynomial.X
            otherCoordinate))
        ((toIntegralModel coordinates baseScheme).app
          (Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ)) (MvPolynomial.X
            otherCoordinate))
          (Proj.awayToSection _ _ (awayXRatio (ULift.{u} ℤ) otherCoordinate coordinate))) •
        ((Scheme.Modules.pullback baseMap).obj (twist coordinates baseScheme 1)).presheaf.map
          (homOfLE (baseMap.preimage_mono (le_top : toIntegralModel coordinates baseScheme ⁻¹ᵁ
            Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ)) (MvPolynomial.X
              otherCoordinate) ≤ ⊤))).op
          (pullbackSection baseMap (twistOneSection coordinates baseScheme otherCoordinate)) := by
  have relation := Proj.map_unitToTwist_eq_smul
    (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinate)
    (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) otherCoordinate)
    (by simpa using X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinate)
  have pulledRelation := pullbackSection_map_eq_smul (toIntegralModel coordinates baseScheme) le_top
    relation
  exact pullbackSection_map_eq_smul baseMap _ pulledRelation

end CoordinateSections

private lemma appLE_eq_of_eq {sourceScheme targetScheme : Scheme.{u}} {firstMap structureMap :
  sourceScheme ⟶ targetScheme} (equality : firstMap = structureMap) (opens otherOpen inclusion) :
    firstMap.appLE opens otherOpen inclusion = structureMap.appLE opens otherOpen (equality ▸
      inclusion) := by
  subst equality
  rfl

/-- The ratio `Tⱼ / Tᵢ` on the standard open where the coordinate `Tᵢ` does not vanish. -/
def coordRatio (coordinates : Type u) (baseScheme : Scheme.{u}) (coordinate otherCoordinate :
  coordinates) : Γ(ℙ(coordinates; baseScheme), standardOpen coordinates baseScheme coordinate) :=
  (toIntegralModel coordinates baseScheme).app _ (Proj.awayToSection _ (MvPolynomial.X coordinate)
    (awayXRatio (ULift.{u} ℤ) coordinate otherCoordinate))

/-- If one coordinate section is one, pulling back the corresponding coordinate ratios recovers
the other sections. -/
lemma homOfSections_appLE_coordRatio {targetScheme baseScheme : Scheme.{u}} {coordinates : Type u}
    (structureMap : targetScheme ⟶ baseScheme) (sections : coordinates → Γ(targetScheme, ⊤))
    (generators : Ideal.span (Set.range sections) = ⊤) {coordinate : coordinates} (hsi : sections
      coordinate = 1) (otherCoordinate : coordinates) (inclusion) :
    (homOfSections structureMap sections generators).appLE (standardOpen coordinates baseScheme
      coordinate) ⊤ inclusion (coordRatio coordinates baseScheme coordinate otherCoordinate) =
      sections otherCoordinate := by
  obtain ⟨chartMap, hq, hq'⟩ := Proj.exists_comp_awayι_eq_fromOfGlobalSections _ (evalSections
    sections)
    (map_irrelevant_evalSections_eq_top sections generators) Nat.one_pos
    (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinate) (by rw [evalSections_X, hsi])
  have equality : homOfSections structureMap sections generators ≫ toIntegralModel coordinates
    baseScheme = chartMap ≫ Proj.awayι _ (MvPolynomial.X coordinate)
      (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinate) Nat.one_pos := by
    rw [homOfSections_toIntegralModel, hq]
  have h2 := Proj.comp_awayι_appLE_awayToSection _
    (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinate) Nat.one_pos chartMap (equality ▸
      inclusion)
    (awayXRatio (ULift.{u} ℤ) coordinate otherCoordinate)
  rw [← appLE_eq_of_eq equality, Scheme.Hom.comp_appLE] at h2
  refine h2.trans ((hq' 1 (MvPolynomial.X otherCoordinate) _).trans (evalSections_X sections
    otherCoordinate))

open Scheme.Modules

section Construction

variable {sourceScheme baseScheme : Scheme.{u}} {coordinates : Type u} {moduleSheaf :
  sourceScheme.Modules} (sections : coordinates → Γ(moduleSheaf, ⊤)) (opens : coordinates →
  sourceScheme.Opens)
  (generators : ∀ coordinate, IsFreeGenerator (moduleSheaf.presheaf.map (homOfLE (le_top : opens
    coordinate ≤ ⊤)).op (sections coordinate)))

/-- The coefficient of one global section relative to a chosen local free generator. -/
def sectionRatio (coordinate otherCoordinate : coordinates) : Γ(sourceScheme, opens coordinate) :=
  (generators coordinate).coeff (moduleSheaf.presheaf.map (homOfLE (le_top : opens coordinate ≤
    ⊤)).op (sections otherCoordinate))

lemma sectionRatio_smul (coordinate otherCoordinate : coordinates) :
    sectionRatio sections opens generators coordinate otherCoordinate • moduleSheaf.presheaf.map
      (homOfLE (le_top : opens coordinate ≤ ⊤)).op (sections coordinate) =
      moduleSheaf.presheaf.map (homOfLE (le_top : opens coordinate ≤ ⊤)).op (sections
        otherCoordinate) :=
  (generators coordinate).coeff_smul _

@[simp]
lemma sectionRatio_self (coordinate : coordinates) : sectionRatio sections opens generators
  coordinate coordinate = 1 :=
  ((generators coordinate).coeff_eq_iff _ 1).mpr (one_smul _ _)

/-- Restriction of a coordinate ratio expresses the restricted section in the chosen generator. -/
lemma sectionRatio_map_smul {openSubset : sourceScheme.Opens} (coordinate otherCoordinate :
  coordinates) (equality : openSubset ≤ opens coordinate) :
    sourceScheme.presheaf.map (homOfLE equality).op (sectionRatio sections opens generators
      coordinate otherCoordinate) •
        moduleSheaf.presheaf.map (homOfLE (le_top : openSubset ≤ ⊤)).op (sections coordinate) =
      moduleSheaf.presheaf.map (homOfLE (le_top : openSubset ≤ ⊤)).op (sections otherCoordinate) :=
        by
  have := presheaf_map_homOfLE_eq_smul (le_top : opens coordinate ≤ ⊤) equality (sectionRatio_smul
    sections opens generators coordinate otherCoordinate).symm
  exact this.symm

/-- Coordinate ratios satisfy the multiplicative cocycle relation on overlaps. -/
lemma sectionRatio_mul {openSubset : sourceScheme.Opens} (coordinate comparisonCoordinate
  otherCoordinate : coordinates) (hi : openSubset ≤ opens coordinate) (hl : openSubset ≤ opens
  comparisonCoordinate) :
    sourceScheme.presheaf.map (homOfLE hl).op (sectionRatio sections opens generators
      comparisonCoordinate coordinate) *
        sourceScheme.presheaf.map (homOfLE hi).op (sectionRatio sections opens generators coordinate
          otherCoordinate) =
      sourceScheme.presheaf.map (homOfLE hl).op (sectionRatio sections opens generators
        comparisonCoordinate otherCoordinate) := by
  refine ((generators comparisonCoordinate).map hl).smul_left_injective ?_
  simp only [presheaf_map_homOfLE_map_homOfLE]
  rw [sectionRatio_map_smul sections opens generators comparisonCoordinate otherCoordinate hl,
    mul_comm, mul_smul,
    sectionRatio_map_smul sections opens generators comparisonCoordinate coordinate hl,
      sectionRatio_map_smul sections opens generators coordinate otherCoordinate hi]

/-- The coordinate ratios, viewed as global functions on an open subscheme. -/
def localSections (coordinate : coordinates) : coordinates → Γ(opens coordinate, ⊤) := fun
  otherCoordinate ↦ (opens coordinate).topIso.inv (sectionRatio sections opens generators coordinate
  otherCoordinate)

lemma span_range_localSections (coordinate : coordinates) : Ideal.span (Set.range (localSections
  sections opens generators coordinate)) = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span ⟨coordinate, by simp [localSections]⟩)

variable (structureMap : sourceScheme ⟶ baseScheme)

/-- The projective morphism on an open subscheme defined by its coordinate ratios. -/
def localHom (coordinate : coordinates) : (opens coordinate).toScheme ⟶ ℙ(coordinates; baseScheme)
  :=
  homOfSections ((opens coordinate).ι ≫ structureMap) (localSections sections opens generators
    coordinate) (span_range_localSections sections opens generators coordinate)

lemma localHom_compat (coordinate comparisonCoordinate : coordinates) :
    sourceScheme.homOfLE (inf_le_left : opens coordinate ⊓ opens comparisonCoordinate ≤ opens
      coordinate) ≫ localHom sections opens generators structureMap coordinate =
      sourceScheme.homOfLE (inf_le_right : opens coordinate ⊓ opens comparisonCoordinate ≤ opens
        comparisonCoordinate) ≫ localHom sections opens generators structureMap comparisonCoordinate
        := by
  rw [localHom, localHom, comp_homOfSections, comp_homOfSections, sourceScheme.homOfLE_ι_assoc,
    sourceScheme.homOfLE_ι_assoc]
  have hu : IsUnit ((opens coordinate ⊓ opens comparisonCoordinate).topIso.inv
      (sourceScheme.presheaf.map (homOfLE inf_le_right).op (sectionRatio sections opens generators
        comparisonCoordinate coordinate))) := by
    refine IsUnit.of_mul_eq_one ((opens coordinate ⊓ opens comparisonCoordinate).topIso.inv
      (sourceScheme.presheaf.map (homOfLE inf_le_left).op (sectionRatio sections opens generators
        coordinate comparisonCoordinate))) ?_
    rw [← map_mul, sectionRatio_mul sections opens generators coordinate comparisonCoordinate
      comparisonCoordinate inf_le_left inf_le_right, sectionRatio_self,
      map_one, map_one]
  refine homOfSections_eq_of_unit_mul _ hu.unit _ _ fun otherCoordinate ↦ ?_
  simp only [localSections, homOfLE_appTop_topIso_inv, IsUnit.unit_spec, ← map_mul]
  rw [sectionRatio_mul sections opens generators coordinate comparisonCoordinate otherCoordinate
    inf_le_left inf_le_right]

variable (covers : ⨆ coordinate, opens coordinate = ⊤)

/-- Global sections which freely generate a module on an open cover define a morphism to
projective space over the base. -/
def homOfIsFreeGenerator : sourceScheme ⟶ ℙ(coordinates; baseScheme) :=
  Scheme.Opens.glueMorphismsOfTop opens covers (localHom sections opens generators structureMap)
    (localHom_compat sections opens generators structureMap)

@[reassoc]
lemma ι_homOfIsFreeGenerator (coordinate : coordinates) :
    (opens coordinate).ι ≫ homOfIsFreeGenerator sections opens generators structureMap covers =
      localHom sections opens generators structureMap coordinate :=
  Scheme.Opens.ι_glueMorphismsOfTop ..

@[reassoc (attr := simp)]
lemma homOfIsFreeGenerator_over : homOfIsFreeGenerator sections opens generators structureMap covers
  ≫ ℙ(coordinates; baseScheme) ↘ baseScheme = structureMap :=
  Scheme.Opens.hom_ext_of_iSup_eq_top opens covers _ _ fun coordinate ↦ by
    rw [ι_homOfIsFreeGenerator_assoc, localHom, homOfSections_over]

lemma le_preimage_standardOpen (coordinate : coordinates) :
    opens coordinate ≤ homOfIsFreeGenerator sections opens generators structureMap covers ⁻¹ᵁ
      standardOpen coordinates baseScheme coordinate := by
  intro point hx
  have equality : (opens coordinate).ι ⁻¹ᵁ (homOfIsFreeGenerator sections opens generators
    structureMap covers ⁻¹ᵁ standardOpen coordinates baseScheme coordinate) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, ι_homOfIsFreeGenerator, localHom,
      homOfSections_preimage_standardOpen]
    simp [localSections]
  have : (⟨point, hx⟩ : opens coordinate) ∈ (opens coordinate).ι ⁻¹ᵁ (homOfIsFreeGenerator sections
    opens generators structureMap covers ⁻¹ᵁ
      standardOpen coordinates baseScheme coordinate) := equality ▸ trivial
  exact this

private lemma topIso_inv_appLE {targetScheme : Scheme.{u}} (firstMap : sourceScheme ⟶ targetScheme)
  (openSubset : sourceScheme.Opens) (otherOpen : targetScheme.Opens)
    (inclusion : openSubset ≤ firstMap ⁻¹ᵁ otherOpen) (point : Γ(targetScheme, otherOpen)) :
    openSubset.topIso.inv (firstMap.appLE otherOpen openSubset inclusion point) =
      (openSubset.ι ≫ firstMap).appLE otherOpen ⊤ (by
        rw [Scheme.Hom.comp_preimage]
        exact fun localPoint _ ↦ inclusion localPoint.2) point := by
  rw [Scheme.Hom.comp_appLE, Scheme.Opens.ι_appLE]
  simp only [Scheme.Hom.appLE, Scheme.Opens.topIso_inv]
  rw [← ConcreteCategory.comp_apply, Category.assoc, ← Functor.map_comp]
  rfl

/-- The glued projective morphism pulls coordinate ratios back to the local coefficient functions. -/
lemma homOfIsFreeGenerator_appLE_coordRatio (coordinate otherCoordinate : coordinates) :
    (homOfIsFreeGenerator sections opens generators structureMap covers).appLE (standardOpen
      coordinates baseScheme coordinate) (opens coordinate)
        (le_preimage_standardOpen sections opens generators structureMap covers coordinate)
          (coordRatio coordinates baseScheme coordinate otherCoordinate) =
      sectionRatio sections opens generators coordinate otherCoordinate := by
  have equality := topIso_inv_appLE _ _ _ (le_preimage_standardOpen sections opens generators
    structureMap covers coordinate) (coordRatio coordinates baseScheme coordinate otherCoordinate)
  rw [appLE_eq_of_eq (ι_homOfIsFreeGenerator sections opens generators structureMap covers
    coordinate)] at equality
  have h2 := equality.trans (homOfSections_appLE_coordRatio
    (targetScheme := (opens coordinate).toScheme) (baseScheme := baseScheme) (coordinates :=
      coordinates)
    ((opens coordinate).ι ≫ structureMap) (localSections sections opens generators coordinate)
    (span_range_localSections sections opens generators coordinate) (coordinate := coordinate) (by
      simp [localSections]) otherCoordinate _)
  exact (ConcreteCategory.bijective_of_isIso (opens coordinate).topIso.inv).1 h2

/-- The pulled-back coordinate sections satisfy the same transition relations as the given
generators. -/
lemma pullbackSection_twistOneSection_map_eq_sectionRatio_smul (coordinate otherCoordinate :
  coordinates) {openSubset : sourceScheme.Opens}
    (hWj : openSubset ≤ opens otherCoordinate) :
    (twistRestrict (homOfIsFreeGenerator sections opens generators structureMap covers)
      1).presheaf.map
        (homOfLE (fun _ _ ↦ trivial : openSubset ≤ homOfIsFreeGenerator sections opens generators
          structureMap covers ⁻¹ᵁ ⊤)).op
        (pullbackSection _ (twistOneSection coordinates baseScheme coordinate)) =
      sourceScheme.presheaf.map (homOfLE hWj).op (sectionRatio sections opens generators
        otherCoordinate coordinate) •
        (twistRestrict (homOfIsFreeGenerator sections opens generators structureMap covers)
          1).presheaf.map
          (homOfLE (fun _ _ ↦ trivial : openSubset ≤ homOfIsFreeGenerator sections opens generators
            structureMap covers ⁻¹ᵁ ⊤)).op
          (pullbackSection _ (twistOneSection coordinates baseScheme otherCoordinate)) := by
  have relation := pullbackSection_twistOneSection_map_eq_smul (homOfIsFreeGenerator sections opens
    generators structureMap covers) coordinate otherCoordinate
  have relation' := presheaf_map_homOfLE_eq_smul _
    (hWj.trans (le_preimage_standardOpen sections opens generators structureMap covers
      otherCoordinate)) relation
  refine relation'.trans ?_
  congr 1
  rw [← homOfIsFreeGenerator_appLE_coordRatio sections opens generators structureMap covers
    otherCoordinate coordinate, Scheme.Hom.appLE,
    CommRingCat.comp_apply, Scheme.presheaf_map_map_apply]
  rfl

/-- A pulled-back coordinate section restricted to its chosen member of the open cover. -/
def pullbackCoord (coordinate : coordinates) : Γ(twistRestrict (homOfIsFreeGenerator sections opens
  generators structureMap covers) 1, opens coordinate) :=
  (twistRestrict (homOfIsFreeGenerator sections opens generators structureMap covers)
    1).presheaf.map
    (homOfLE (fun _ _ ↦ trivial : opens coordinate ≤ homOfIsFreeGenerator sections opens generators
      structureMap covers ⁻¹ᵁ ⊤)).op
    (pullbackSection _ (twistOneSection coordinates baseScheme coordinate))

lemma isFreeGenerator_pullbackCoord (coordinate : coordinates) :
    IsFreeGenerator (pullbackCoord sections opens generators structureMap covers coordinate) := by
  have equality := (isFreeGenerator_pullbackSection_twistOneSection
    (homOfIsFreeGenerator sections opens generators structureMap covers) coordinate).map
      (le_preimage_standardOpen sections opens generators structureMap covers coordinate)
  rwa [presheaf_map_homOfLE_map_homOfLE] at equality

lemma pullbackCoord_map {coordinate : coordinates} {openSubset : sourceScheme.Opens} (equality :
  openSubset ≤ opens coordinate) :
    (twistRestrict (homOfIsFreeGenerator sections opens generators structureMap covers)
      1).presheaf.map (homOfLE equality).op
        (pullbackCoord sections opens generators structureMap covers coordinate) =
      (twistRestrict (homOfIsFreeGenerator sections opens generators structureMap covers)
        1).presheaf.map
        (homOfLE (fun _ _ ↦ trivial : openSubset ≤ homOfIsFreeGenerator sections opens generators
          structureMap covers ⁻¹ᵁ ⊤)).op
        (pullbackSection _ (twistOneSection coordinates baseScheme coordinate)) :=
  presheaf_map_homOfLE_map_homOfLE _ _ _

lemma restrict_section_map {coordinate : coordinates} {openSubset : sourceScheme.Opens} (equality :
  openSubset ≤ opens coordinate) :
    moduleSheaf.presheaf.map (homOfLE equality).op (moduleSheaf.presheaf.map (homOfLE (le_top :
      opens coordinate ≤ ⊤)).op (sections coordinate)) =
      moduleSheaf.presheaf.map (homOfLE (le_top : openSubset ≤ ⊤)).op (sections coordinate) :=
  presheaf_map_homOfLE_map_homOfLE _ _ _

lemma pullbackCoord_transition (coordinate otherCoordinate : coordinates) (openSubset :
  sourceScheme.Opens) (hi : openSubset ≤ opens coordinate) (hj : openSubset ≤ opens otherCoordinate)
    (scalar otherScalar : Γ(sourceScheme, openSubset))
    (hab : scalar • (twistRestrict (homOfIsFreeGenerator sections opens generators structureMap
      covers) 1).presheaf.map (homOfLE hi).op
        (pullbackCoord sections opens generators structureMap covers coordinate) =
      otherScalar • (twistRestrict (homOfIsFreeGenerator sections opens generators structureMap
        covers) 1).presheaf.map (homOfLE hj).op
        (pullbackCoord sections opens generators structureMap covers otherCoordinate)) :
    scalar • moduleSheaf.presheaf.map (homOfLE hi).op (moduleSheaf.presheaf.map (homOfLE (le_top :
      opens coordinate ≤ ⊤)).op (sections coordinate)) =
      otherScalar • moduleSheaf.presheaf.map (homOfLE hj).op
        (moduleSheaf.presheaf.map (homOfLE (le_top : opens otherCoordinate ≤ ⊤)).op (sections
          otherCoordinate)) := by
  rw [pullbackCoord_map, pullbackCoord_map,
    pullbackSection_twistOneSection_map_eq_sectionRatio_smul sections opens generators structureMap
      covers coordinate otherCoordinate hj, smul_smul] at hab
  rw [← pullbackCoord_map sections opens generators structureMap covers hj] at hab
  have hb := ((isFreeGenerator_pullbackCoord sections opens generators structureMap covers
    otherCoordinate).map hj).smul_left_injective hab
  rw [restrict_section_map, restrict_section_map, ← hb,
    ← sectionRatio_map_smul sections opens generators otherCoordinate coordinate hj, smul_smul]

/-- The comparison from the pullback of `𝒪(1)` to the given module, taking coordinate sections to
the chosen generators. -/
def twistRestrictHom : twistRestrict (homOfIsFreeGenerator sections opens generators structureMap
  covers) 1 ⟶ moduleSheaf :=
  glueHom covers (isFreeGenerator_pullbackCoord sections opens generators structureMap covers)
    (pullbackCoord_transition sections opens generators structureMap covers)

lemma twistRestrictHom_app_pullbackCoord (coordinate : coordinates) :
    (twistRestrictHom sections opens generators structureMap covers).app (opens coordinate)
      (pullbackCoord sections opens generators structureMap covers coordinate) =
      moduleSheaf.presheaf.map (homOfLE (le_top : opens coordinate ≤ ⊤)).op (sections coordinate) :=
        by
  refine (isGlueValue_glueHom_app covers (isFreeGenerator_pullbackCoord sections opens generators
    structureMap covers)
    (pullbackCoord_transition sections opens generators structureMap covers) _).unique covers
    (isFreeGenerator_pullbackCoord sections opens generators structureMap covers) fun
      comparisonCoordinate openSubset hW hWl scalar ha ↦ ?_
  have := pullbackCoord_transition sections opens generators structureMap covers
    comparisonCoordinate coordinate openSubset hWl hW scalar 1 (by rw [one_smul]; exact ha)
  rw [one_smul] at this
  exact this.symm

instance isIso_twistRestrictHom : IsIso (twistRestrictHom sections opens generators structureMap
  covers) := by
  refine Scheme.Modules.isIso_of_isFreeGenerator _ fun point ↦ ?_
  obtain ⟨coordinate, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (covers.ge (Set.mem_univ point))
  exact ⟨opens coordinate, pullbackCoord sections opens generators structureMap covers coordinate,
    hi, isFreeGenerator_pullbackCoord sections opens generators structureMap covers coordinate,
    (twistRestrictHom_app_pullbackCoord sections opens generators structureMap covers
      coordinate).symm ▸ generators coordinate⟩

lemma twistRestrictHom_app_pullbackSection (otherCoordinate : coordinates) :
    (twistRestrictHom sections opens generators structureMap covers).app _ (pullbackSection _
      (twistOneSection coordinates baseScheme otherCoordinate)) =
      moduleSheaf.presheaf.map (homOfLE (le_top : homOfIsFreeGenerator sections opens generators
        structureMap covers ⁻¹ᵁ ⊤ ≤ ⊤)).op
        (sections otherCoordinate) := by
  refine (isGlueValue_glueHom_app covers (isFreeGenerator_pullbackCoord sections opens generators
    structureMap covers)
    (pullbackCoord_transition sections opens generators structureMap covers) _).unique covers
    (isFreeGenerator_pullbackCoord sections opens generators structureMap covers) fun coordinate
      openSubset hW hWi scalar ha ↦ ?_
  have hT := pullbackSection_twistOneSection_map_eq_sectionRatio_smul sections opens generators
    structureMap covers otherCoordinate coordinate hWi
  rw [pullbackCoord_map] at ha
  have ha'' := ha.trans hT
  rw [← pullbackCoord_map sections opens generators structureMap covers hWi] at ha''
  have ha' := ((isFreeGenerator_pullbackCoord sections opens generators structureMap covers
    coordinate).map hWi).smul_left_injective ha''
  rw [presheaf_map_homOfLE_map_homOfLE, restrict_section_map, ha',
    sectionRatio_map_smul sections opens generators coordinate otherCoordinate hWi]

include generators covers in
/-- A family of global sections which freely generate on an open cover defines a projective
morphism and an isomorphism from its pullback of `𝒪(1)`, preserving the chosen sections. -/
theorem exists_hom_twistRestrict :
    ∃ projectiveMap : sourceScheme ⟶ ℙ(coordinates; baseScheme), projectiveMap ≫ ℙ(coordinates;
      baseScheme) ↘ baseScheme = structureMap ∧ ∃ comparison : twistRestrict projectiveMap 1 ⟶
      moduleSheaf, IsIso comparison ∧
      ∀ otherCoordinate, comparison.app _ (pullbackSection projectiveMap (twistOneSection
        coordinates baseScheme otherCoordinate)) =
        moduleSheaf.presheaf.map (homOfLE (le_top : projectiveMap ⁻¹ᵁ ⊤ ≤ ⊤)).op (sections
          otherCoordinate) :=
  ⟨homOfIsFreeGenerator sections opens generators structureMap covers, homOfIsFreeGenerator_over
    sections opens generators structureMap covers,
    twistRestrictHom sections opens generators structureMap covers, inferInstance,
      twistRestrictHom_app_pullbackSection sections opens generators structureMap covers⟩

end Construction

section Sections

variable {sourceScheme baseScheme : Scheme.{u}} {coordinates : Type u} {moduleSheaf :
  sourceScheme.Modules} {sections : coordinates → Γ(moduleSheaf, ⊤)}
  {projectiveMap : sourceScheme ⟶ ℙ(coordinates; baseScheme)} (comparison : twistRestrict
    projectiveMap 1 ⟶ moduleSheaf) [IsIso comparison]
  (comparison_sections : ∀ otherCoordinate, comparison.app _ (pullbackSection projectiveMap
    (twistOneSection coordinates baseScheme otherCoordinate)) =
    moduleSheaf.presheaf.map (homOfLE (le_top : projectiveMap ⁻¹ᵁ ⊤ ≤ ⊤)).op (sections
      otherCoordinate))
include comparison_sections

/-- A comparison with the pullback of `𝒪(1)` makes the corresponding section a free generator over
the inverse image of its standard open. -/
lemma isFreeGenerator_of_twistRestrict_iso (coordinate : coordinates) :
    IsFreeGenerator (moduleSheaf.presheaf.map (homOfLE (le_top : projectiveMap ⁻¹ᵁ standardOpen
      coordinates baseScheme coordinate ≤ ⊤)).op
      (sections coordinate)) := by
  have equality := (isFreeGenerator_pullbackSection_twistOneSection projectiveMap
    coordinate).app_hom (asIso comparison)
  rwa [asIso_hom, Hom.app_presheaf_map, comparison_sections,
    presheaf_map_homOfLE_map_homOfLE] at equality

omit [IsIso comparison] in
/-- A comparison preserving coordinate sections also preserves their coordinate-ratio transition
relations. -/
lemma map_eq_coordRatio_smul_of_twistRestrict_iso (coordinate otherCoordinate : coordinates) :
    moduleSheaf.presheaf.map (homOfLE (le_top : projectiveMap ⁻¹ᵁ standardOpen coordinates
      baseScheme coordinate ≤ ⊤)).op (sections otherCoordinate) =
      projectiveMap.app (standardOpen coordinates baseScheme coordinate) (coordRatio coordinates
        baseScheme coordinate otherCoordinate) •
        moduleSheaf.presheaf.map (homOfLE (le_top : projectiveMap ⁻¹ᵁ standardOpen coordinates
          baseScheme coordinate ≤ ⊤)).op (sections coordinate) := by
  have equality := congrArg (comparison.app _) (pullbackSection_twistOneSection_map_eq_smul
    projectiveMap otherCoordinate coordinate)
  rwa [Hom.app_smul, Hom.app_presheaf_map, Hom.app_presheaf_map, comparison_sections,
    comparison_sections,
    presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE] at equality

end Sections

end ProjectiveSpace

end AlgebraicGeometry
