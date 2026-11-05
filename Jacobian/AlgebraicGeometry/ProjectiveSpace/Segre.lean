import Jacobian.AlgebraicGeometry.ProjectiveSpace.Charts
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.FromGlobalSections
import Jacobian.AlgebraicGeometry.Pullbacks.Affine
import Jacobian.RingTheory.MvPolynomial.Generators

/-!
# The Segre closed immersion

The products of homogeneous coordinates define compatible morphisms on the
standard charts of a product of projective spaces. Gluing gives the integral
Segre morphism. Its standard affine chart maps are closed immersions, and base
change gives the relative Segre closed immersion over any base scheme.
-/

noncomputable section

set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

/-- Two open subsets of a scheme agree if their preimages under every chart of an open
cover agree. -/
private lemma Scheme.Opens.ext_of_openCover {scheme : Scheme.{u}} (cover : scheme.OpenCover) {firstOpen secondOpen : scheme.Opens}
    (compatibility : ∀ index, cover.f index ⁻¹ᵁ firstOpen = cover.f index ⁻¹ᵁ secondOpen) : firstOpen = secondOpen := by
  refine TopologicalSpace.Opens.ext (Set.ext fun point ↦ ?_)
  obtain ⟨chartPoint, hy⟩ := cover.covers point
  rw [← hy]
  constructor
  · intro hx
    have hyU : chartPoint ∈ cover.f (cover.idx point) ⁻¹ᵁ firstOpen := hx
    rw [compatibility] at hyU
    exact hyU
  · intro hx
    have hyV : chartPoint ∈ cover.f (cover.idx point) ⁻¹ᵁ secondOpen := hx
    rw [← compatibility] at hyV
    exact hyV

/-- The range of the morphism of fibre products induced by two open immersions `firstOpenMap` and `secondOpenMap` is
the intersection of the preimages of the ranges of `firstOpenMap` and `secondOpenMap`. -/
private lemma Scheme.Pullback.opensRange_map {firstScheme secondScheme baseScheme firstSource secondSource : Scheme.{u}} {firstMap : firstScheme ⟶ baseScheme} {secondMap : secondScheme ⟶ baseScheme}
    (firstOpenMap : firstSource ⟶ firstScheme) (secondOpenMap : secondSource ⟶ secondScheme) [IsOpenImmersion firstOpenMap] [IsOpenImmersion secondOpenMap]
    (w₁ : (firstOpenMap ≫ firstMap) ≫ 𝟙 baseScheme = firstOpenMap ≫ firstMap) (w₂ : (secondOpenMap ≫ secondMap) ≫ 𝟙 baseScheme = secondOpenMap ≫ secondMap) :
    (pullback.map (firstOpenMap ≫ firstMap) (secondOpenMap ≫ secondMap) firstMap secondMap firstOpenMap secondOpenMap (𝟙 baseScheme) w₁ w₂).opensRange =
      pullback.fst firstMap secondMap ⁻¹ᵁ firstOpenMap.opensRange ⊓ pullback.snd firstMap secondMap ⁻¹ᵁ secondOpenMap.opensRange := by
  set productMap := pullback.map (firstOpenMap ≫ firstMap) (secondOpenMap ≫ secondMap) firstMap secondMap firstOpenMap secondOpenMap (𝟙 baseScheme) w₁ w₂ with hM
  have hMfst : productMap ≫ pullback.fst firstMap secondMap = pullback.fst (firstOpenMap ≫ firstMap) (secondOpenMap ≫ secondMap) ≫ firstOpenMap := by simp [hM]
  have hMsnd : productMap ≫ pullback.snd firstMap secondMap = pullback.snd (firstOpenMap ≫ firstMap) (secondOpenMap ≫ secondMap) ≫ secondOpenMap := by simp [hM]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨sourcePoint, rfl⟩
    refine ⟨?_, ?_⟩
    · change (pullback.fst firstMap secondMap).base (productMap.base sourcePoint) ∈ firstOpenMap.opensRange
      rw [← Scheme.Hom.comp_apply, hMfst]
      exact ⟨_, rfl⟩
    · change (pullback.snd firstMap secondMap).base (productMap.base sourcePoint) ∈ secondOpenMap.opensRange
      rw [← Scheme.Hom.comp_apply, hMsnd]
      exact ⟨_, rfl⟩
  · set openSubset : (pullback firstMap secondMap).Opens :=
      pullback.fst firstMap secondMap ⁻¹ᵁ firstOpenMap.opensRange ⊓ pullback.snd firstMap secondMap ⁻¹ᵁ secondOpenMap.opensRange with hW
    have h1 : Set.range (openSubset.ι ≫ pullback.fst firstMap secondMap).base ⊆ Set.range firstOpenMap.base := by
      rintro _ ⟨point, rfl⟩
      exact point.2.1
    have h2 : Set.range (openSubset.ι ≫ pullback.snd firstMap secondMap).base ⊆ Set.range secondOpenMap.base := by
      rintro _ ⟨point, rfl⟩
      exact point.2.2
    have hab : IsOpenImmersion.lift firstOpenMap _ h1 ≫ (firstOpenMap ≫ firstMap) =
        IsOpenImmersion.lift secondOpenMap _ h2 ≫ (secondOpenMap ≫ secondMap) := by
      rw [← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
        IsOpenImmersion.lift_fac, Category.assoc, Category.assoc, pullback.condition]
    have hc : pullback.lift _ _ hab ≫ productMap = openSubset.ι := by
      apply pullback.hom_ext
      · rw [Category.assoc, hMfst, ← Category.assoc, pullback.lift_fst,
          IsOpenImmersion.lift_fac]
      · rw [Category.assoc, hMsnd, ← Category.assoc, pullback.lift_snd,
          IsOpenImmersion.lift_fac]
    rintro point hy
    refine ⟨(pullback.lift _ _ hab).base ⟨point, hy⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, hc]
    rfl

/-- The range of the `(i, j)`-th chart of the product cover of a fibre product is the
intersection of the preimages of the `i`-th and `j`-th chart of the two covers. -/
private lemma Scheme.Pullback.opensRange_openCoverOfLeftRight_f {firstScheme secondScheme baseScheme : Scheme.{u}}
    (firstCover : firstScheme.OpenCover) (secondCover : secondScheme.OpenCover) (firstMap : firstScheme ⟶ baseScheme) (secondMap : secondScheme ⟶ baseScheme) (chartPair : firstCover.I₀ × secondCover.I₀) :
    ((Scheme.Pullback.openCoverOfLeftRight firstCover secondCover firstMap secondMap).f chartPair).opensRange =
      pullback.fst firstMap secondMap ⁻¹ᵁ (firstCover.f chartPair.1).opensRange ⊓
        pullback.snd firstMap secondMap ⁻¹ᵁ (secondCover.f chartPair.2).opensRange := by
  rw [← Scheme.Pullback.opensRange_map (firstMap := firstMap) (secondMap := secondMap) (firstCover.f chartPair.1) (secondCover.f chartPair.2)
    (by simp) (by simp)]
  refine TopologicalSpace.Opens.ext ?_
  rw [Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange,
    Scheme.Pullback.openCoverOfLeftRight_f]
  rfl

variable {sourceScheme targetScheme sourceOpenScheme targetOpenScheme : Scheme.{u}}

/-- If `sourceInclusion ≫ morphism = restrictedMap ≫ targetInclusion` with `sourceInclusion`, `targetInclusion` open immersions and `morphism ⁻¹ᵁ (range targetInclusion) = range sourceInclusion`, then
the restriction `morphism ∣_ targetInclusion.opensRange` is isomorphic to `restrictedMap` in the arrow category. -/
private def morphismRestrictArrowIso (morphism : sourceScheme ⟶ targetScheme) {sourceInclusion : sourceOpenScheme ⟶ sourceScheme} {targetInclusion : targetOpenScheme ⟶ targetScheme}
    (restrictedMap : sourceOpenScheme ⟶ targetOpenScheme) [IsOpenImmersion sourceInclusion] [IsOpenImmersion targetInclusion]
    (compatibility : sourceInclusion ≫ morphism = restrictedMap ≫ targetInclusion) (range_eq : morphism ⁻¹ᵁ targetInclusion.opensRange = sourceInclusion.opensRange) :
    Arrow.mk (morphism ∣_ targetInclusion.opensRange) ≅ Arrow.mk restrictedMap := by
  have hα : Set.range ⇑(morphism ⁻¹ᵁ targetInclusion.opensRange).ι = Set.range ⇑sourceInclusion := by
    rw [Scheme.Opens.range_ι, range_eq]; rfl
  have hβ : Set.range ⇑targetInclusion.opensRange.ι = Set.range ⇑targetInclusion := by
    rw [Scheme.Opens.range_ι]; rfl
  refine Arrow.isoMk' (morphism ∣_ targetInclusion.opensRange) restrictedMap
    (IsOpenImmersion.isoOfRangeEq (morphism ⁻¹ᵁ targetInclusion.opensRange).ι sourceInclusion hα)
    (IsOpenImmersion.isoOfRangeEq targetInclusion.opensRange.ι targetInclusion hβ) ?_
  rw [← cancel_mono targetInclusion, Category.assoc, Category.assoc, ← compatibility,
    IsOpenImmersion.isoOfRangeEq_hom_fac_assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, morphismRestrict_ι]

end AlgebraicGeometry

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

section Cover

variable (coordinates baseRing : Type u) [CommRing baseRing]

/-- The standard affine open cover of `ℙ^σ_A` by the charts `D₊(Xᵢ) ≅ Spec (baseRing[X]_{Xᵢ})₀`. -/
private def projectiveSpaceOverAffineAffineOpenCover :
    (projectiveSpaceOverAffine coordinates baseRing).AffineOpenCover :=
  affineOpenCoverOfIrrelevantLESpan _ (fun firstCoordinate : coordinates ↦ MvPolynomial.X firstCoordinate)
    (fun firstCoordinate ↦ X_mem_homogeneousSubmodule_one baseRing firstCoordinate) (fun _ ↦ Nat.one_pos)
    (toIdeal_irrelevant_homogeneousSubmodule coordinates baseRing).le

@[simp]
private lemma projectiveSpaceOverAffineAffineOpenCover_X (firstCoordinate : coordinates) :
    (projectiveSpaceOverAffineAffineOpenCover coordinates baseRing).X firstCoordinate =
      CommRingCat.of (Away (homogeneousSubmodule coordinates baseRing) (MvPolynomial.X firstCoordinate)) := rfl

@[simp]
private lemma projectiveSpaceOverAffineAffineOpenCover_f (firstCoordinate : coordinates) :
    (projectiveSpaceOverAffineAffineOpenCover coordinates baseRing).f firstCoordinate =
      awayι _ (MvPolynomial.X firstCoordinate) (X_mem_homogeneousSubmodule_one baseRing firstCoordinate) Nat.one_pos := rfl

end Cover

variable (firstCoordinates secondCoordinates : Type u)

/-- The open cover of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` by the products `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` of standard charts
of the two factors. -/
def segreCover :
    (pullback (terminal.from (projectiveSpaceOverAffine firstCoordinates (ULift.{u} ℤ)))
      (terminal.from (projectiveSpaceOverAffine secondCoordinates (ULift.{u} ℤ)))).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight
    (projectiveSpaceOverAffineAffineOpenCover firstCoordinates (ULift.{u} ℤ)).openCover
    (projectiveSpaceOverAffineAffineOpenCover secondCoordinates (ULift.{u} ℤ)).openCover _ _

variable {firstCoordinates secondCoordinates}

/-- The projection of the `(firstCoordinate, secondCoordinate)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` to the `firstCoordinate`-th standard chart of
the first factor. -/
def segreCoverFst (firstCoordinate : firstCoordinates) (secondCoordinate : secondCoordinates) :
    (segreCover firstCoordinates secondCoordinates).X (firstCoordinate, secondCoordinate) ⟶
      Spec (.of <| Away (homogeneousSubmodule firstCoordinates (ULift.{u} ℤ)) (MvPolynomial.X firstCoordinate)) :=
  pullback.fst _ _

/-- The projection of the `(firstCoordinate, secondCoordinate)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` to the `secondCoordinate`-th standard chart of
the second factor. -/
def segreCoverSnd (firstCoordinate : firstCoordinates) (secondCoordinate : secondCoordinates) :
    (segreCover firstCoordinates secondCoordinates).X (firstCoordinate, secondCoordinate) ⟶
      Spec (.of <| Away (homogeneousSubmodule secondCoordinates (ULift.{u} ℤ)) (MvPolynomial.X secondCoordinate)) :=
  pullback.snd _ _

@[reassoc]
lemma segreCoverFst_awayι (firstCoordinate : firstCoordinates) (secondCoordinate : secondCoordinates) :
    segreCoverFst firstCoordinate secondCoordinate ≫ awayι _ (MvPolynomial.X firstCoordinate)
        (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) firstCoordinate) Nat.one_pos =
      (segreCover firstCoordinates secondCoordinates).f (firstCoordinate, secondCoordinate) ≫ pullback.fst _ _ := by
  simp [segreCover, segreCoverFst]

@[reassoc]
lemma segreCoverSnd_awayι (firstCoordinate : firstCoordinates) (secondCoordinate : secondCoordinates) :
    segreCoverSnd firstCoordinate secondCoordinate ≫ awayι _ (MvPolynomial.X secondCoordinate)
        (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) secondCoordinate) Nat.one_pos =
      (segreCover firstCoordinates secondCoordinates).f (firstCoordinate, secondCoordinate) ≫ pullback.snd _ _ := by
  simp [segreCover, segreCoverSnd]

/-- The section `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)` of the `(firstCoordinate, secondCoordinate)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`. It is the
image of the homogeneous coordinate `W_{targetFirst,targetSecond}` of `ℙ^(firstCoordinates×secondCoordinates)_ℤ` under the Segre morphism. -/
def segreChartSection (firstCoordinate : firstCoordinates) (secondCoordinate : secondCoordinates) (coordinatePair : firstCoordinates × secondCoordinates) : Γ((segreCover firstCoordinates secondCoordinates).X (firstCoordinate, secondCoordinate), ⊤) :=
  ((Scheme.ΓSpecIso _).inv ≫ (segreCoverFst firstCoordinate secondCoordinate).appTop).hom
      (awayXRatio (ULift.{u} ℤ) firstCoordinate coordinatePair.1) *
    ((Scheme.ΓSpecIso _).inv ≫ (segreCoverSnd firstCoordinate secondCoordinate).appTop).hom
      (awayXRatio (ULift.{u} ℤ) secondCoordinate coordinatePair.2)

@[simp]
lemma segreChartSection_self (firstCoordinate : firstCoordinates) (secondCoordinate : secondCoordinates) : segreChartSection firstCoordinate secondCoordinate (firstCoordinate, secondCoordinate) = 1 := by
  simp [segreChartSection]

lemma span_range_segreChartSection_eq_top (firstCoordinate : firstCoordinates) (secondCoordinate : secondCoordinates) :
    Ideal.span (Set.range (segreChartSection firstCoordinate secondCoordinate)) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← segreChartSection_self firstCoordinate secondCoordinate]
  exact Ideal.subset_span ⟨(firstCoordinate, secondCoordinate), rfl⟩

/-- The Segre morphism on the `(firstCoordinate, secondCoordinate)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`: the morphism to
`ℙ^(firstCoordinates×secondCoordinates)_ℤ` sending the homogeneous coordinate `W_{targetFirst,targetSecond}` to `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)`. -/
def segreChartHom (firstCoordinate : firstCoordinates) (secondCoordinate : secondCoordinates) :
    (segreCover firstCoordinates secondCoordinates).X (firstCoordinate, secondCoordinate) ⟶ projectiveSpaceOverAffine (firstCoordinates × secondCoordinates) (ULift.{u} ℤ) :=
  fromOfGlobalSections _ (ProjectiveSpace.evalSections (segreChartSection firstCoordinate secondCoordinate))
    (ProjectiveSpace.map_irrelevant_evalSections_eq_top _
      (span_range_segreChartSection_eq_top firstCoordinate secondCoordinate))

section Compatibility

variable (firstCoordinate otherFirstCoordinate : firstCoordinates) (secondCoordinate otherSecondCoordinate : secondCoordinates)

/-- The chart morphisms `segreChartHom` agree on the overlap of two charts of the standard
cover of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`: the two chart morphisms differ by rescaling the homogeneous
coordinates of `ℙ^(firstCoordinates×secondCoordinates)_ℤ` by the unit `(Xᵢ / Xᵢ') · (Yⱼ / Yⱼ')`. -/
lemma segreChartHom_compatible :
    pullback.fst ((segreCover firstCoordinates secondCoordinates).f (firstCoordinate, secondCoordinate)) ((segreCover firstCoordinates secondCoordinates).f (otherFirstCoordinate, otherSecondCoordinate)) ≫ segreChartHom firstCoordinate secondCoordinate =
      pullback.snd ((segreCover firstCoordinates secondCoordinates).f (firstCoordinate, secondCoordinate)) ((segreCover firstCoordinates secondCoordinates).f (otherFirstCoordinate, otherSecondCoordinate)) ≫
        segreChartHom otherFirstCoordinate otherSecondCoordinate := by
  have hXi : ∀ targetFirst : firstCoordinates, (MvPolynomial.X targetFirst : MvPolynomial firstCoordinates (ULift.{u} ℤ)) ∈
      homogeneousSubmodule firstCoordinates (ULift.{u} ℤ) 1 := X_mem_homogeneousSubmodule_one _
  have hXj : ∀ targetSecond : secondCoordinates, (MvPolynomial.X targetSecond : MvPolynomial secondCoordinates (ULift.{u} ℤ)) ∈
      homogeneousSubmodule secondCoordinates (ULift.{u} ℤ) 1 := X_mem_homogeneousSubmodule_one _
  have hXi1 : ∀ targetFirst : firstCoordinates, (MvPolynomial.X targetFirst : MvPolynomial firstCoordinates (ULift.{u} ℤ)) ∈
      homogeneousSubmodule firstCoordinates (ULift.{u} ℤ) (1 • 1) := fun targetFirst ↦ by simpa using hXi targetFirst
  have hXj1 : ∀ targetSecond : secondCoordinates, (MvPolynomial.X targetSecond : MvPolynomial secondCoordinates (ULift.{u} ℤ)) ∈
      homogeneousSubmodule secondCoordinates (ULift.{u} ℤ) (1 • 1) := fun targetSecond ↦ by simpa using hXj targetSecond
  set firstOverlap := pullback.fst ((segreCover firstCoordinates secondCoordinates).f (firstCoordinate, secondCoordinate)) ((segreCover firstCoordinates secondCoordinates).f (otherFirstCoordinate, otherSecondCoordinate))
  set secondOverlap := pullback.snd ((segreCover firstCoordinates secondCoordinates).f (firstCoordinate, secondCoordinate)) ((segreCover firstCoordinates secondCoordinates).f (otherFirstCoordinate, otherSecondCoordinate))
  have hcond : firstOverlap ≫ (segreCover firstCoordinates secondCoordinates).f (firstCoordinate, secondCoordinate) = secondOverlap ≫ (segreCover firstCoordinates secondCoordinates).f (otherFirstCoordinate, otherSecondCoordinate) :=
    pullback.condition
  have ha : (firstOverlap ≫ segreCoverFst firstCoordinate secondCoordinate) ≫ awayι _ (MvPolynomial.X firstCoordinate) (hXi firstCoordinate) Nat.one_pos =
      (secondOverlap ≫ segreCoverFst otherFirstCoordinate otherSecondCoordinate) ≫ awayι _ (MvPolynomial.X otherFirstCoordinate) (hXi otherFirstCoordinate) Nat.one_pos := by
    rw [Category.assoc, Category.assoc, segreCoverFst_awayι, segreCoverFst_awayι,
      ← Category.assoc, ← Category.assoc, hcond]
  have hb : (firstOverlap ≫ segreCoverSnd firstCoordinate secondCoordinate) ≫ awayι _ (MvPolynomial.X secondCoordinate) (hXj secondCoordinate) Nat.one_pos =
      (secondOverlap ≫ segreCoverSnd otherFirstCoordinate otherSecondCoordinate) ≫ awayι _ (MvPolynomial.X otherSecondCoordinate) (hXj otherSecondCoordinate) Nat.one_pos := by
    rw [Category.assoc, Category.assoc, segreCoverSnd_awayι, segreCoverSnd_awayι,
      ← Category.assoc, ← Category.assoc, hcond]
  have hA : IsUnit (((Scheme.ΓSpecIso _).inv ≫ (secondOverlap ≫ segreCoverFst otherFirstCoordinate otherSecondCoordinate).appTop).hom
      (awayXRatio (ULift.{u} ℤ) otherFirstCoordinate firstCoordinate)) :=
    isUnit_appTop_awayMk _ Nat.one_pos (hXi firstCoordinate) (hXi otherFirstCoordinate) _ _ ha (hXi1 firstCoordinate) (hXi1 otherFirstCoordinate)
  have hB : IsUnit (((Scheme.ΓSpecIso _).inv ≫ (secondOverlap ≫ segreCoverSnd otherFirstCoordinate otherSecondCoordinate).appTop).hom
      (awayXRatio (ULift.{u} ℤ) otherSecondCoordinate secondCoordinate)) :=
    isUnit_appTop_awayMk _ Nat.one_pos (hXj secondCoordinate) (hXj otherSecondCoordinate) _ _ hb (hXj1 secondCoordinate) (hXj1 otherSecondCoordinate)
  have hpull : ∀ {coordinateRing : CommRingCat.{u}} {targetScheme sourceScheme : Scheme.{u}} (sourceMap : sourceScheme ⟶ targetScheme) (chartMap : targetScheme ⟶ Spec coordinateRing) (coordinateValue : coordinateRing),
      sourceMap.appTop.hom (((Scheme.ΓSpecIso coordinateRing).inv ≫ chartMap.appTop).hom coordinateValue) =
        ((Scheme.ΓSpecIso coordinateRing).inv ≫ (sourceMap ≫ chartMap).appTop).hom coordinateValue := fun _ _ _ ↦ rfl
  have hvar : ∀ coordinatePair : firstCoordinates × secondCoordinates, secondOverlap.appTop.hom (segreChartSection otherFirstCoordinate otherSecondCoordinate coordinatePair) =
      (hA.unit * hB.unit).val *
        firstOverlap.appTop.hom (segreChartSection firstCoordinate secondCoordinate coordinatePair) := by
    intro coordinatePair
    have h1 : ((Scheme.ΓSpecIso _).inv ≫ (secondOverlap ≫ segreCoverFst otherFirstCoordinate otherSecondCoordinate).appTop).hom
        (awayXRatio (ULift.{u} ℤ) otherFirstCoordinate coordinatePair.1) =
        ((Scheme.ΓSpecIso _).inv ≫ (firstOverlap ≫ segreCoverFst firstCoordinate secondCoordinate).appTop).hom
            (awayXRatio (ULift.{u} ℤ) firstCoordinate coordinatePair.1) *
          ((Scheme.ΓSpecIso _).inv ≫ (secondOverlap ≫ segreCoverFst otherFirstCoordinate otherSecondCoordinate).appTop).hom
            (awayXRatio (ULift.{u} ℤ) otherFirstCoordinate firstCoordinate) :=
      appTop_awayMk_eq_mul _ Nat.one_pos (hXi firstCoordinate) (hXi otherFirstCoordinate) _ _ ha (hXi1 firstCoordinate)
        (MvPolynomial.X coordinatePair.1) (hXi1 coordinatePair.1)
    have h2 : ((Scheme.ΓSpecIso _).inv ≫ (secondOverlap ≫ segreCoverSnd otherFirstCoordinate otherSecondCoordinate).appTop).hom
        (awayXRatio (ULift.{u} ℤ) otherSecondCoordinate coordinatePair.2) =
        ((Scheme.ΓSpecIso _).inv ≫ (firstOverlap ≫ segreCoverSnd firstCoordinate secondCoordinate).appTop).hom
            (awayXRatio (ULift.{u} ℤ) secondCoordinate coordinatePair.2) *
          ((Scheme.ΓSpecIso _).inv ≫ (secondOverlap ≫ segreCoverSnd otherFirstCoordinate otherSecondCoordinate).appTop).hom
            (awayXRatio (ULift.{u} ℤ) otherSecondCoordinate secondCoordinate) :=
      appTop_awayMk_eq_mul _ Nat.one_pos (hXj secondCoordinate) (hXj otherSecondCoordinate) _ _ hb (hXj1 secondCoordinate)
        (MvPolynomial.X coordinatePair.2) (hXj1 coordinatePair.2)
    simp only [segreChartSection, map_mul, hpull, h1, h2, Units.val_mul, IsUnit.unit_spec]
    ring
  simp only [segreChartHom]
  rw [comp_fromOfGlobalSections _ firstOverlap _ _ (map_irrelevant_comp_appTop_eq_top _ firstOverlap _
      (ProjectiveSpace.map_irrelevant_evalSections_eq_top _
        (span_range_segreChartSection_eq_top firstCoordinate secondCoordinate))),
    comp_fromOfGlobalSections _ secondOverlap _ _ (map_irrelevant_comp_appTop_eq_top _ secondOverlap _
      (ProjectiveSpace.map_irrelevant_evalSections_eq_top _
        (span_range_segreChartSection_eq_top otherFirstCoordinate otherSecondCoordinate)))]
  refine fromOfGlobalSections_eq_of_unit_pow_mul _ (hA.unit * hB.unit) _ _ (fun degree element hda ↦ ?_) _ _
  rw [ProjectiveSpace.comp_evalSections, ProjectiveSpace.comp_evalSections]
  simp only [hvar]
  exact ProjectiveSpace.evalSections_const_mul _ _ hda

end Compatibility

variable (firstCoordinates secondCoordinates)

/-- **The Segre morphism** `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ ⟶ ℙ^(firstCoordinates×secondCoordinates)_ℤ` between the integral models of
projective spaces, sending element pair of points with homogeneous coordinates `(xₖ)` and `(yₗ)` to
the point with homogeneous coordinates `(xₖ · yₗ)`.

It is glued from the morphisms `segreChartHom firstCoordinate secondCoordinate` on the standard cover of the product by the
charts `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)`. -/
def segre :
    pullback (terminal.from (projectiveSpaceOverAffine firstCoordinates (ULift.{u} ℤ)))
        (terminal.from (projectiveSpaceOverAffine secondCoordinates (ULift.{u} ℤ))) ⟶
      projectiveSpaceOverAffine (firstCoordinates × secondCoordinates) (ULift.{u} ℤ) :=
  (segreCover firstCoordinates secondCoordinates).glueMorphisms (fun chartPair ↦ segreChartHom chartPair.1 chartPair.2)
    fun chartPair otherChartPair ↦ segreChartHom_compatible chartPair.1 otherChartPair.1 chartPair.2 otherChartPair.2

variable {firstCoordinates secondCoordinates}

/-- On the chart `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`, the Segre morphism is the morphism
`segreChartHom firstCoordinate secondCoordinate` given by the sections `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)`. -/
@[reassoc]
lemma segreCover_f_comp_segre (firstCoordinate : firstCoordinates) (secondCoordinate : secondCoordinates) :
    (segreCover firstCoordinates secondCoordinates).f (firstCoordinate, secondCoordinate) ≫ segre firstCoordinates secondCoordinates = segreChartHom firstCoordinate secondCoordinate :=
  (segreCover firstCoordinates secondCoordinates).ι_glueMorphisms _ _ (firstCoordinate, secondCoordinate)

section ClosedImmersion

/-- The `(firstCoordinate, secondCoordinate)`-chart `D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` is the fibre product of the two
affine charts over the terminal scheme. -/
lemma isPullback_segreCoverFst_segreCoverSnd (firstCoordinate : firstCoordinates) (secondCoordinate : secondCoordinates) :
    IsPullback (segreCoverFst firstCoordinate secondCoordinate) (segreCoverSnd firstCoordinate secondCoordinate)
      (terminal.from (Spec (.of <| Away (homogeneousSubmodule firstCoordinates (ULift.{u} ℤ))
        (MvPolynomial.X firstCoordinate))))
      (terminal.from (Spec (.of <| Away (homogeneousSubmodule secondCoordinates (ULift.{u} ℤ))
        (MvPolynomial.X secondCoordinate)))) := by
  have h1 : awayι _ (MvPolynomial.X firstCoordinate) (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) firstCoordinate)
      Nat.one_pos ≫ terminal.from (projectiveSpaceOverAffine firstCoordinates (ULift.{u} ℤ)) =
      terminal.from _ := terminal.hom_ext _ _
  have h2 : awayι _ (MvPolynomial.X secondCoordinate) (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) secondCoordinate)
      Nat.one_pos ≫ terminal.from (projectiveSpaceOverAffine secondCoordinates (ULift.{u} ℤ)) =
      terminal.from _ := terminal.hom_ext _ _
  rw [← h1, ← h2]
  exact IsPullback.of_hasPullback _ _

instance isAffine_segreCover_X (firstCoordinate : firstCoordinates) (secondCoordinate : secondCoordinates) : IsAffine ((segreCover firstCoordinates secondCoordinates).X (firstCoordinate, secondCoordinate)) :=
  IsAffine.of_isIso (isPullback_segreCoverFst_segreCoverSnd firstCoordinate secondCoordinate).isoPullback.hom

/-- **The chart sections generate the sections of the chart**: the global sections of
`D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` are generated as element ring by the products `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)`. -/
lemma closure_range_segreChartSection_eq_top (firstCoordinate : firstCoordinates) (secondCoordinate : secondCoordinates) :
    Subring.closure (Set.range (segreChartSection firstCoordinate secondCoordinate)) = ⊤ := by
  have hR : Function.Surjective ((↑) : ℤ → ULift.{u} ℤ) := fun integer ↦ ⟨integer.down, by ext; simp⟩
  exact closure_range_mul_appTop_eq_top (isPullback_segreCoverFst_segreCoverSnd firstCoordinate secondCoordinate)
    (MvPolynomial.closure_range_awayXRatio_eq_top _ hR firstCoordinate)
    (MvPolynomial.closure_range_awayXRatio_eq_top _ hR secondCoordinate)
    (awayXRatio_self (ULift.{u} ℤ) firstCoordinate) (awayXRatio_self (ULift.{u} ℤ) secondCoordinate)

/-- The `(firstCoordinate, secondCoordinate)`-chart of the standard cover of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` is the locus where the `firstCoordinate`-th
homogeneous coordinate of the first factor and the `secondCoordinate`-th homogeneous coordinate of the second
factor do not vanish. -/
lemma opensRange_segreCover_f (firstCoordinate : firstCoordinates) (secondCoordinate : secondCoordinates) :
    ((segreCover firstCoordinates secondCoordinates).f (firstCoordinate, secondCoordinate)).opensRange =
      pullback.fst (terminal.from (projectiveSpaceOverAffine firstCoordinates (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine secondCoordinates (ULift.{u} ℤ))) ⁻¹ᵁ
        basicOpen (homogeneousSubmodule firstCoordinates (ULift.{u} ℤ)) (MvPolynomial.X firstCoordinate) ⊓
      pullback.snd (terminal.from (projectiveSpaceOverAffine firstCoordinates (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine secondCoordinates (ULift.{u} ℤ))) ⁻¹ᵁ
        basicOpen (homogeneousSubmodule secondCoordinates (ULift.{u} ℤ)) (MvPolynomial.X secondCoordinate) := by
  have h1 : ((projectiveSpaceOverAffineAffineOpenCover firstCoordinates (ULift.{u} ℤ)).openCover.f firstCoordinate).opensRange =
      basicOpen (homogeneousSubmodule firstCoordinates (ULift.{u} ℤ)) (MvPolynomial.X firstCoordinate) :=
    opensRange_awayι _ _ (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) firstCoordinate) Nat.one_pos
  have h2 : ((projectiveSpaceOverAffineAffineOpenCover secondCoordinates (ULift.{u} ℤ)).openCover.f secondCoordinate).opensRange =
      basicOpen (homogeneousSubmodule secondCoordinates (ULift.{u} ℤ)) (MvPolynomial.X secondCoordinate) :=
    opensRange_awayι _ _ (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) secondCoordinate) Nat.one_pos
  rw [← h1, ← h2]
  exact Scheme.Pullback.opensRange_openCoverOfLeftRight_f
    (projectiveSpaceOverAffineAffineOpenCover firstCoordinates (ULift.{u} ℤ)).openCover
    (projectiveSpaceOverAffineAffineOpenCover secondCoordinates (ULift.{u} ℤ)).openCover
    (terminal.from (projectiveSpaceOverAffine firstCoordinates (ULift.{u} ℤ)))
    (terminal.from (projectiveSpaceOverAffine secondCoordinates (ULift.{u} ℤ))) (firstCoordinate, secondCoordinate)

set_option backward.isDefEq.respectTransparency.types false in
/-- Inside the `(firstCoordinate, secondCoordinate)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`, the locus where the `targetFirst`-th and `targetSecond`-th
homogeneous coordinates of the two factors do not vanish is the basic open of the chart
section `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)`. -/
lemma segreCover_f_preimage_inf (firstCoordinate : firstCoordinates) (secondCoordinate : secondCoordinates) (targetFirst : firstCoordinates) (targetSecond : secondCoordinates) :
    (segreCover firstCoordinates secondCoordinates).f (firstCoordinate, secondCoordinate) ⁻¹ᵁ
        (pullback.fst (terminal.from (projectiveSpaceOverAffine firstCoordinates (ULift.{u} ℤ)))
            (terminal.from (projectiveSpaceOverAffine secondCoordinates (ULift.{u} ℤ))) ⁻¹ᵁ
          basicOpen (homogeneousSubmodule firstCoordinates (ULift.{u} ℤ)) (MvPolynomial.X targetFirst) ⊓
        pullback.snd (terminal.from (projectiveSpaceOverAffine firstCoordinates (ULift.{u} ℤ)))
            (terminal.from (projectiveSpaceOverAffine secondCoordinates (ULift.{u} ℤ))) ⁻¹ᵁ
          basicOpen (homogeneousSubmodule secondCoordinates (ULift.{u} ℤ)) (MvPolynomial.X targetSecond)) =
      ((segreCover firstCoordinates secondCoordinates).X (firstCoordinate, secondCoordinate)).basicOpen (segreChartSection firstCoordinate secondCoordinate (targetFirst, targetSecond)) := by
  have e1 : (segreCover firstCoordinates secondCoordinates).f (firstCoordinate, secondCoordinate) ⁻¹ᵁ
      (pullback.fst (terminal.from (projectiveSpaceOverAffine firstCoordinates (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine secondCoordinates (ULift.{u} ℤ))) ⁻¹ᵁ
        basicOpen (homogeneousSubmodule firstCoordinates (ULift.{u} ℤ)) (MvPolynomial.X targetFirst)) =
      ((segreCover firstCoordinates secondCoordinates).X (firstCoordinate, secondCoordinate)).basicOpen
        (((Scheme.ΓSpecIso _).inv ≫ (segreCoverFst firstCoordinate secondCoordinate).appTop).hom
          (awayXRatio (ULift.{u} ℤ) firstCoordinate targetFirst)) := by
    rw [← Scheme.Hom.comp_preimage, ← segreCoverFst_awayι, Scheme.Hom.comp_preimage,
      awayι_preimage_basicOpen _ (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) firstCoordinate) Nat.one_pos
        (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) targetFirst) Nat.one_pos,
      isLocalizationElem_X]
    refine Eq.trans (congrArg (segreCoverFst firstCoordinate secondCoordinate ⁻¹ᵁ ·) (basicOpen_eq_of_affine
      (R := CommRingCat.of (Away (homogeneousSubmodule firstCoordinates (ULift.{u} ℤ)) (MvPolynomial.X firstCoordinate)))
      (awayXRatio (ULift.{u} ℤ) firstCoordinate targetFirst)).symm) ?_
    exact Scheme.preimage_basicOpen _ _
  have e2 : (segreCover firstCoordinates secondCoordinates).f (firstCoordinate, secondCoordinate) ⁻¹ᵁ
      (pullback.snd (terminal.from (projectiveSpaceOverAffine firstCoordinates (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine secondCoordinates (ULift.{u} ℤ))) ⁻¹ᵁ
        basicOpen (homogeneousSubmodule secondCoordinates (ULift.{u} ℤ)) (MvPolynomial.X targetSecond)) =
      ((segreCover firstCoordinates secondCoordinates).X (firstCoordinate, secondCoordinate)).basicOpen
        (((Scheme.ΓSpecIso _).inv ≫ (segreCoverSnd firstCoordinate secondCoordinate).appTop).hom
          (awayXRatio (ULift.{u} ℤ) secondCoordinate targetSecond)) := by
    rw [← Scheme.Hom.comp_preimage, ← segreCoverSnd_awayι, Scheme.Hom.comp_preimage,
      awayι_preimage_basicOpen _ (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) secondCoordinate) Nat.one_pos
        (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) targetSecond) Nat.one_pos,
      isLocalizationElem_X]
    refine Eq.trans (congrArg (segreCoverSnd firstCoordinate secondCoordinate ⁻¹ᵁ ·) (basicOpen_eq_of_affine
      (R := CommRingCat.of (Away (homogeneousSubmodule secondCoordinates (ULift.{u} ℤ)) (MvPolynomial.X secondCoordinate)))
      (awayXRatio (ULift.{u} ℤ) secondCoordinate targetSecond)).symm) ?_
    exact Scheme.preimage_basicOpen _ _
  have hs : segreChartSection firstCoordinate secondCoordinate (targetFirst, targetSecond) =
      ((Scheme.ΓSpecIso _).inv ≫ (segreCoverFst firstCoordinate secondCoordinate).appTop).hom
          (awayXRatio (ULift.{u} ℤ) firstCoordinate targetFirst) *
        ((Scheme.ΓSpecIso _).inv ≫ (segreCoverSnd firstCoordinate secondCoordinate).appTop).hom
          (awayXRatio (ULift.{u} ℤ) secondCoordinate targetSecond) := rfl
  rw [hs, Scheme.basicOpen_mul, ← e1, ← e2]
  rfl

/-- Inside the `(firstCoordinate, secondCoordinate)`-chart of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`, the preimage under the Segre morphism of the
locus where the homogeneous coordinate `W_{targetFirst,targetSecond}` does not vanish is the basic open of the chart
section `(Xₖ / Xᵢ) · (Yₗ / Yⱼ)`. -/
lemma segreCover_f_preimage_segre_preimage (firstCoordinate : firstCoordinates) (secondCoordinate : secondCoordinates) (targetFirst : firstCoordinates) (targetSecond : secondCoordinates) :
    (segreCover firstCoordinates secondCoordinates).f (firstCoordinate, secondCoordinate) ⁻¹ᵁ (segre firstCoordinates secondCoordinates ⁻¹ᵁ
        basicOpen (homogeneousSubmodule (firstCoordinates × secondCoordinates) (ULift.{u} ℤ)) (MvPolynomial.X (targetFirst, targetSecond))) =
      ((segreCover firstCoordinates secondCoordinates).X (firstCoordinate, secondCoordinate)).basicOpen (segreChartSection firstCoordinate secondCoordinate (targetFirst, targetSecond)) := by
  rw [← Scheme.Hom.comp_preimage, segreCover_f_comp_segre, segreChartHom,
    fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.one_pos
      (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (targetFirst, targetSecond)),
    ProjectiveSpace.evalSections_X]

/-- **The preimage of element standard open under the Segre morphism.** The locus in
`ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` where the homogeneous coordinate `W_{targetFirst,targetSecond}` of `ℙ^(firstCoordinates×secondCoordinates)_ℤ` does not vanish is
the product of the loci where `Xₖ` and `Yₗ` do not vanish. -/
theorem segre_preimage_basicOpen (targetFirst : firstCoordinates) (targetSecond : secondCoordinates) :
    segre firstCoordinates secondCoordinates ⁻¹ᵁ basicOpen (homogeneousSubmodule (firstCoordinates × secondCoordinates) (ULift.{u} ℤ))
        (MvPolynomial.X (targetFirst, targetSecond)) =
      pullback.fst (terminal.from (projectiveSpaceOverAffine firstCoordinates (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine secondCoordinates (ULift.{u} ℤ))) ⁻¹ᵁ
        basicOpen (homogeneousSubmodule firstCoordinates (ULift.{u} ℤ)) (MvPolynomial.X targetFirst) ⊓
      pullback.snd (terminal.from (projectiveSpaceOverAffine firstCoordinates (ULift.{u} ℤ)))
          (terminal.from (projectiveSpaceOverAffine secondCoordinates (ULift.{u} ℤ))) ⁻¹ᵁ
        basicOpen (homogeneousSubmodule secondCoordinates (ULift.{u} ℤ)) (MvPolynomial.X targetSecond) := by
  refine Scheme.Opens.ext_of_openCover (segreCover firstCoordinates secondCoordinates) fun chartPair ↦ ?_
  obtain ⟨firstCoordinate, secondCoordinate⟩ := chartPair
  rw [segreCover_f_preimage_segre_preimage, segreCover_f_preimage_inf]

/-- The preimage under the Segre morphism of the locus where `W_{targetFirst,targetSecond}` does not vanish is the
`(targetFirst, targetSecond)`-chart of the standard cover of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ`. -/
lemma opensRange_segreCover_f_eq_preimage (targetFirst : firstCoordinates) (targetSecond : secondCoordinates) :
    ((segreCover firstCoordinates secondCoordinates).f (targetFirst, targetSecond)).opensRange =
      segre firstCoordinates secondCoordinates ⁻¹ᵁ basicOpen (homogeneousSubmodule (firstCoordinates × secondCoordinates) (ULift.{u} ℤ))
        (MvPolynomial.X (targetFirst, targetSecond)) := by
  rw [segre_preimage_basicOpen, opensRange_segreCover_f]

/-- **The Segre morphism is element closed immersion.**

Being element closed immersion is Zariski-local on the target, so it suffices to check this over the
standard opens `D₊(W_{targetFirst,targetSecond})` of `ℙ^(firstCoordinates×secondCoordinates)_ℤ`. The preimage of `D₊(W_{targetFirst,targetSecond})` is the chart
`D₊(Xₖ) ×_ℤ D₊(Yₗ)`, which is the spectrum of `ℤ[Xᵣ/Xₖ] ⊗_ℤ ℤ[Yₛ/Yₗ]`, and on it the Segre
morphism is the spectrum of the ring map sending `W_{integer,s} / W_{targetFirst,targetSecond}` to
`(Xᵣ / Xₖ) ⊗ (Yₛ / Yₗ)`, which is surjective. -/
instance isClosedImmersion_segre : IsClosedImmersion (segre firstCoordinates secondCoordinates) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun coordinatePair : firstCoordinates × secondCoordinates ↦ basicOpen (homogeneousSubmodule (firstCoordinates × secondCoordinates) (ULift.{u} ℤ))
      (MvPolynomial.X coordinatePair))
    (iSup_basicOpen_eq_top _ _
      (toIdeal_irrelevant_homogeneousSubmodule (firstCoordinates × secondCoordinates) (ULift.{u} ℤ)).le) ?_
  rintro ⟨targetFirst, targetSecond⟩
  have hgen : Subring.closure {sectionValue : Γ((segreCover firstCoordinates secondCoordinates).X (targetFirst, targetSecond), ⊤) | ∃ identification : ℕ,
      ∃ element ∈ homogeneousSubmodule (firstCoordinates × secondCoordinates) (ULift.{u} ℤ) (identification • 1),
        ProjectiveSpace.evalSections (segreChartSection targetFirst targetSecond) element = sectionValue} = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← closure_range_segreChartSection_eq_top targetFirst targetSecond]
    refine Subring.closure_le.mpr ?_
    rintro _ ⟨coordinatePair, rfl⟩
    exact Subring.subset_closure ⟨1, MvPolynomial.X coordinatePair,
      by simpa using X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinatePair,
      ProjectiveSpace.evalSections_X _ _⟩
  obtain ⟨chartMap, hq, hqw⟩ := exists_isClosedImmersion_of_fromOfGlobalSections
    (homogeneousSubmodule (firstCoordinates × secondCoordinates) (ULift.{u} ℤ))
    (ProjectiveSpace.evalSections (segreChartSection targetFirst targetSecond))
    (ProjectiveSpace.map_irrelevant_evalSections_eq_top _
      (span_range_segreChartSection_eq_top targetFirst targetSecond))
    Nat.one_pos (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (targetFirst, targetSecond))
    (by rw [ProjectiveSpace.evalSections_X, segreChartSection_self]) hgen
  have identification : Arrow.mk (segre firstCoordinates secondCoordinates ∣_ (awayι (homogeneousSubmodule (firstCoordinates × secondCoordinates) (ULift.{u} ℤ))
      (MvPolynomial.X (targetFirst, targetSecond)) (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (targetFirst, targetSecond))
      Nat.one_pos).opensRange) ≅ Arrow.mk chartMap :=
    morphismRestrictArrowIso (segre firstCoordinates secondCoordinates) chartMap
      ((segreCover_f_comp_segre targetFirst targetSecond).trans hqw.symm)
      (by rw [opensRange_awayι, ← opensRange_segreCover_f_eq_preimage])
  have restrictedImmersion : IsClosedImmersion (segre firstCoordinates secondCoordinates ∣_ (awayι (homogeneousSubmodule (firstCoordinates × secondCoordinates) (ULift.{u} ℤ))
      (MvPolynomial.X (targetFirst, targetSecond)) (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) (targetFirst, targetSecond))
      Nat.one_pos).opensRange) :=
    (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion identification).mpr hq
  rwa [opensRange_awayι] at restrictedImmersion

end ClosedImmersion

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveSpace

variable (firstCoordinates secondCoordinates : Type u) (baseScheme : Scheme.{u})

/-- The morphism `ℙ(firstCoordinates; baseScheme) ×_S ℙ(secondCoordinates; baseScheme) ⟶ ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` to the product of the integral models,
induced by the two maps `ProjectiveSpace.toIntegralModel` to the integral models. -/
def prodToIntegralModel :
    pullback (ℙ(firstCoordinates; baseScheme) ↘ baseScheme) (ℙ(secondCoordinates; baseScheme) ↘ baseScheme) ⟶
      pullback (terminal.from (Proj.projectiveSpaceOverAffine firstCoordinates (ULift.{u} ℤ)))
        (terminal.from (Proj.projectiveSpaceOverAffine secondCoordinates (ULift.{u} ℤ))) :=
  pullback.lift (pullback.fst _ _ ≫ toIntegralModel firstCoordinates baseScheme) (pullback.snd _ _ ≫ toIntegralModel secondCoordinates baseScheme)
    (terminal.hom_ext _ _)

@[reassoc (attr := simp)]
lemma prodToIntegralModel_fst :
    prodToIntegralModel firstCoordinates secondCoordinates baseScheme ≫ pullback.fst _ _ = pullback.fst _ _ ≫ toIntegralModel firstCoordinates baseScheme :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma prodToIntegralModel_snd :
    prodToIntegralModel firstCoordinates secondCoordinates baseScheme ≫ pullback.snd _ _ = pullback.snd _ _ ≫ toIntegralModel secondCoordinates baseScheme :=
  pullback.lift_snd _ _ _

/-- `ℙ(firstCoordinates; baseScheme) ×_S ℙ(secondCoordinates; baseScheme)` is the base change of `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ` along the structure morphism
of `baseScheme`. -/
lemma isPullback_prodToIntegralModel :
    IsPullback (pullback.fst (ℙ(firstCoordinates; baseScheme) ↘ baseScheme) (ℙ(secondCoordinates; baseScheme) ↘ baseScheme) ≫ (ℙ(firstCoordinates; baseScheme) ↘ baseScheme))
      (prodToIntegralModel firstCoordinates secondCoordinates baseScheme) (terminal.from baseScheme)
      (terminal.from (pullback
        (terminal.from (Proj.projectiveSpaceOverAffine firstCoordinates (ULift.{u} ℤ)))
        (terminal.from (Proj.projectiveSpaceOverAffine secondCoordinates (ULift.{u} ℤ))))) := by
  have pullbackSquare := IsPullback.baseChange_pullback' (isPullback_over_toIntegralModel firstCoordinates baseScheme)
    (isPullback_over_toIntegralModel secondCoordinates baseScheme)
    (IsPullback.of_hasPullback (ℙ(firstCoordinates; baseScheme) ↘ baseScheme) (ℙ(secondCoordinates; baseScheme) ↘ baseScheme))
    (IsPullback.of_hasPullback _ _) (prodToIntegralModel_fst firstCoordinates secondCoordinates baseScheme) (prodToIntegralModel_snd firstCoordinates secondCoordinates baseScheme)
  rwa [terminal.hom_ext (pullback.fst
    (terminal.from (Proj.projectiveSpaceOverAffine firstCoordinates (ULift.{u} ℤ)))
    (terminal.from (Proj.projectiveSpaceOverAffine secondCoordinates (ULift.{u} ℤ))) ≫ terminal.from _)
    (terminal.from _)] at pullbackSquare

/-- **The relative Segre morphism** `ℙ(firstCoordinates; baseScheme) ×_S ℙ(secondCoordinates; baseScheme) ⟶ ℙ(firstCoordinates × secondCoordinates; baseScheme)`, obtained from the
Segre morphism `ℙⁿ_ℤ ×_ℤ ℙᵐ_ℤ ⟶ ℙ^(firstCoordinates×secondCoordinates)_ℤ` of the integral models by base change along the
structure morphism of `baseScheme`. -/
def segre : pullback (ℙ(firstCoordinates; baseScheme) ↘ baseScheme) (ℙ(secondCoordinates; baseScheme) ↘ baseScheme) ⟶ ℙ(firstCoordinates × secondCoordinates; baseScheme) :=
  pullback.lift (pullback.fst _ _ ≫ (ℙ(firstCoordinates; baseScheme) ↘ baseScheme))
    (prodToIntegralModel firstCoordinates secondCoordinates baseScheme ≫ Proj.segre firstCoordinates secondCoordinates) (terminal.hom_ext _ _)

/-- The relative Segre morphism is a morphism over `baseScheme`. -/
@[reassoc (attr := simp)]
lemma segre_over :
    segre firstCoordinates secondCoordinates baseScheme ≫ (ℙ(firstCoordinates × secondCoordinates; baseScheme) ↘ baseScheme) = pullback.fst _ _ ≫ (ℙ(firstCoordinates; baseScheme) ↘ baseScheme) :=
  pullback.lift_fst _ _ _

/-- The relative Segre morphism is compatible with the Segre morphism of the integral models. -/
@[reassoc (attr := simp)]
lemma segre_toIntegralModel :
    segre firstCoordinates secondCoordinates baseScheme ≫ toIntegralModel (firstCoordinates × secondCoordinates) baseScheme = prodToIntegralModel firstCoordinates secondCoordinates baseScheme ≫ Proj.segre firstCoordinates secondCoordinates :=
  pullback.lift_snd _ _ _

/-- **The relative Segre morphism is the base change of the Segre morphism of the integral
models** along the map `ℙ(firstCoordinates × secondCoordinates; baseScheme) ⟶ ℙ^(firstCoordinates×secondCoordinates)_ℤ`. -/
lemma isPullback_segre :
    IsPullback (prodToIntegralModel firstCoordinates secondCoordinates baseScheme) (segre firstCoordinates secondCoordinates baseScheme) (Proj.segre firstCoordinates secondCoordinates) (toIntegralModel (firstCoordinates × secondCoordinates) baseScheme) := by
  refine IsPullback.of_bot ?_ (segre_toIntegralModel firstCoordinates secondCoordinates baseScheme).symm
    (isPullback_over_toIntegralModel (firstCoordinates × secondCoordinates) baseScheme).flip
  rw [segre_over, terminal.hom_ext (Proj.segre firstCoordinates secondCoordinates ≫
    terminal.from (Proj.projectiveSpaceOverAffine (firstCoordinates × secondCoordinates) (ULift.{u} ℤ))) (terminal.from _)]
  exact (isPullback_prodToIntegralModel firstCoordinates secondCoordinates baseScheme).flip

/-- **The relative Segre morphism is a closed immersion**, being the base change of the Segre
morphism of the integral models. -/
instance isClosedImmersion_segre : IsClosedImmersion (segre firstCoordinates secondCoordinates baseScheme) :=
  MorphismProperty.of_isPullback (isPullback_segre firstCoordinates secondCoordinates baseScheme) inferInstance

end AlgebraicGeometry.ProjectiveSpace
