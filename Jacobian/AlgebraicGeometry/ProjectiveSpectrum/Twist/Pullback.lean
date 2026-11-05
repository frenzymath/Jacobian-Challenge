import Jacobian.AlgebraicGeometry.Modules.RestrictionIsomorphism
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist
import Jacobian.RingTheory.GradedAlgebra.HomogeneousLocalization.DegreePartMap
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Pullback maps for twisting sheaves

A graded ring homomorphism defining a morphism of projective spectra induces
canonical maps on twisting sheaves. They are induced by maps on homogeneous
fractions, identify the zeroth twists with the structure sheaves, and commute
with multiplication by homogeneous elements.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace HomogeneousIdeal HomogeneousLocalization

namespace AlgebraicGeometry

variable {sourceRing targetRing sourceSubobjects targetSubobjects : Type u}
  [CommRing sourceRing] [CommRing targetRing]
  [SetLike sourceSubobjects sourceRing] [AddSubgroupClass sourceSubobjects sourceRing]
  [SetLike targetSubobjects targetRing] [AddSubgroupClass targetSubobjects targetRing]
  {sourceGrading : ℕ → sourceSubobjects} {targetGrading : ℕ → targetSubobjects}
  [GradedRing sourceGrading] [GradedRing targetGrading]
  (gradedMap : sourceGrading →+*ᵍ targetGrading)
  (irrelevantLE : targetGrading₊ ≤ sourceGrading₊.map gradedMap)

namespace ProjectiveSpectrum.Twist

private def mapValues (degree : ℤ) (openSubset : (Proj sourceGrading).Opens)
    (values : ∀ point : openSubset, fiber sourceGrading degree point.1)
    (point : Proj.map gradedMap irrelevantLE ⁻¹ᵁ openSubset) :
    fiber targetGrading degree point.1 :=
  degreePart.localRingHom gradedMap _ point.1.asHomogeneousIdeal.toIdeal rfl degree
    (values ⟨ProjectiveSpectrum.comap gradedMap irrelevantLE point.1, point.2⟩)

private lemma isLocallyFraction_mapValues (degree : ℤ)
    (openSubset : (Proj sourceGrading).Opens)
    (values : ∀ point : openSubset, fiber sourceGrading degree point.1)
    (locallyFraction : (isLocallyFraction sourceGrading degree).pred values) :
    (isLocallyFraction targetGrading degree).pred
      (mapValues gradedMap irrelevantLE degree openSubset values) := by
  rintro ⟨point, pointMem⟩
  obtain ⟨neighborhood, pointMemNeighborhood, inclusion, numeratorDegree, denominatorDegree,
    degreeEquation, numerator, denominator, denominatorNotMem, fractionEquation⟩ :=
    locallyFraction ⟨ProjectiveSpectrum.comap gradedMap irrelevantLE point, pointMem⟩
  refine ⟨neighborhood.comap (ProjectiveSpectrum.comap gradedMap irrelevantLE) ⊓
    (Proj.map gradedMap irrelevantLE ⁻¹ᵁ openSubset),
    ⟨pointMemNeighborhood, pointMem⟩, Opens.infLERight _ _, numeratorDegree,
    denominatorDegree, degreeEquation, gradedMap.gradedAddHom numeratorDegree numerator,
    gradedMap.gradedAddHom denominatorDegree denominator,
    fun ⟨_, membership⟩ ↦ denominatorNotMem ⟨_, membership.1⟩,
    fun ⟨targetPoint, membership⟩ ↦ ?_⟩
  let nativePoint : ProjectiveSpectrum targetGrading := targetPoint
  let sourcePoint : neighborhood :=
    ⟨ProjectiveSpectrum.comap gradedMap irrelevantLE nativePoint, membership.1⟩
  have localEquation : values (inclusion sourcePoint) =
      degreePart.mk numerator denominator (denominatorNotMem sourcePoint) degreeEquation :=
    fractionEquation sourcePoint
  change degreePart.localRingHom gradedMap _ nativePoint.asHomogeneousIdeal.toIdeal rfl degree
    (values (inclusion sourcePoint)) = _
  exact (congrArg
    (degreePart.localRingHom gradedMap _ nativePoint.asHomogeneousIdeal.toIdeal rfl degree)
    localEquation).trans
      (degreePart.localRingHom_mk gradedMap _ nativePoint.asHomogeneousIdeal.toIdeal rfl
        numerator denominator (denominatorNotMem sourcePoint) degreeEquation)

private def mapPresheafInAb (degree : ℤ) :
    presheafInAb sourceGrading degree ⟶
      ((Scheme.Modules.pushforward (Proj.map gradedMap irrelevantLE)).obj
        (Proj.twist targetGrading degree)).presheaf where
  app openSubset := AddCommGrpCat.ofHom
    { toFun localSection := ⟨mapValues gradedMap irrelevantLE degree openSubset.unop localSection.1,
        isLocallyFraction_mapValues gradedMap irrelevantLE degree openSubset.unop
          localSection.1 localSection.2⟩
      map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
      map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _) }
  naturality _ _ _ := rfl

end ProjectiveSpectrum.Twist

namespace Proj

open Scheme.Modules ProjectiveSpectrum.Twist

/-- The map on twisting sheaves obtained by applying the graded homomorphism
to homogeneous numerators and denominators. -/
def twistToPushforward (degree : ℤ) :
    twist sourceGrading degree ⟶
      (pushforward (Proj.map gradedMap irrelevantLE)).obj (twist targetGrading degree) :=
  ⟨PresheafOfModules.homMk (mapPresheafInAb gradedMap irrelevantLE degree)
    fun openSubset scalar localSection ↦ by
      refine Subtype.ext (funext fun point ↦ ?_)
      let nativePoint : ProjectiveSpectrum targetGrading := point.1
      exact (degreePart.localRingHom gradedMap _ nativePoint.asHomogeneousIdeal.toIdeal
        rfl degree).map_smulₛₗ _ _⟩

/-- The canonical comparison from the pullback of a twist to the corresponding twist. -/
def pullbackTwistMap (degree : ℤ) :
    (pullback (Proj.map gradedMap irrelevantLE)).obj (twist sourceGrading degree) ⟶
      twist targetGrading degree :=
  ((pullbackPushforwardAdjunction (Proj.map gradedMap irrelevantLE)).homEquiv _ _).symm
    (twistToPushforward gradedMap irrelevantLE degree)

@[simp]
lemma homEquiv_pullbackTwistMap (degree : ℤ) :
    (pullbackPushforwardAdjunction (Proj.map gradedMap irrelevantLE)).homEquiv _ _
        (pullbackTwistMap gradedMap irrelevantLE degree) =
      twistToPushforward gradedMap irrelevantLE degree :=
  Equiv.apply_symm_apply _ _

@[simp]
lemma twistToPushforward_app_apply (degree : ℤ) (openSubset : (Proj sourceGrading).Opens)
    (localSection : Γ(twist sourceGrading degree, openSubset))
    (point : Proj.map gradedMap irrelevantLE ⁻¹ᵁ openSubset) :
    ((twistToPushforward gradedMap irrelevantLE degree).app openSubset localSection).1 point =
      degreePart.localRingHom gradedMap _ point.1.asHomogeneousIdeal.toIdeal rfl degree
        (localSection.1 ⟨ProjectiveSpectrum.comap gradedMap irrelevantLE point.1, point.2⟩) :=
  rfl

/-- The comparison in degree zero agrees with the canonical map of structure sheaves. -/
lemma unitToTwistZero_twistToPushforward :
    unitToTwistZero (𝒜 := sourceGrading) ≫ twistToPushforward gradedMap irrelevantLE 0 =
      SheafOfModules.unitToPushforwardObjUnit (Proj.map gradedMap irrelevantLE).toRingCatSheafHom ≫
        (pushforward (Proj.map gradedMap irrelevantLE)).map
          (unitToTwistZero (𝒜 := targetGrading)) := by
  refine Scheme.Modules.hom_ext _ _ fun openSubset ↦ ?_
  refine ConcreteCategory.hom_ext _ _ fun localSection ↦ ?_
  refine Subtype.ext (funext fun point ↦ ?_)
  let nativePoint : ProjectiveSpectrum targetGrading := point.1
  exact degreePart.localRingHom_zeroEquiv gradedMap _ nativePoint.asHomogeneousIdeal.toIdeal rfl _

/-- Pulling back `𝒪 ≅ 𝒪(0)` commutes with the twisting-sheaf comparison. -/
lemma pullback_unitToTwistZero_pullbackTwistMap :
    (pullback (Proj.map gradedMap irrelevantLE)).map
        (unitToTwistZero (𝒜 := sourceGrading)) ≫
        pullbackTwistMap gradedMap irrelevantLE 0 =
      (pullbackObjUnitIso (Proj.map gradedMap irrelevantLE)).hom ≫
        unitToTwistZero (𝒜 := targetGrading) := by
  apply ((pullbackPushforwardAdjunction (Proj.map gradedMap irrelevantLE)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, homEquiv_pullbackTwistMap,
    Adjunction.homEquiv_naturality_right]
  rw [show (pullbackPushforwardAdjunction (Proj.map gradedMap irrelevantLE)).homEquiv _ _
      (pullbackObjUnitIso (Proj.map gradedMap irrelevantLE)).hom =
    SheafOfModules.unitToPushforwardObjUnit
      (Proj.map gradedMap irrelevantLE).toRingCatSheafHom from
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _]
  exact unitToTwistZero_twistToPushforward gradedMap irrelevantLE

instance isIso_pullbackTwistMap_zero : IsIso (pullbackTwistMap gradedMap irrelevantLE 0) := by
  haveI : IsIso ((pullback (Proj.map gradedMap irrelevantLE)).map
      (unitToTwistZero (𝒜 := sourceGrading))) :=
    ((pullback (Proj.map gradedMap irrelevantLE)).mapIso
      (unitIsoTwistZero (𝒜 := sourceGrading))).isIso_hom
  haveI : IsIso (unitToTwistZero (𝒜 := targetGrading)) :=
    (unitIsoTwistZero (𝒜 := targetGrading)).isIso_hom
  exact IsIso.of_isIso_fac_left
    (pullback_unitToTwistZero_pullbackTwistMap gradedMap irrelevantLE)

/-- Multiplication by a homogeneous element commutes with the map on twisting sheaves. -/
lemma twistMul_twistToPushforward (degree : ℤ) {elementDegree : ℕ} {element : sourceRing}
    (homogeneous : element ∈ sourceGrading elementDegree) :
    twistMul (𝒜 := sourceGrading) degree homogeneous ≫
        twistToPushforward gradedMap irrelevantLE (degree + elementDegree) =
      twistToPushforward gradedMap irrelevantLE degree ≫
        (pushforward (Proj.map gradedMap irrelevantLE)).map
          (twistMul (𝒜 := targetGrading) degree (gradedMap.map_mem homogeneous)) := by
  refine Scheme.Modules.hom_ext _ _ fun openSubset ↦ ?_
  refine ConcreteCategory.hom_ext _ _ fun localSection ↦ ?_
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply]
  refine Subtype.ext (funext fun point ↦ Subtype.ext ?_)
  let nativePoint : ProjectiveSpectrum targetGrading := point.1
  let nativeSourcePoint : ProjectiveSpectrum sourceGrading :=
    ProjectiveSpectrum.comap gradedMap irrelevantLE nativePoint
  let sourcePoint : openSubset := ⟨nativeSourcePoint, point.2⟩
  let localizationMap : Localization.AtPrime nativeSourcePoint.asHomogeneousIdeal.toIdeal →+*
      Localization.AtPrime nativePoint.asHomogeneousIdeal.toIdeal :=
    Localization.localRingHom _ _ gradedMap.toRingHom rfl
  have elementImage : localizationMap (Localization.mk element 1) =
      Localization.mk (gradedMap element) 1 := by
    dsimp only [localizationMap]
    rw [Localization.localRingHom_mk]
    simp only [GradedRingHom.coe_toRingHom]
    refine congrArg (Localization.mk (gradedMap element)) (Subtype.ext ?_)
    change gradedMap (1 : sourceRing) = (1 : targetRing)
    exact map_one gradedMap
  change localizationMap
      ((localSection.1 sourcePoint : Localization.AtPrime nativeSourcePoint.asHomogeneousIdeal.toIdeal) *
        Localization.mk element 1) =
    localizationMap (localSection.1 sourcePoint) * Localization.mk (gradedMap element) 1
  rw [map_mul, elementImage]

/-- Pullback comparisons commute with multiplication by homogeneous elements. -/
lemma pullback_twistMul_pullbackTwistMap (degree : ℤ) {elementDegree : ℕ}
    {element : sourceRing} (homogeneous : element ∈ sourceGrading elementDegree) :
    (pullback (Proj.map gradedMap irrelevantLE)).map
        (twistMul (𝒜 := sourceGrading) degree homogeneous) ≫
        pullbackTwistMap gradedMap irrelevantLE (degree + elementDegree) =
      pullbackTwistMap gradedMap irrelevantLE degree ≫
        twistMul (𝒜 := targetGrading) degree (gradedMap.map_mem homogeneous) := by
  apply ((pullbackPushforwardAdjunction (Proj.map gradedMap irrelevantLE)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, homEquiv_pullbackTwistMap,
    Adjunction.homEquiv_naturality_right, homEquiv_pullbackTwistMap]
  exact twistMul_twistToPushforward gradedMap irrelevantLE degree homogeneous

private lemma isIso_restrict_pullback_twistMul (degree : ℤ) {element : sourceRing}
    (homogeneous : element ∈ sourceGrading 1) :
    IsIso ((restrictFunctor (basicOpen targetGrading (gradedMap element)).ι).map
      ((pullback (Proj.map gradedMap irrelevantLE)).map
        (twistMul (𝒜 := sourceGrading) degree homogeneous))) := by
  let schemeMap : Proj targetGrading ⟶ Proj sourceGrading := Proj.map gradedMap irrelevantLE
  let openSubset : (Proj sourceGrading).Opens := basicOpen sourceGrading element
  have restrictedIso := isIso_restrict_pullback_map schemeMap
    (twistMul (𝒜 := sourceGrading) degree homogeneous) openSubset
  simpa only [schemeMap, openSubset, Proj.map_preimage_basicOpen] using restrictedIso

/-- The pullback comparison is an isomorphism wherever the image of a homogeneous
element of degree one does not vanish. -/
lemma isIso_restrict_pullbackTwistMap (degree : ℤ) {element : sourceRing}
    (homogeneous : element ∈ sourceGrading 1) :
    IsIso ((restrictFunctor (basicOpen targetGrading (gradedMap element)).ι).map
      (pullbackTwistMap gradedMap irrelevantLE degree)) := by
  let restriction := restrictFunctor (basicOpen targetGrading (gradedMap element)).ι
  have multiplicationSquare (degree : ℤ) := congrArg restriction.map
    (pullback_twistMul_pullbackTwistMap gradedMap irrelevantLE degree homogeneous)
  simp only [Functor.map_comp] at multiplicationSquare
  induction degree using Int.induction_on with
  | zero => infer_instance
  | succ natural inductionHypothesis =>
    haveI := inductionHypothesis
    haveI := isIso_restrict_pullback_twistMul gradedMap irrelevantLE (natural : ℤ) homogeneous
    exact IsIso.of_isIso_fac_left (multiplicationSquare natural)
  | pred natural inductionHypothesis =>
    haveI := inductionHypothesis
    haveI := isIso_restrict_pullback_twistMul gradedMap irrelevantLE
      (-(natural : ℤ) - 1) homogeneous
    haveI : IsIso (restriction.map (pullbackTwistMap gradedMap irrelevantLE
        (-(natural : ℤ) - 1 + ((1 : ℕ) : ℤ)))) := by
      change IsIso ((restrictFunctor (basicOpen targetGrading (gradedMap element)).ι).map
        (pullbackTwistMap gradedMap irrelevantLE (-(natural : ℤ) - 1 + 1)))
      have degreeEquation : (-(natural : ℤ) - 1 + 1 : ℤ) = -natural := by omega
      exact Eq.mpr (congrArg
        (fun twistDegree : ℤ ↦ IsIso (restriction.map
          (pullbackTwistMap gradedMap irrelevantLE twistDegree)))
        degreeEquation) inductionHypothesis
    have square := multiplicationSquare (-(natural : ℤ) - 1)
    exact IsIso.of_isIso_fac_right square.symm

/-- Pullback preserves twisting sheaves if images of homogeneous elements of
degree one give a standard-open cover of the target projective spectrum. -/
lemma isIso_pullbackTwistMap (degree : ℤ)
    (degreeOneCover : ∀ point : Proj targetGrading,
      ∃ element ∈ sourceGrading 1, point ∈ basicOpen targetGrading (gradedMap element)) :
    IsIso (pullbackTwistMap gradedMap irrelevantLE degree) := by
  apply Hom.isIso_of_forall_bijective_app
  intro point
  obtain ⟨element, homogeneous, pointMem⟩ := degreeOneCover point
  haveI := isIso_restrict_pullbackTwistMap gradedMap irrelevantLE degree homogeneous
  exact ⟨basicOpen targetGrading (gradedMap element), pointMem,
    fun _ inclusion ↦ bijective_app_of_isIso_restrict _ inclusion⟩

/-- The pullback isomorphism of twists for a graded map whose degree-one
standard opens cover the target. -/
def pullbackTwistIso (degree : ℤ)
    (degreeOneCover : ∀ point : Proj targetGrading,
      ∃ element ∈ sourceGrading 1, point ∈ basicOpen targetGrading (gradedMap element)) :
    (pullback (Proj.map gradedMap irrelevantLE)).obj (twist sourceGrading degree) ≅
      twist targetGrading degree := by
  haveI := isIso_pullbackTwistMap gradedMap irrelevantLE degree degreeOneCover
  exact asIso (pullbackTwistMap gradedMap irrelevantLE degree)

end Proj

end AlgebraicGeometry
