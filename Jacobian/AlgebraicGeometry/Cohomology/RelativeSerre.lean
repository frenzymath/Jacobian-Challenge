import Jacobian.AlgebraicGeometry.Cohomology.FiniteDescent
import Jacobian.RingTheory.Finiteness.Semilinear
import Jacobian.AlgebraicGeometry.Cohomology.FiniteProjective
import Jacobian.AlgebraicGeometry.Cohomology.Finiteness
import Jacobian.AlgebraicGeometry.Cohomology.SerreVanishing
import Jacobian.AlgebraicGeometry.Modules.PullbackMonoidal
import Jacobian.AlgebraicGeometry.Modules.PullbackUnit
import Jacobian.AlgebraicGeometry.Modules.Sections
import Jacobian.AlgebraicGeometry.Modules.TensorEquivalence
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Twist
import Jacobian.AlgebraicGeometry.ProjectiveSpace.AffineTwist

/-!
# Relative projective cohomology

For a closed immersion into a finite relative projective space, affine base
change is controlled by the cartesian relative-projective-space square.
The coordinate lift remains a closed immersion, and pulling back a twisted
module agrees with twisting its pullback. These comparisons identify vanishing
on an affine base chart with vanishing of the corresponding twisted cohomology.
The affine comparison with polynomial projective space supplies finite
cohomology and Serre vanishing for coherent modules. Affine-local descent then
gives coherence of the zeroth direct image and uniform relative Serre vanishing.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A coherent module on a scheme finite over relative projective space over
an affine Noetherian base has finite cohomology over the coefficient ring. -/
theorem hasFiniteH_of_isFinite_relativeProjectiveSpace
    (coordinates : Type u) [Finite coordinates] (baseRing : CommRingCat.{u})
    [IsNoetherianRing baseRing] {sourceScheme : Scheme.{u}}
    (morphism : sourceScheme ⟶ ℙ(coordinates; Spec baseRing)) [IsFinite morphism]
    (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsFinitePresentation] :
    HasFiniteH (morphism ≫ ℙ(coordinates; Spec baseRing) ↘ Spec baseRing) moduleSheaf := by
  have finiteCohomology := hasFiniteH_of_isFinite_projectiveSpaceOverAffine
    coordinates baseRing (morphism ≫ (ProjectiveSpace.affineIso coordinates baseRing).hom)
    moduleSheaf
  simpa only [Category.assoc, ProjectiveSpace.affineIso_hom_over] using finiteCohomology

/-- Serre vanishing for a coherent module on a scheme finite over relative
projective space over an affine Noetherian base. -/
theorem exists_subsingleton_H_tensor_twistRestrict_of_isFinite
    (coordinates : Type u) [Finite coordinates] (baseRing : CommRingCat.{u})
    [IsNoetherianRing baseRing] {sourceScheme : Scheme.{u}}
    (morphism : sourceScheme ⟶ ℙ(coordinates; Spec baseRing)) [IsFinite morphism]
    (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsFinitePresentation] :
    ∃ bound : ℤ, ∀ twistDegree ≥ bound, ∀ degree : ℕ, 0 < degree →
      Subsingleton ((moduleSheaf ⊗ ProjectiveSpace.twistRestrict morphism twistDegree).H
        degree) := by
  obtain ⟨bound, vanishing⟩ := exists_subsingleton_H_tensor_pullback_twist_of_isFinite
    coordinates baseRing (morphism ≫ (ProjectiveSpace.affineIso coordinates baseRing).hom)
    moduleSheaf
  refine ⟨bound, fun twistDegree degreeBound degree positiveDegree ↦ ?_⟩
  let polynomialTwist := Proj.twist (MvPolynomial.homogeneousSubmodule coordinates baseRing)
    twistDegree
  let twistComparison :
      (pullback (morphism ≫ (ProjectiveSpace.affineIso coordinates baseRing).hom)).obj
          polynomialTwist ≅ ProjectiveSpace.twistRestrict morphism twistDegree :=
    (pullbackComp morphism (ProjectiveSpace.affineIso coordinates baseRing).hom).symm.app
        polynomialTwist ≪≫
      (pullback morphism).mapIso
        (ProjectiveSpace.pullbackAffineIsoTwistIso coordinates baseRing twistDegree)
  letI := vanishing twistDegree degreeBound degree positiveDegree
  exact (H.mapLinearEquiv (Iso.refl moduleSheaf ⊗ᵢ twistComparison.symm)
    degree).toEquiv.subsingleton

variable {Y Y' : Scheme.{u}} {n : Type u} [Finite n] {π : Y' ⟶ Y}
  {e : Y' ⟶ ℙ(n; Y)} [IsClosedImmersion e]

/-- The structure morphism of a closed subscheme of relative projective space is proper. -/
lemma isProper_of_comp_over (he : e ≫ ℙ(n; Y) ↘ Y = π) : IsProper π := by
  rw [← he]
  infer_instance

/-- The affine-base-change lift of a projective closed immersion. -/
def coordinateLift {R : CommRingCat.{u}} (he : e ≫ ℙ(n; Y) ↘ Y = π) (g : Spec R ⟶ Y) :
    Limits.pullback π g ⟶ ℙ(n; Spec R) :=
  ProjectiveSpace.liftBaseChange (pullback.snd π g) (pullback.fst π g ≫ e)
    (by rw [Category.assoc, he]; exact pullback.condition.symm)

/-- The affine-base-change lift remains a closed immersion. -/
lemma isClosedImmersion_coordinateLift {R : CommRingCat.{u}}
    (he : e ≫ ℙ(n; Y) ↘ Y = π) (g : Spec R ⟶ Y) :
    IsClosedImmersion (coordinateLift (π := π) he g) := by
  have w : pullback.snd π g ≫ g =
      (pullback.fst π g ≫ e) ≫ (ℙ(n; Y) ↘ Y) := by
    rw [Category.assoc, he]
    exact pullback.condition.symm
  have h : IsPullback (pullback.fst π g) (pullback.snd π g) (e ≫ ℙ(n; Y) ↘ Y) g := by
    rw [he]
    exact IsPullback.of_hasPullback π g
  exact MorphismProperty.of_isPullback
    (ProjectiveSpace.isPullback_liftBaseChange (pullback.snd π g) h w) inferInstance

/-- The coordinate lift has the expected structure morphism over the affine chart. -/
lemma coordinateLift_over {R : CommRingCat.{u}}
    (he : e ≫ ℙ(n; Y) ↘ Y = π) (g : Spec R ⟶ Y) :
    coordinateLift (π := π) he g ≫ ℙ(n; Spec R) ↘ Spec R = pullback.snd π g :=
  ProjectiveSpace.liftBaseChange_over (pullback.snd π g) (pullback.fst π g ≫ e) (by
    rw [Category.assoc, he]
    exact pullback.condition.symm)

/-- Base change of a twisted module is the twist of its base change. -/
def pullbackTensorTwistIso {baseRing : CommRingCat.{u}}
    (he : e ≫ ℙ(n; Y) ↘ Y = π) (baseMap : Spec baseRing ⟶ Y)
    (moduleSheaf : Y'.Modules) (degree : ℤ) :
    (Modules.pullback (pullback.fst π baseMap)).obj
        (moduleSheaf ⊗ ProjectiveSpace.twistRestrict e degree) ≅
  (Modules.pullback (pullback.fst π baseMap)).obj moduleSheaf ⊗
        ProjectiveSpace.twistRestrict (coordinateLift (π := π) he baseMap) degree :=
  (Functor.Monoidal.μIso (Modules.pullback (pullback.fst π baseMap)) moduleSheaf _).symm ≪≫
    (Iso.refl _ ⊗ᵢ (pullbackCompOfEq (pullback.fst π baseMap) e _
        (ProjectiveSpace.liftBaseChange_map _ _ _).symm _ ≪≫
      (pullbackCompOfEq (coordinateLift (π := π) he baseMap)
        (ProjectiveSpace.map n baseMap) _ rfl _).symm ≪≫
      (Modules.pullback (coordinateLift (π := π) he baseMap)).mapIso
        (ProjectiveSpace.pullbackMapTwistIso n baseMap degree)))

/-- On an affine base chart, a twisted higher direct image vanishes exactly when
the twisted cohomology of the base-changed module vanishes. -/
theorem isZero_restrict_higherDirectImage_tensorObj_twistRestrict_iff
    [HasInjectiveResolutions Y'.Modules] (he : e ≫ ℙ(n; Y) ↘ Y = π)
    (moduleSheaf : Y'.Modules) [moduleSheaf.IsQuasicoherent]
    {openSubset : Y.Opens} (affine : IsAffineOpen openSubset)
    (twistDegree : ℤ) (cohomologyDegree : ℕ) :
    IsZero (((higherDirectImage π cohomologyDegree).obj
      (moduleSheaf ⊗ ProjectiveSpace.twistRestrict e twistDegree)).restrict affine.fromSpec) ↔
      Subsingleton (((Modules.pullback (pullback.fst π affine.fromSpec)).obj moduleSheaf ⊗
        ProjectiveSpace.twistRestrict
          (coordinateLift (π := π) he affine.fromSpec) twistDegree).H cohomologyDegree) := by
  letI : IsProper π := isProper_of_comp_over he
  letI := isGrothendieckAbelian (Limits.pullback π affine.fromSpec)
  letI : (moduleSheaf ⊗ ProjectiveSpace.twistRestrict e twistDegree).IsQuasicoherent :=
    isQuasicoherent_tensorObj_of_isInvertible moduleSheaf _
  let comparison := pullbackTensorTwistIso he affine.fromSpec moduleSheaf twistDegree
  rw [isZero_restrict_higherDirectImage_iff_subsingleton_H]
  constructor
  · intro vanishing
    letI := vanishing
    exact (H.mapLinearEquiv comparison cohomologyDegree).surjective.subsingleton
  · intro vanishing
    letI := vanishing
    exact (H.mapLinearEquiv comparison.symm cohomologyDegree).surjective.subsingleton

/-- A local affine bound on the pulled-back cohomology gives relative Serre
vanishing after compact-open descent.  The affine bound is the native
projective-space input; this theorem supplies its geometric relative output. -/
theorem exists_isZero_higherDirectImage_tensorObj_twistRestrict_of_affine
    [CompactSpace Y] (he : e ≫ ℙ(n; Y) ↘ Y = π) (moduleSheaf : Y'.Modules)
    [moduleSheaf.IsQuasicoherent]
    (affineVanishing : ∀ (openSubset : Y.Opens) (affine : IsAffineOpen openSubset),
      ∃ bound : ℤ, ∀ degree ≥ bound, ∀ cohomologyDegree : ℕ,
        Subsingleton (((Modules.pullback (pullback.fst π affine.fromSpec)).obj moduleSheaf ⊗
          ProjectiveSpace.twistRestrict
            (coordinateLift (π := π) he affine.fromSpec) degree).H
          (cohomologyDegree + 1))) :
    ∃ bound : ℤ, ∀ degree ≥ bound, ∀ cohomologyDegree : ℕ,
      IsZero ((higherDirectImage π (cohomologyDegree + 1)).obj
        (moduleSheaf ⊗ ProjectiveSpace.twistRestrict e degree)) := by
  classical
  have hcov : ∀ point : Y, ∃ openSubset : Y.Opens, IsAffineOpen openSubset ∧ point ∈ openSubset :=
    fun point ↦ by
      obtain ⟨openSubset, affine, membership, -⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens)
          (show point ∈ (⊤ : Y.Opens) from trivial)
      exact ⟨openSubset, affine, membership⟩
  choose openSubset affine membership using hcov
  choose bound localBound using fun point ↦ affineVanishing (openSubset point) (affine point)
  obtain ⟨finitePoints, cover⟩ := isCompact_univ.elim_finite_subcover
    (fun point ↦ (openSubset point : Set Y)) (fun point ↦ (openSubset point).isOpen)
    (fun point _ ↦ Set.mem_iUnion.2 ⟨point, membership point⟩)
  obtain ⟨globalBound, boundAbove⟩ := (finitePoints.finite_toSet.image bound).bddAbove
  refine ⟨globalBound, fun degree degreeBound cohomologyDegree ↦
    isZero_of_forall_exists_isZero_restrict _ fun point ↦ ?_⟩
  obtain ⟨point', pointMembership, pointInOpen⟩ :=
    Set.mem_iUnion₂.1 (cover (Set.mem_univ point))
  refine ⟨openSubset point', pointInOpen, ?_⟩
  have vanishing :=
    (isZero_restrict_higherDirectImage_tensorObj_twistRestrict_iff he moduleSheaf
      (affine point') degree (cohomologyDegree + 1)).mpr
      (localBound point' degree
        ((boundAbove ⟨point', pointMembership, rfl⟩).trans degreeBound) cohomologyDegree)
  have openVanishing :=
    isZero_restrict_opensRange_of_isZero_restrict (affine point').fromSpec vanishing
  have affineRange : (affine point').fromSpec.opensRange = openSubset point' :=
    (affine point').opensRange_fromSpec
  exact affineRange ▸ openVanishing

/-- The zeroth direct image has finite presentation when every affine base
change has finite cohomology.  This is the finite-presentation endpoint used
by a native affine projective-space provider. -/
theorem isFinitePresentation_higherDirectImage_zero_of_affine_finiteH
    [IsLocallyNoetherian Y] [HasInjectiveResolutions Y'.Modules]
    (he : e ≫ ℙ(n; Y) ↘ Y = π) (moduleSheaf : Y'.Modules) [moduleSheaf.IsQuasicoherent]
    (finiteH : ∀ (openSubset : Y.Opens) (affine : IsAffineOpen openSubset),
      HasFiniteH (pullback.snd π affine.fromSpec)
        ((Modules.pullback (pullback.fst π affine.fromSpec)).obj moduleSheaf)) :
    ((higherDirectImage π 0).obj moduleSheaf).IsFinitePresentation := by
  have hProper : IsProper π := isProper_of_comp_over he
  let hP (openSubset : Y.Opens) (affine : IsAffineOpen openSubset) :
      ∃ presentation : (((higherDirectImage π 0).obj moduleSheaf).restrict affine.fromSpec).Presentation,
        presentation.IsFinite := by
    let baseMap := affine.fromSpec
    letI := isGrothendieckAbelian (Limits.pullback π baseMap)
    letI : IsNoetherianRing Γ(Y, openSubset) :=
      IsLocallyNoetherian.component_noetherian ⟨openSubset, affine⟩
    haveI : IsProper π := hProper
    haveI := isQuasicoherent_higherDirectImage π moduleSheaf 0
    let comparison := higherDirectImagePullbackIsoRestrict
      (IsPullback.of_hasPullback π baseMap) moduleSheaf 0
    obtain ⟨semilinearComparison, bijective⟩ :=
      exists_bijective_semilinearMap_sections_higherDirectImage_H
        (pullback.snd π baseMap)
        ((Modules.pullback (pullback.fst π baseMap)).obj moduleSheaf) 0
    have finiteSource := finiteH openSubset affine 0
    letI : Module.Finite Γ(Spec Γ(Y, openSubset), ⊤)
        Γ(((higherDirectImage (pullback.snd π baseMap) 0).obj
          ((Modules.pullback (pullback.fst π baseMap)).obj moduleSheaf)), ⊤) :=
      Module.Finite.of_bijective_semilinear semilinearComparison bijective
        (Scheme.ΓSpecIso Γ(Y, openSubset)).inv.hom finiteSource
    have finiteTargetSections : Module.Finite Γ(Spec Γ(Y, openSubset), ⊤)
        Γ(((higherDirectImage π 0).obj moduleSheaf).restrict baseMap, ⊤) :=
      Module.Finite.of_surjective
        (Hom.appₗ (X := Spec Γ(Y, openSubset)) comparison.hom ⊤)
        (ConcreteCategory.bijective_of_isIso (comparison.hom.app ⊤)).2
    letI : Module.Finite Γ(Spec Γ(Y, openSubset), ⊤)
        Γ(((higherDirectImage π 0).obj moduleSheaf).restrict baseMap, ⊤) :=
      finiteTargetSections
    letI : Module.Finite Γ(Y, openSubset)
        Γ(((higherDirectImage π 0).obj moduleSheaf).restrict baseMap, ⊤) :=
      finite_sections_top_of_finite
        (((higherDirectImage π 0).obj moduleSheaf).restrict baseMap)
    exact exists_presentation_isFinite_of_finite_sections
      (((higherDirectImage π 0).obj moduleSheaf).restrict baseMap)
  choose presentations finitePresentations using fun openSubset : Y.affineOpens ↦
    hP openSubset.1 openSubset.2
  letI : ∀ openSubset : Y.affineOpens, (presentations openSubset).IsFinite :=
    finitePresentations
  exact isFinitePresentation_of_iSup_opensRange_eq_top
    ((higherDirectImage π 0).obj moduleSheaf)
    (fun openSubset : Y.affineOpens ↦ openSubset.2.fromSpec)
    (by simpa only [IsAffineOpen.opensRange_fromSpec] using iSup_affineOpens_eq_top Y)
    presentations

/-- Serre vanishing for a coherent module on a closed subscheme of finite
relative projective space over a quasi-compact locally Noetherian scheme. -/
theorem exists_isZero_higherDirectImage_tensorObj_twistRestrict
    [IsLocallyNoetherian Y] [CompactSpace Y]
    (he : e ≫ ℙ(n; Y) ↘ Y = π) (moduleSheaf : Y'.Modules)
    [moduleSheaf.IsFinitePresentation] :
    ∃ bound : ℤ, ∀ degree ≥ bound, ∀ cohomologyDegree : ℕ,
      IsZero ((higherDirectImage π (cohomologyDegree + 1)).obj
        (moduleSheaf ⊗ ProjectiveSpace.twistRestrict e degree)) := by
  apply exists_isZero_higherDirectImage_tensorObj_twistRestrict_of_affine he moduleSheaf
  intro openSubset affine
  letI : IsNoetherianRing Γ(Y, openSubset) :=
    IsLocallyNoetherian.component_noetherian ⟨openSubset, affine⟩
  letI := isClosedImmersion_coordinateLift he affine.fromSpec
  obtain ⟨bound, vanishing⟩ := exists_subsingleton_H_tensor_twistRestrict_of_isFinite n
    (CommRingCat.of Γ(Y, openSubset)) (coordinateLift he affine.fromSpec)
    ((pullback (pullback.fst π affine.fromSpec)).obj moduleSheaf)
  exact ⟨bound, fun degree degreeBound cohomologyDegree ↦
    vanishing degree degreeBound (cohomologyDegree + 1) (by omega)⟩

/-- The zeroth higher direct image of a coherent module on a closed subscheme
of finite relative projective space over a locally Noetherian scheme is coherent. -/
theorem isFinitePresentation_higherDirectImage_zero_of_projectiveSpace
    [IsLocallyNoetherian Y] [HasInjectiveResolutions Y'.Modules]
    (he : e ≫ ℙ(n; Y) ↘ Y = π) (moduleSheaf : Y'.Modules)
    [moduleSheaf.IsFinitePresentation] :
    ((higherDirectImage π 0).obj moduleSheaf).IsFinitePresentation := by
  apply isFinitePresentation_higherDirectImage_zero_of_affine_finiteH he moduleSheaf
  intro openSubset affine
  letI : IsNoetherianRing Γ(Y, openSubset) :=
    IsLocallyNoetherian.component_noetherian ⟨openSubset, affine⟩
  letI := isClosedImmersion_coordinateLift he affine.fromSpec
  have finiteCohomology := hasFiniteH_of_isFinite_relativeProjectiveSpace n
    (CommRingCat.of Γ(Y, openSubset)) (coordinateLift he affine.fromSpec)
    ((pullback (pullback.fst π affine.fromSpec)).obj moduleSheaf)
  simpa only [coordinateLift_over (R := CommRingCat.of Γ(Y, openSubset))
    he affine.fromSpec] using finiteCohomology

/-- Local affine presentations descend to finite presentation on the base. -/
theorem isFinitePresentation_of_affinePresentations (M : Y.Modules)
    {indices : Type u} {sources : indices → Scheme.{u}}
    (morphisms : ∀ index, sources index ⟶ Y) [∀ index, IsOpenImmersion (morphisms index)]
    (cover : ⨆ index, (morphisms index).opensRange = ⊤)
    (presentations : ∀ index, (M.restrict (morphisms index)).Presentation)
    [∀ index, (presentations index).IsFinite] : M.IsFinitePresentation :=
  isFinitePresentation_of_iSup_opensRange_eq_top M morphisms cover presentations

end AlgebraicGeometry.Scheme.Modules
