import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Jacobian.AlgebraicGeometry.Cohomology.Finiteness
import Jacobian.CategoryTheory.Abelian.DimensionShifting
import Jacobian.CategoryTheory.Abelian.RightDerived.ExactSequence

/-!
# Cohomology of an acyclic pushforward

When all positive higher direct images of a module sheaf vanish, its cohomology
agrees with the cohomology of its pushforward. The comparison is natural in the
coefficient sheaf, compatible with global-function scalars, and preserves finite
cohomology over an affine base.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {sourceScheme targetScheme : Scheme.{u}} (morphism : sourceScheme ⟶ targetScheme) [HasInjectiveResolutions sourceScheme.Modules]

attribute [local instance] enoughInjectives_of_hasInjectiveResolutions

local instance preservesZeroMorphisms_toSheaf_source :
    Functor.PreservesZeroMorphisms (C := sourceScheme.Modules)
      (D := Sheaf (Opens.grothendieckTopology sourceScheme) AddCommGrpCat.{u})
      (SheafOfModules.toSheaf.{u} sourceScheme.ringCatSheaf) where
  map_zero := by intros; ext openSubset sectionValue; rfl

local instance preservesZeroMorphisms_toSheaf_target :
    Functor.PreservesZeroMorphisms (C := targetScheme.Modules)
      (D := Sheaf (Opens.grothendieckTopology targetScheme) AddCommGrpCat.{u})
      (SheafOfModules.toSheaf.{u} targetScheme.ringCatSheaf) where
  map_zero := by intros; ext openSubset sectionValue; rfl

/-- The `𝒪_{sourceScheme}`-modules whose higher direct images along `morphism` vanish in all positive degrees. -/
def higherDirectImageAcyclic : ObjectProperty sourceScheme.Modules :=
  fun coefficientSheaf ↦ ∀ degree : ℕ, IsZero ((higherDirectImage morphism (degree + 1)).obj coefficientSheaf)

variable {morphism}

/-- The pushforward of a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` with `R¹ π_* ℱ₁ = 0` is
short exact: `π_*` is left exact, and `π_* ℱ₂ ⟶ π_* ℱ₃ ⟶ R¹ π_* ℱ₁` is exact. -/
lemma shortExact_map_pushforward_of_isZero {sequence : ShortComplex sourceScheme.Modules} (hS : sequence.ShortExact)
    (witness : IsZero ((higherDirectImage morphism 1).obj sequence.X₁)) : (sequence.map (pushforward morphism)).ShortExact := by
  let := HasDerivedCategory.standard sourceScheme.Modules
  let := HasDerivedCategory.standard targetScheme.Modules
  have := (pullbackPushforwardAdjunction morphism).rightAdjoint_preservesLimits.{0, 0}
  have : PreservesFiniteLimits (pushforward morphism) := inferInstance
  have := hS.mono_f
  have hepi : Epi ((pushforward morphism).map sequence.g) := by
    obtain ⟨connecting, _, _, exactAt, _⟩ := hS.exists_rightDerived_δ_exact (pushforward morphism) 0
    have : Epi ((((pushforward morphism).rightDerived 0).map sequence.g)) :=
      exactAt.epi_f (witness.eq_of_tgt _ _)
    have comparison := ((pushforward morphism).rightDerivedZeroIsoSelf.hom.naturality sequence.g)
    have : (pushforward morphism).map sequence.g = ((pushforward morphism).rightDerivedZeroIsoSelf.inv.app sequence.X₂) ≫
        ((pushforward morphism).rightDerived 0).map sequence.g ≫
          (pushforward morphism).rightDerivedZeroIsoSelf.hom.app sequence.X₃ := by
      rw [comparison, Iso.inv_hom_id_app_assoc]
    rw [this]
    infer_instance
  exact ShortComplex.ShortExact.mk' (hS.exact.map_of_mono_of_preservesKernel _ inferInstance
    inferInstance) (Functor.map_mono (pushforward morphism) sequence.f) hepi

set_option maxHeartbeats 800000 in
variable (morphism) in
/-- The modules with vanishing higher direct images are stable under the dimension shifting
`0 ⟶ coefficientSheaf ⟶ I ⟶ Q ⟶ 0`, with `I` the chosen injective object under `coefficientSheaf`. -/
lemma higherDirectImageAcyclic_under_cokernel (coefficientSheaf : sourceScheme.Modules)
    (hℱ : higherDirectImageAcyclic morphism coefficientSheaf) :
    higherDirectImageAcyclic morphism (Injective.under coefficientSheaf) ∧
      higherDirectImageAcyclic morphism (cokernel (Injective.ι coefficientSheaf)) := by
  let := HasDerivedCategory.standard sourceScheme.Modules
  let := HasDerivedCategory.standard targetScheme.Modules
  refine ⟨fun degree ↦ (pushforward morphism).isZero_rightDerived_obj_injective_succ degree _, fun degree ↦ ?_⟩
  have hS : (ShortComplex.mk (Injective.ι coefficientSheaf) (cokernel.π (Injective.ι coefficientSheaf))
      (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  obtain ⟨connecting, _, _, exactAt, _⟩ := hS.exists_rightDerived_δ_exact (pushforward morphism) (degree + 1)
  exact exactAt.isZero_X₂ (((pushforward morphism).isZero_rightDerived_obj_injective_succ degree _).eq_of_src _ _)
    ((hℱ (degree + 1)).eq_of_tgt _ _)

variable (morphism) in
/-- **Cohomology of a pushforward with vanishing higher direct images.** For `morphism : sourceScheme ⟶ targetScheme`, the
functors `coefficientSheaf ↦ H^degree(sourceScheme, coefficientSheaf)` and `coefficientSheaf ↦ H^degree(targetScheme, π_* coefficientSheaf)` are isomorphic on the `𝒪_{sourceScheme}`-modules `coefficientSheaf`
with `R^higherDegree π_* coefficientSheaf = 0` for all `higherDegree > 0`. This is the degenerate case of the Leray spectral
sequence. -/
theorem nonempty_functorH_iso_pushforward_of_isZero_higherDirectImage (degree : ℕ) :
    Nonempty ((higherDirectImageAcyclic morphism).ι ⋙ (SheafOfModules.toSheaf sourceScheme.ringCatSheaf) ⋙
        CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology sourceScheme) degree ≅
      (higherDirectImageAcyclic morphism).ι ⋙ pushforward morphism ⋙ (SheafOfModules.toSheaf targetScheme.ringCatSheaf) ⋙
        CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology targetScheme) degree) := by
  have := enoughInjectives_of_hasInjectiveResolutions (C := sourceScheme.Modules)
  have hf (sequence : ShortComplex sourceScheme.Modules) (hS : sequence.ShortExact)
      (witness : higherDirectImageAcyclic morphism sequence.X₁) : ((sequence.map (pushforward morphism)).map ((SheafOfModules.toSheaf targetScheme.ringCatSheaf))).ShortExact :=
    shortExact_map_toSheaf (shortExact_map_pushforward_of_isZero hS (witness 0))
  refine (higherDirectImageAcyclic morphism).nonempty_iso_of_connecting
    (higherDirectImageAcyclic_under_cokernel morphism)
    (fun degree ↦ (SheafOfModules.toSheaf sourceScheme.ringCatSheaf) ⋙ CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology sourceScheme) degree)
    (fun degree ↦ pushforward morphism ⋙ (SheafOfModules.toSheaf targetScheme.ringCatSheaf) ⋙
      CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology targetScheme) degree)
    (fun sequence hS _ degree ↦ CategoryTheory.Sheaf.functorHδ (shortExact_map_toSheaf hS) degree)
    (fun sequence hS witness degree ↦ CategoryTheory.Sheaf.functorHδ (hf sequence hS witness) degree)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ degree
  · intro firstSequence secondSequence sequenceMap h₁ h₂ _ _ degree
    exact CategoryTheory.Sheaf.functorHδ_naturality.{u} (shortExact_map_toSheaf h₁) degree
      (shortExact_map_toSheaf h₂) (((SheafOfModules.toSheaf sourceScheme.ringCatSheaf)).mapShortComplex.map sequenceMap)
  · intro firstSequence secondSequence sequenceMap h₁ h₂ p₁ p₂ degree
    exact CategoryTheory.Sheaf.functorHδ_naturality.{u} (hf _ h₁ p₁) degree (hf _ h₂ p₂)
      ((pushforward morphism ⋙ (SheafOfModules.toSheaf targetScheme.ringCatSheaf)).mapShortComplex.map sequenceMap)
  · intro sequence hS _ degree cohomologyClass
    exact CategoryTheory.Sheaf.functorHδ_eq_zero_iff.{u} (shortExact_map_toSheaf hS) degree cohomologyClass
  · intro sequence hS witness degree cohomologyClass
    exact CategoryTheory.Sheaf.functorHδ_eq_zero_iff.{u} (hf sequence hS witness) degree cohomologyClass
  · intro sequence hS _ degree hinj
    have : Subsingleton (CategoryTheory.Sheaf.H (sequence.map ((SheafOfModules.toSheaf sourceScheme.ringCatSheaf))).X₂ (degree + 1)) :=
      subsingleton_H_of_injective sequence.X₂ degree
    exact CategoryTheory.Sheaf.functorHδ_surjective.{u} (shortExact_map_toSheaf hS) degree
  · intro sequence hS witness degree hinj
    have : Subsingleton (CategoryTheory.Sheaf.H ((sequence.map (pushforward morphism)).map ((SheafOfModules.toSheaf targetScheme.ringCatSheaf))).X₂
        (degree + 1)) :=
      subsingleton_H_pushforward_of_injective morphism sequence.X₂ degree
    exact CategoryTheory.Sheaf.functorHδ_surjective.{u} (hf sequence hS witness) degree
  · exact Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft ((SheafOfModules.toSheaf sourceScheme.ringCatSheaf))
          (CategoryTheory.Sheaf.functorHZeroIso.{u} _ isTerminalTop) ≪≫
        NatIso.ofComponents (fun _ ↦ Iso.refl _) ≪≫
        Functor.isoWhiskerLeft (pushforward morphism ⋙ (SheafOfModules.toSheaf targetScheme.ringCatSheaf))
          (CategoryTheory.Sheaf.functorHZeroIso.{u} _ isTerminalTop).symm)

/-- **Cohomology of a pushforward with vanishing higher direct images, with its module
structure.** For `morphism : sourceScheme ⟶ targetScheme` and an `𝒪_{sourceScheme}`-module `coefficientSheaf` with `R^higherDegree π_* coefficientSheaf = 0` for all `higherDegree > 0`,
`H^degree(sourceScheme, coefficientSheaf) ≅ H^degree(targetScheme, π_* coefficientSheaf)`, the isomorphism taking the action of `morphism^♯ scalar` to that of `scalar`, for
every global function `scalar` on `targetScheme`. -/
theorem exists_H_addEquiv_pushforward_of_isZero_higherDirectImage (coefficientSheaf : sourceScheme.Modules)
    (hℱ : ∀ higherDegree : ℕ, IsZero ((higherDirectImage morphism (higherDegree + 1)).obj coefficientSheaf)) (degree : ℕ) :
    ∃ comparison : coefficientSheaf.H degree ≃+ ((pushforward morphism).obj coefficientSheaf).H degree,
      ∀ (scalar : Γ(targetScheme, ⊤)) (cohomologyClass : coefficientSheaf.H degree), comparison (morphism.appTop scalar • cohomologyClass) = scalar • comparison cohomologyClass := by
  obtain ⟨comparison⟩ := nonempty_functorH_iso_pushforward_of_isZero_higherDirectImage morphism degree
  let coefficientObject : (higherDirectImageAcyclic morphism).FullSubcategory := ⟨coefficientSheaf, hℱ⟩
  refine ⟨(comparison.app coefficientObject).addCommGroupIsoToAddEquiv, fun scalar cohomologyClass ↦ ?_⟩
  have witness := NatTrans.naturality_apply comparison.hom
    (ObjectProperty.homMk (coefficientSheaf.smulHom (morphism.appTop scalar)) : coefficientObject ⟶ coefficientObject) cohomologyClass
  change comparison.hom.app coefficientObject (H.map (coefficientSheaf.smulHom (morphism.appTop scalar)) degree cohomologyClass) =
    H.map (((pushforward morphism).obj coefficientSheaf).smulHom scalar) degree (comparison.hom.app coefficientObject cohomologyClass)
  rw [← pushforward_map_smulHom]
  exact witness


/-- Vanishing positive higher direct images preserve finite cohomology over an affine base. -/
lemma hasFiniteH_pushforward_iff_of_isZero {baseRing : Type u} [CommRing baseRing]
    (morphism : sourceScheme ⟶ targetScheme) (baseMap : targetScheme ⟶ Spec (.of baseRing))
    (coefficientSheaf : sourceScheme.Modules)
    (higherVanish : ∀ degree : ℕ, IsZero ((higherDirectImage morphism (degree + 1)).obj coefficientSheaf)) :
    HasFiniteH baseMap ((pushforward morphism).obj coefficientSheaf) ↔
      HasFiniteH (morphism ≫ baseMap) coefficientSheaf := by
  have comparison (degree : ℕ) :
      letI := moduleHOfSpec (morphism ≫ baseMap) coefficientSheaf degree
      letI := moduleHOfSpec baseMap ((pushforward morphism).obj coefficientSheaf) degree
      Nonempty (coefficientSheaf.H degree ≃ₗ[baseRing] ((pushforward morphism).obj coefficientSheaf).H degree) := by
    obtain ⟨additiveComparison, scalarCompatibility⟩ :=
      exists_H_addEquiv_pushforward_of_isZero_higherDirectImage
        (morphism := morphism) coefficientSheaf higherVanish degree
    letI := moduleHOfSpec (morphism ≫ baseMap) coefficientSheaf degree
    letI := moduleHOfSpec baseMap ((pushforward morphism).obj coefficientSheaf) degree
    exact ⟨{ additiveComparison with
      map_smul' := fun scalar cohomologyClass ↦ by
        change additiveComparison
          ((((Scheme.ΓSpecIso (.of baseRing)).inv ≫ (morphism ≫ baseMap).appTop).hom scalar) •
            cohomologyClass) = _
        rw [Scheme.Hom.comp_appTop, ← Category.assoc, CommRingCat.hom_comp, RingHom.comp_apply]
        exact scalarCompatibility _ _ }⟩
  refine ⟨fun finitePushforward degree ↦ ?_, fun finiteSource degree ↦ ?_⟩
  · letI := moduleHOfSpec (morphism ≫ baseMap) coefficientSheaf degree
    letI := moduleHOfSpec baseMap ((pushforward morphism).obj coefficientSheaf) degree
    have := finitePushforward degree
    exact Module.Finite.equiv (comparison degree).some.symm
  · letI := moduleHOfSpec (morphism ≫ baseMap) coefficientSheaf degree
    letI := moduleHOfSpec baseMap ((pushforward morphism).obj coefficientSheaf) degree
    have := finiteSource degree
    exact Module.Finite.equiv (comparison degree).some

end AlgebraicGeometry.Scheme.Modules
