import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Exactness of the associated-sheaf functor

On basic opens, the map associated to a module homomorphism is its localization.
Localization preserves injections, so the associated-sheaf functor preserves
monomorphisms. Its adjunction then gives exactness and preservation of homology.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.tilde

variable {baseRing : CommRingCat.{u}} {source target : ModuleCat.{u} baseRing}

private def basicOpenMap (moduleMap : source ⟶ target) (element : baseRing) :
    ((modulesSpecToSheaf.obj (tilde source)).obj.obj
      (Opposite.op (PrimeSpectrum.basicOpen element))) →ₗ[baseRing]
    ((modulesSpecToSheaf.obj (tilde target)).obj.obj
      (Opposite.op (PrimeSpectrum.basicOpen element))) :=
  ((modulesSpecToSheaf.map (tilde.map moduleMap)).hom.app
    (Opposite.op (PrimeSpectrum.basicOpen element))).hom

private lemma basicOpenMap_eq (moduleMap : source ⟶ target) (element : baseRing) :
    basicOpenMap moduleMap element = IsLocalizedModule.map (Submonoid.powers element)
      (toOpen source (PrimeSpectrum.basicOpen element)).hom
      (toOpen target (PrimeSpectrum.basicOpen element)).hom moduleMap.hom := by
  apply IsLocalizedModule.ext (Submonoid.powers element)
    (toOpen source (PrimeSpectrum.basicOpen element)).hom
    (fun denominator ↦ IsLocalizedModule.map_units
      (toOpen target (PrimeSpectrum.basicOpen element)).hom denominator)
  ext sectionValue
  change basicOpenMap moduleMap element
      ((toOpen source (PrimeSpectrum.basicOpen element)).hom sectionValue) =
    IsLocalizedModule.map (Submonoid.powers element)
      (toOpen source (PrimeSpectrum.basicOpen element)).hom
      (toOpen target (PrimeSpectrum.basicOpen element)).hom moduleMap.hom
      ((toOpen source (PrimeSpectrum.basicOpen element)).hom sectionValue)
  rw [IsLocalizedModule.map_apply]
  exact congrArg (fun comparison : source ⟶ _ ↦ comparison.hom sectionValue)
    (toOpen_map_app moduleMap (PrimeSpectrum.basicOpen element))

/-- An injection of modules is injective on associated-sheaf sections over basic opens. -/
lemma map_injective_app_basicOpen (moduleMap : source ⟶ target)
    (injective : Function.Injective moduleMap.hom) (element : baseRing) :
    Function.Injective (Scheme.Modules.Hom.app ((tilde.functor baseRing).map moduleMap)
      (PrimeSpectrum.basicOpen element)) := by
  have localizedInjective : Function.Injective
      (IsLocalizedModule.map (Submonoid.powers element)
        (toOpen source (PrimeSpectrum.basicOpen element)).hom
        (toOpen target (PrimeSpectrum.basicOpen element)).hom moduleMap.hom) :=
    IsLocalizedModule.map_injective _ _ _ _ injective
  rw [← basicOpenMap_eq moduleMap element] at localizedInjective
  exact localizedInjective

instance (baseRing : CommRingCat.{u}) : (tilde.functor baseRing).PreservesMonomorphisms where
  preserves {source target} moduleMap monic := by
    have injective : Function.Injective moduleMap.hom :=
      (ModuleCat.mono_iff_injective moduleMap).mp monic
    have injectiveOnBasis : ∀ openSubset ∈ Set.range
        (fun element : baseRing ↦ PrimeSpectrum.basicOpen element),
        Function.Injective ((((Scheme.Modules.toPresheaf (Spec baseRing)).map
          ((tilde.functor baseRing).map moduleMap)).app (Opposite.op openSubset))) := by
      rintro openSubset ⟨element, rfl⟩
      exact map_injective_app_basicOpen moduleMap injective element
    let sourceSheaf : TopCat.Sheaf Ab.{u} (Spec baseRing) :=
      ⟨((tilde.functor baseRing).obj source).presheaf, ((tilde.functor baseRing).obj source).isSheaf⟩
    let targetSheaf : TopCat.Sheaf Ab.{u} (Spec baseRing) :=
      ⟨((tilde.functor baseRing).obj target).presheaf, ((tilde.functor baseRing).obj target).isSheaf⟩
    let sheafMap : sourceSheaf ⟶ targetSheaf :=
      ⟨(Scheme.Modules.toPresheaf (Spec baseRing)).map ((tilde.functor baseRing).map moduleMap)⟩
    have : ∀ point, Mono ((TopCat.Presheaf.stalkFunctor Ab.{u} point).map sheafMap.1) :=
      fun point ↦ (AddCommGrpCat.mono_iff_injective _).mpr
        (TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis
          PrimeSpectrum.isBasis_basic_opens injectiveOnBasis point)
    have monicSheaf : Mono sheafMap := TopCat.Presheaf.mono_of_stalk_mono sheafMap
    have : Mono ((Scheme.Modules.toPresheaf (Spec baseRing)).map
        ((tilde.functor baseRing).map moduleMap)) :=
      (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _ sheafMap).mp monicSheaf
    exact (Scheme.Modules.toPresheaf (Spec baseRing)).mono_of_mono_map ‹_›

instance (baseRing : CommRingCat.{u}) : PreservesFiniteLimits (tilde.functor baseRing) := by
  rw [(tilde.functor baseRing).preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro shortComplex shortExact
  have := shortExact.mono_f
  exact ⟨shortExact.exact.map_of_epi_of_preservesCokernel _ shortExact.epi_g inferInstance,
    inferInstance⟩

instance preservesHomology (baseRing : CommRingCat.{u}) :
    (tilde.functor baseRing).PreservesHomology :=
  Functor.preservesHomologyOfExact _

end AlgebraicGeometry.tilde
