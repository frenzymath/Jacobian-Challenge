import Jacobian.AlgebraicGeometry.Modules.FinitePresentation
import Jacobian.AlgebraicGeometry.Modules.LocallyFreeAffine
import Jacobian.AlgebraicGeometry.Modules.LocalizedFreeRestriction
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Finite local freeness from affine sections

A quasi-coherent module sheaf is finite locally free when its sections on every
affine open are finitely presented and flat. No constant-rank or Noetherian
hypothesis is needed: finite free neighborhoods are obtained by localization at
each prime, and their ranks may vary.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem exists_free_localization {ringType moduleType : Type*} [CommRing ringType]
    [AddCommGroup moduleType] [Module ringType moduleType]
    [Module.FinitePresentation ringType moduleType] [Module.Flat ringType moduleType]
    (prime : Ideal ringType) [prime.IsPrime] :
    ∃ scalar ∉ prime,
      Module.Free (Localization.Away scalar) (LocalizedModule.Away scalar moduleType) ∧
        Module.Finite (Localization.Away scalar) (LocalizedModule.Away scalar moduleType) := by
  letI : Module.Free (Localization.AtPrime prime)
      (LocalizedModule prime.primeCompl moduleType) := Module.free_of_flat_of_isLocalRing
  obtain ⟨scalar, outsidePrime, free, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers prime.primeCompl
      (LocalizedModule.mkLinearMap prime.primeCompl moduleType) (Localization.AtPrime prime)
  exact ⟨scalar, outsidePrime, free,
    Module.Finite.of_isLocalizedModule (.powers scalar)
      (LocalizedModule.mkLinearMap (.powers scalar) moduleType)⟩

/-- A quasi-coherent sheaf with finitely presented flat sections on every affine
open is finite locally free, with no restriction on the variation of its rank. -/
theorem isFiniteLocallyFree_of_finitePresentation_flat_sections {scheme : Scheme.{u}}
    (moduleSheaf : scheme.Modules) [moduleSheaf.IsQuasicoherent]
    (affineSections : ∀ openSubset : scheme.Opens, IsAffineOpen openSubset →
      Module.FinitePresentation Γ(scheme, openSubset) Γ(moduleSheaf, openSubset) ∧
        Module.Flat Γ(scheme, openSubset) Γ(moduleSheaf, openSubset)) :
    moduleSheaf.IsFiniteLocallyFree := by
  have neighborhood (point : scheme) :
      ∃ (chart : Scheme.{u}) (chartMap : chart ⟶ scheme) (_ : IsOpenImmersion chartMap)
        (indices : Type u) (_ : Finite indices), point ∈ chartMap.opensRange ∧
          Nonempty (moduleSheaf.restrict chartMap ≅ SheafOfModules.free indices) := by
    obtain ⟨_, ⟨openSubset, affine, rfl⟩, membership, _⟩ :=
      scheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ point) isOpen_univ
    replace affine : IsAffineOpen openSubset := affine
    obtain ⟨finitePresentation, flat⟩ := affineSections openSubset affine
    letI := finitePresentation
    letI := flat
    let chartSheaf := moduleSheaf.restrict affine.fromSpec
    letI : chartSheaf.IsQuasicoherent := isQuasicoherent_restrictFunctor affine.fromSpec moduleSheaf
    let sectionsIso := sectionsRestrictFromSpecLinearEquiv moduleSheaf affine
    let chartSections := moduleSpecΓFunctor.obj chartSheaf
    letI : Module.FinitePresentation Γ(scheme, openSubset) chartSections :=
      Module.FinitePresentation.of_equiv sectionsIso.symm
    letI : Module.Flat Γ(scheme, openSubset) chartSections := Module.Flat.of_linearEquiv sectionsIso
    let prime := affine.primeIdealOf ⟨point, membership⟩
    obtain ⟨scalar, outsidePrime, free, finite⟩ :=
      exists_free_localization (moduleType := chartSections) prime.asIdeal
    letI := free
    letI := finite
    let localizationMap := Spec.map
      (CommRingCat.ofHom (algebraMap Γ(scheme, openSubset) (Localization.Away scalar)))
    obtain ⟨comparison⟩ := nonempty_restrict_iso_free_of_localizedModule chartSheaf scalar
      (Module.Free.chooseBasis (Localization.Away scalar)
        (LocalizedModule.Away scalar chartSections)).repr
    refine ⟨_, localizationMap ≫ affine.fromSpec, inferInstance, _, inferInstance, ?_,
      ⟨(restrictFunctorComp localizationMap affine.fromSpec).app moduleSheaf ≪≫ comparison⟩⟩
    have primeInRange : prime ∈ localizationMap.opensRange := by
      rw [Hom.opensRange_localizationAway]
      exact outsidePrime
    obtain ⟨localizedPrime, imagePrime⟩ := primeInRange
    refine ⟨localizedPrime, (Hom.comp_apply _ _ _).trans ?_⟩
    exact (congrArg affine.fromSpec imagePrime).trans
      (affine.fromSpec_primeIdealOf ⟨point, membership⟩)
  choose charts chartMaps openImmersions indices finiteIndices membership comparisons
    using neighborhood
  letI := openImmersions
  letI := finiteIndices
  exact isFiniteLocallyFree_of_restrict_iso_free moduleSheaf chartMaps
    (eq_top_iff.mpr fun point _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨point, membership point⟩)
    indices comparisons

end AlgebraicGeometry.Scheme.Modules
