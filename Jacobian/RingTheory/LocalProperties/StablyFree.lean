import Jacobian.Algebra.Module.StablyFree.Exact
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.LocalProperties.Projective

/-!
# Stably free localizations of modules with finite projective dimension
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe typeUniverse

open CategoryTheory

namespace Module

variable {ring : Type typeUniverse} [CommRing ring] [IsLocalRing ring] [IsNoetherianRing ring] (multiplicativeSet : Submonoid ring)


theorem isStablyFree_of_isLocalizedModule_of_hasProjectiveDimensionLE (bound : ℕ) :
    ∀ (module : Type typeUniverse) [AddCommGroup module] [Module ring module] [Module.Finite ring module],
      HasProjectiveDimensionLE (ModuleCat.of ring module) bound →
      ∀ (quotientModule : Type typeUniverse) [AddCommGroup quotientModule] [Module ring quotientModule] [Module (Localization multiplicativeSet) quotientModule]
        [IsScalarTower ring (Localization multiplicativeSet) quotientModule] (firstMap : module →ₗ[ring] quotientModule) [IsLocalizedModule multiplicativeSet firstMap]
        [Projective (Localization multiplicativeSet) quotientModule], IsStablyFree (Localization multiplicativeSet) quotientModule := by
  induction bound with
  | zero =>
    intro module _ _ _ hM quotientModule _ _ _ _ firstMap _ _
    have : Projective ring module := by
      rw [IsProjective.iff_projective, projective_iff_hasProjectiveDimensionLE_zero]
      exact hM
    have : Free ring module := free_of_flat_of_isLocalRing
    have : Free (Localization multiplicativeSet) quotientModule := free_of_isLocalizedModule multiplicativeSet firstMap
    infer_instance
  | succ bound ih =>
    intro module _ _ _ hM quotientModule _ _ _ _ firstMap _ _
    obtain ⟨rank, presentationMap, hπ⟩ := Module.Finite.exists_fin' ring module
    let kernel := LinearMap.ker presentationMap
    have hex := LinearMap.exact_subtype_ker_map presentationMap
    have hS := ModuleCat.shortComplex_shortExact
      (ModuleCat.shortComplexOfCompEqZero kernel.subtype presentationMap hex.linearMap_comp_eq_zero) hex
      kernel.injective_subtype hπ
    have : CategoryTheory.Projective (ModuleCat.of ring (Fin rank → ring)) := by
      rw [← IsProjective.iff_projective]
      infer_instance
    have hK : HasProjectiveDimensionLE (ModuleCat.of ring kernel) bound :=
      (hS.hasProjectiveDimensionLT_X₃_iff bound this).1 hM
    let fK := LocalizedModule.mkLinearMap multiplicativeSet kernel
    let fF := LocalizedModule.mkLinearMap multiplicativeSet (Fin rank → ring)
    have : Free (Localization multiplicativeSet) (LocalizedModule multiplicativeSet (Fin rank → ring)) := free_of_isLocalizedModule multiplicativeSet fF
    have : Module.Finite (Localization multiplicativeSet) (LocalizedModule multiplicativeSet (Fin rank → ring)) :=
      .of_isLocalizedModule multiplicativeSet fF
    let inclusion := (IsLocalizedModule.map multiplicativeSet fK fF kernel.subtype).extendScalarsOfIsLocalization multiplicativeSet
      (Localization multiplicativeSet)
    let projection := (IsLocalizedModule.map multiplicativeSet fF firstMap presentationMap).extendScalarsOfIsLocalization multiplicativeSet (Localization multiplicativeSet)
    have hi : Function.Injective inclusion := IsLocalizedModule.map_injective multiplicativeSet fK fF _ kernel.injective_subtype
    have hp : Function.Surjective projection := IsLocalizedModule.map_surjective multiplicativeSet fF firstMap _ hπ
    have hip : Function.Exact inclusion projection := IsLocalizedModule.map_exact multiplicativeSet fK fF firstMap _ _ hex
    have : Projective (Localization multiplicativeSet) (LocalizedModule multiplicativeSet kernel) := by
      with_unfolding_all
        exact Projective.of_exact_of_projective (ring := Localization multiplicativeSet)
          (kernel := LocalizedModule multiplicativeSet kernel) (freeModule := LocalizedModule multiplicativeSet (Fin rank → ring)) (quotientModule := quotientModule)
          (firstMap := inclusion) (secondMap := projection) hi hp hip
    have := ih kernel hK (LocalizedModule multiplicativeSet kernel) fK
    with_unfolding_all
      exact IsStablyFree.of_exact (ring := Localization multiplicativeSet)
        (kernel := LocalizedModule multiplicativeSet kernel) (freeModule := LocalizedModule multiplicativeSet (Fin rank → ring)) (quotientModule := quotientModule)
        (firstMap := inclusion) (secondMap := projection) hi hp hip

end Module
