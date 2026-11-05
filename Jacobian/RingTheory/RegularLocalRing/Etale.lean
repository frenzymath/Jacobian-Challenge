import Mathlib.Algebra.Module.SpanRank
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Regular local rings and étale algebras

A flat local homomorphism carrying the maximal ideal onto the maximal ideal
preserves regularity. Applying this to the localizations of an étale algebra
shows that an étale algebra over a regular ring has regular local rings.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing

/-- A flat local homomorphism whose extended maximal ideal is the maximal ideal
preserves regularity of noetherian local rings. -/
theorem IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq {source target : Type*}
    [CommRing source] [CommRing target] [Algebra source target] [IsRegularLocalRing source]
    [IsLocalRing target] [IsNoetherianRing target] [IsLocalHom (algebraMap source target)]
    [Module.Flat source target]
    (maximal_map : (maximalIdeal source).map (algebraMap source target) = maximalIdeal target) :
    IsRegularLocalRing target := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have : (maximalIdeal target).LiesOver (maximalIdeal source) :=
    ⟨(((local_hom_TFAE (algebraMap source target)).out 0 4 rfl rfl).mp inferInstance).symm⟩
  rw [← maximal_map, ← maximalIdeal_height_eq_ringKrullDim,
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      (maximalIdeal source) (maximalIdeal target)]
  calc (((maximalIdeal source).map (algebraMap source target)).spanFinrank : WithBot ℕ∞)
      ≤ (maximalIdeal source).spanFinrank := by
        exact_mod_cast Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)
    _ = (maximalIdeal source).height := by
        rw [IsRegularLocalRing.spanFinrank_maximalIdeal, maximalIdeal_height_eq_ringKrullDim]
    _ ≤ _ := by exact_mod_cast le_self_add

/-- A localization of an étale algebra is regular if the corresponding local
ring of the base is regular. -/
theorem IsRegularLocalRing.localization_of_etale_of_comap {baseRing algebra : Type*}
    [CommRing baseRing] [CommRing algebra] [Algebra baseRing algebra]
    [Algebra.Etale baseRing algebra] (prime : Ideal algebra) [prime.IsPrime]
    (regular_base :
      IsRegularLocalRing (Localization.AtPrime (prime.comap (algebraMap baseRing algebra)))) :
    IsRegularLocalRing (Localization.AtPrime prime) := by
  set basePrime := prime.comap (algebraMap baseRing algebra)
  have : prime.LiesOver basePrime := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver basePrime prime
  have : Algebra.EssFiniteType (Localization.AtPrime basePrime) (Localization.AtPrime prime) :=
    .of_comp baseRing _ _
  have : IsNoetherianRing (Localization.AtPrime prime) :=
    Algebra.EssFiniteType.isNoetherianRing (Localization.AtPrime basePrime) _
  have : IsLocalHom
      (algebraMap (Localization.AtPrime basePrime) (Localization.AtPrime prime)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have : Module.Flat (Localization.AtPrime basePrime) (Localization.AtPrime prime) :=
    RingHom.Flat.localRingHom (f := algebraMap baseRing algebra)
      (RingHom.flat_algebraMap_iff.mpr inferInstance) prime basePrime rfl
  refine IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq
    (source := Localization.AtPrime basePrime) ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  exact ((Algebra.isUnramifiedAt_iff_map_eq baseRing basePrime prime).mp inferInstance).2

/-- Local rings of an étale algebra over a regular ring are regular. -/
theorem IsRegularLocalRing.localization_of_etale {baseRing algebra : Type*}
    [CommRing baseRing] [CommRing algebra] [Algebra baseRing algebra]
    [Algebra.Etale baseRing algebra] [IsRegularRing baseRing]
    (prime : Ideal algebra) [prime.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime prime) :=
  localization_of_etale_of_comap (baseRing := baseRing) prime inferInstance
