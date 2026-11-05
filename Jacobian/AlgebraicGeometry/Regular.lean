import Jacobian.AlgebraicGeometry.Morphisms.SmoothSourceDescent
import Jacobian.RingTheory.RegularLocalRing.UniqueFactorization
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Regular schemes and factorial local rings

A scheme is regular when every local ring is regular. Smooth schemes over a
field are regular. The localizations of each stalk are again scheme stalks,
so the Auslander–Buchsbaum theorem makes these local rings factorial.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory

namespace AlgebraicGeometry

@[mk_iff]
class IsRegular (scheme : Scheme.{schemeUniverse}) : Prop where

  isRegularLocalRing_stalk (point : scheme) : IsRegularLocalRing (scheme.presheaf.stalk point)

attribute [instance] IsRegular.isRegularLocalRing_stalk


theorem IsRegular.of_smoothOfRelativeDimension {baseField : Type schemeUniverse} [Field baseField] {scheme : Scheme.{schemeUniverse}}
    (structureMap : scheme ⟶ Spec (.of baseField)) (dimension : ℕ) [SmoothOfRelativeDimension dimension structureMap] : IsRegular scheme :=
  ⟨SmoothOfRelativeDimension.isRegularLocalRing_stalk structureMap dimension⟩


theorem IsRegular.isIntegral (scheme : Scheme.{schemeUniverse}) [IsRegular scheme]
    [IrreducibleSpace scheme] : IsIntegral scheme :=
  have := isReduced_of_isReduced_stalk scheme
  isIntegral_of_irreducibleSpace_of_isReduced scheme

theorem IsAffineOpen.isRegularLocalRing_localization {scheme : Scheme.{schemeUniverse}} {openSubset : scheme.Opens}
    (hU : IsAffineOpen openSubset) (hX : ∀ point ∈ openSubset, IsRegularLocalRing (scheme.presheaf.stalk point))
    (p : Ideal Γ(scheme, openSubset)) [p.IsPrime] : IsRegularLocalRing (Localization.AtPrime p) := by
  have hy : hU.fromSpec ⟨p, inferInstance⟩ ∈ openSubset := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact Set.mem_range_self _
  let := scheme.presheaf.algebra_section_stalk ⟨_, hy⟩
  have := hU.isLocalization_stalk' ⟨p, inferInstance⟩ hy
  have := hX _ hy
  exact .of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (scheme.presheaf.stalk (hU.fromSpec ⟨p, inferInstance⟩)) (Localization.AtPrime p)).toRingEquiv

theorem IsRegular.of_smooth {baseField : Type schemeUniverse} [Field baseField] {scheme : Scheme.{schemeUniverse}} (structureMap : scheme ⟶ Spec (.of baseField))
    [Smooth structureMap] : IsRegular scheme :=
  ⟨Smooth.isRegularLocalRing_stalk structureMap⟩

theorem IsRegular.isRegularRing_stalk {scheme : Scheme.{schemeUniverse}} [IsRegular scheme] (point : scheme) :
    IsRegularRing (scheme.presheaf.stalk point) := by
  obtain ⟨_, ⟨openSubset, hU, rfl⟩, hxU, -⟩ :=
    scheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ point) isOpen_univ
  let := scheme.presheaf.algebra_section_stalk ⟨point, hxU⟩
  have := hU.isLocalization_stalk ⟨point, hxU⟩
  rw [isRegularRing_iff]
  intro primeIdeal _
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (hU.primeIdealOf ⟨point, hxU⟩).asIdeal.primeCompl (Localization.AtPrime primeIdeal) primeIdeal
  let localPoint : PrimeSpectrum Γ(scheme, openSubset) :=
    ⟨primeIdeal.comap (algebraMap Γ(scheme, openSubset) (scheme.presheaf.stalk point)), inferInstance⟩
  have hy : hU.fromSpec localPoint ∈ openSubset := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact Set.mem_range_self localPoint
  let := scheme.presheaf.algebra_section_stalk ⟨hU.fromSpec localPoint, hy⟩
  have := hU.isLocalization_stalk' localPoint hy
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv localPoint.asIdeal.primeCompl
    (scheme.presheaf.stalk (hU.fromSpec localPoint)) (Localization.AtPrime primeIdeal)).toRingEquiv


theorem IsRegular.uniqueFactorizationMonoid_stalk {scheme : Scheme.{schemeUniverse}} [IsRegular scheme] (point : scheme) :
    UniqueFactorizationMonoid (scheme.presheaf.stalk point) :=
  have := isRegularRing_stalk point
  IsRegularLocalRing.uniqueFactorizationMonoid _



end AlgebraicGeometry
