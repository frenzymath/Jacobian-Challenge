import Jacobian.RingTheory.RegularLocalRing.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# Regular local rings of smooth schemes over fields

A scheme smooth of fixed relative dimension over a field has étale polynomial
charts. The local rings in these charts are regular, giving local regularity
without assumptions on the perfection of the ground field.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth scheme of relative dimension `dimension` over a field has affine
charts étale over the polynomial ring in `dimension` variables. -/
theorem SmoothOfRelativeDimension.exists_etale_mvPolynomial_of_field
    {baseField : Type u} [Field baseField] {scheme : Scheme.{u}}
    (morphism : scheme ⟶ Spec (.of baseField)) (dimension : ℕ)
    [SmoothOfRelativeDimension dimension morphism] (point : scheme) :
    ∃ (chart : scheme.Opens) (_ : IsAffineOpen chart) (_ : point ∈ chart)
      (chartMap : MvPolynomial (Fin dimension) baseField →+* Γ(scheme, chart)),
      chartMap.Etale := by
  obtain ⟨baseOpen, -, chart, affineChart, point_mem, image_mem, standardSmooth⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := dimension) (f := morphism) point
  obtain rfl : baseOpen = ⊤ := eq_top_iff.mpr fun otherPoint _ ↦
    Subsingleton.elim (morphism point) otherPoint ▸ image_mem point_mem
  obtain ⟨chartMap, -, chartMap_etale⟩ := standardSmooth.exists_etale_mvPolynomial
  let coefficients : MvPolynomial (Fin dimension) baseField ≃+*
      MvPolynomial (Fin dimension) Γ(Spec (.of baseField), ⊤) :=
    MvPolynomial.mapEquiv _ (Scheme.ΓSpecIso (.of baseField)).symm.commRingCatIsoToRingEquiv
  exact ⟨chart, affineChart, point_mem, chartMap.comp coefficients.toRingHom,
    RingHom.Etale.respectsIso.2 _ _ chartMap_etale⟩

/-- The stalk of an affine chart étale over a regular ring is regular. -/
theorem IsAffineOpen.isRegularLocalRing_stalk_of_etale {scheme : Scheme.{u}}
    {baseRing : Type u} [CommRing baseRing] [IsRegularRing baseRing]
    {chart : scheme.Opens} (affineChart : IsAffineOpen chart)
    (chartMap : baseRing →+* Γ(scheme, chart)) (etale : chartMap.Etale)
    (point : scheme) (point_mem : point ∈ chart) :
    IsRegularLocalRing (scheme.presheaf.stalk point) := by
  algebraize [chartMap]
  let := TopCat.Presheaf.algebra_section_stalk scheme.presheaf ⟨point, point_mem⟩
  have := affineChart.isLocalization_stalk ⟨point, point_mem⟩
  have := IsRegularLocalRing.localization_of_etale (baseRing := baseRing)
    (affineChart.primeIdealOf ⟨point, point_mem⟩).asIdeal
  exact .of_ringEquiv
    (IsLocalization.algEquiv (affineChart.primeIdealOf ⟨point, point_mem⟩).asIdeal.primeCompl
      (Localization.AtPrime (affineChart.primeIdealOf ⟨point, point_mem⟩).asIdeal)
      (scheme.presheaf.stalk point)).toRingEquiv

/-- Every local ring of a scheme smooth of fixed relative dimension over a
field is regular. -/
theorem SmoothOfRelativeDimension.isRegularLocalRing_stalk {baseField : Type u}
    [Field baseField] {scheme : Scheme.{u}} (morphism : scheme ⟶ Spec (.of baseField))
    (dimension : ℕ) [SmoothOfRelativeDimension dimension morphism] (point : scheme) :
    IsRegularLocalRing (scheme.presheaf.stalk point) := by
  obtain ⟨chart, affineChart, point_mem, chartMap, etale⟩ :=
    SmoothOfRelativeDimension.exists_etale_mvPolynomial_of_field morphism dimension point
  exact affineChart.isRegularLocalRing_stalk_of_etale chartMap etale point point_mem

end AlgebraicGeometry
