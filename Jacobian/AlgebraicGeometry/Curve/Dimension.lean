import Jacobian.AlgebraicGeometry.Curve.LocalRing
import Jacobian.RingTheory.KrullDimension.Polynomial
import Jacobian.RingTheory.RegularLocalRing.Domain
import Jacobian.Topology.KrullDimension.Curve
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Dimension and valuation local rings of smooth curves

Étale polynomial charts compute the codimension of closed points and bound the
 dimension of a smooth scheme over a field. Consequently the local rings of an
 integral smooth curve are fields or discrete valuation rings.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open CategoryTheory Limits Topology Order
namespace AlgebraicGeometry

variable {space otherSpace : Scheme.{u}}

instance (priority := low) LocallyQuasiFinite.of_etale (morphism : space ⟶ otherSpace) [Etale morphism] :
    LocallyQuasiFinite morphism := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro openSet chart equivalence
  have := HasRingHomProperty.appLE (P := @Etale) morphism ‹_› openSet chart equivalence
  algebraize [(morphism.appLE openSet chart equivalence).hom]
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance


/-- A locally quasi-finite morphism identifies no distinct specializing points. -/
lemma Scheme.Hom.eq_of_specializes_of_apply_eq (morphism : space ⟶ otherSpace) [LocallyQuasiFinite morphism] {point specialPoint : space}
    (dimension_bound : point ⤳ specialPoint) (hx : morphism point = morphism specialPoint) : point = specialPoint := by
  have : DiscreteTopology (morphism ⁻¹' {morphism specialPoint}) := (morphism.isDiscrete_preimage_singleton (morphism specialPoint)).to_subtype
  have h' : (⟨point, hx⟩ : morphism ⁻¹' {morphism specialPoint}) ⤳ ⟨specialPoint, rfl⟩ := IsInducing.subtypeVal.specializes_iff.mp dimension_bound
  exact congrArg Subtype.val h'.eq

/-- Flat locally quasi-finite morphisms preserve codimension of points. -/
lemma Scheme.Hom.coheight_apply_of_flat (morphism : space ⟶ otherSpace) [Flat morphism] [LocallyQuasiFinite morphism] (otherPoint : space) :
    coheight (morphism otherPoint) = coheight otherPoint := by
  have hf : StrictMono morphism := by
    intro element basis hab
    rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes] at hab ⊢
    refine ⟨hab.1.map morphism.continuous, fun dimension_bound ↦ hab.2 ?_⟩
    have := morphism.eq_of_specializes_of_apply_eq hab.1 (dimension_bound.antisymm (hab.1.map morphism.continuous)).eq.symm
    rw [this]
  refine (coheight_eq_of_strictMono morphism hf (fun element basis hab ↦ ?_) otherPoint).symm
  rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes] at hab
  obtain ⟨a', ha', rfl⟩ := Flat.generalizingMap morphism hab.1
  refine ⟨a', ?_, rfl⟩
  rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes]
  exact ⟨ha', fun dimension_bound ↦ hab.2 (dimension_bound.map morphism.continuous)⟩

/-- An étale polynomial chart has the expected codimension bound and closed-point codimension. -/
theorem coheight_le_of_etale_mvPolynomial {baseField : Type u} [Field baseField] {algebra : CommRingCat.{u}} {dimension : ℕ}
    (φ : MvPolynomial (Fin dimension) baseField →+* algebra) (hφ : φ.Etale) (otherPoint : Spec algebra) :
    coheight otherPoint ≤ dimension ∧ (IsClosed {otherPoint} → coheight otherPoint = dimension) := by
  let ringMap := Spec.map (CommRingCat.ofHom φ)
  have : Etale ringMap := HasRingHomProperty.Spec_iff.mpr hφ
  rw [← ringMap.coheight_apply_of_flat otherPoint, ← idealHeight_eq_coheight]
  refine ⟨?_, fun hy ↦ ?_⟩
  · have dimension_bound := Ideal.height_le_ringKrullDim_of_ne_top (ringMap otherPoint).2.ne_top
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at dimension_bound
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at dimension_bound
    exact_mod_cast dimension_bound
  · have : (ringMap otherPoint).asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
      (ringMap.closePoints_subset_preimage_closedPoints hy)
    exact MvPolynomial.height_eq_of_isMaximal dimension _

/-- Smooth relative dimension bounds the codimension of every point. -/
theorem coheight_le_of_smoothOfRelativeDimension {baseField : Type u} [Field baseField] {space : Scheme.{u}}
    (morphism : space ⟶ Spec (.of baseField)) (dimension : ℕ) [SmoothOfRelativeDimension dimension morphism] (point : space) :
    coheight point ≤ dimension := by
  obtain ⟨chart, hV, hx, φ, hφ⟩ := SmoothOfRelativeDimension.exists_etale_mvPolynomial_of_field morphism dimension point
  obtain ⟨otherPoint, rfl⟩ : ∃ otherPoint, hV.fromSpec otherPoint = point := ⟨_, hV.fromSpec_primeIdealOf ⟨point, hx⟩⟩
  rw [coheight_eq_of_isOpenImmersion]
  exact (coheight_le_of_etale_mvPolynomial φ hφ _).1

open Order in

/-- Closed points of a smooth scheme over a field have the expected codimension. -/
theorem coheight_eq_of_smoothOfRelativeDimension_of_isClosed {baseField : Type u} [Field baseField]
    {space : Scheme.{u}} (morphism : space ⟶ Spec (.of baseField)) (dimension : ℕ) [SmoothOfRelativeDimension dimension morphism] {point : space}
    (hx : IsClosed ({point} : Set space)) : coheight point = dimension := by
  obtain ⟨chart, hV, hxV, φ, hφ⟩ := SmoothOfRelativeDimension.exists_etale_mvPolynomial_of_field morphism dimension point
  obtain ⟨otherPoint, hy⟩ : ∃ otherPoint, hV.fromSpec otherPoint = point := ⟨_, hV.fromSpec_primeIdealOf ⟨point, hxV⟩⟩
  have hy' : IsClosed ({otherPoint} : Set (Spec Γ(space, chart))) := by
    have : hV.fromSpec.base ⁻¹' {point} = {otherPoint} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun dimension_bound ↦ hV.fromSpec.isOpenEmbedding.injective (dimension_bound.trans hy.symm), fun dimension_bound ↦ dimension_bound ▸ hy⟩
    rw [← this]
    exact hx.preimage hV.fromSpec.base.hom.continuous
  rw [← hy, coheight_eq_of_isOpenImmersion]
  exact (coheight_le_of_etale_mvPolynomial φ hφ otherPoint).2 hy'


/-- Smooth relative dimension bounds topological Krull dimension. -/
theorem topologicalKrullDim_le_of_smoothOfRelativeDimension {baseField : Type u} [Field baseField]
    {space : Scheme.{u}} (morphism : space ⟶ Spec (.of baseField)) (dimension : ℕ) [SmoothOfRelativeDimension dimension morphism] :
    topologicalKrullDim space ≤ dimension := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints,
    Order.krullDim_eq_iSup_coheight]
  exact iSup_le fun point ↦ by exact_mod_cast coheight_le_of_smoothOfRelativeDimension morphism dimension point


/-- A nonempty smooth scheme over a field has the expected dimension. -/
theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension {baseField : Type u} [Field baseField]
    {space : Scheme.{u}} (morphism : space ⟶ Spec (.of baseField)) (dimension : ℕ) [SmoothOfRelativeDimension dimension morphism]
    [Nonempty space] : topologicalKrullDim space = dimension := by
  refine le_antisymm (topologicalKrullDim_le_of_smoothOfRelativeDimension morphism dimension) ?_
  obtain ⟨point⟩ := ‹Nonempty space›
  obtain ⟨chart, hV, hx, φ, hφ⟩ := SmoothOfRelativeDimension.exists_etale_mvPolynomial_of_field morphism dimension point
  obtain ⟨maximal, hM, -⟩ := Ideal.exists_le_maximal _ (hV.primeIdealOf ⟨point, hx⟩).2.ne_top
  let otherPoint : Spec Γ(space, chart) := ⟨maximal, hM.isPrime⟩
  have := (coheight_le_of_etale_mvPolynomial φ hφ otherPoint).2
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hM)
  rw [← coheight_eq_of_isOpenImmersion hV.fromSpec] at this
  have dimension_bound := Order.coheight_le_krullDim (hV.fromSpec otherPoint)
  rw [this] at dimension_bound
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints]
  exact_mod_cast dimension_bound

namespace Scheme

section SmoothCurve

variable {baseField : Type u} [Field baseField] {space : Scheme.{u}}
variable (morphism : space ⟶ Spec (.of baseField)) [SmoothOfRelativeDimension 1 morphism]
include morphism

/-- The stalk at a closed point of a smooth curve is one-dimensional. -/
theorem ringKrullDim_stalk_eq_one_of_isClosed {point : space} (hx : IsClosed {point}) :
    ringKrullDim (space.presheaf.stalk point) = 1 := by
  rw [ringKrullDim_stalk_eq_coheight,
    coheight_eq_of_smoothOfRelativeDimension_of_isClosed morphism 1 hx]
  simp


/-- The stalk at a closed point of a smooth curve is a discrete valuation ring. -/
theorem isDiscreteValuationRing_stalk_of_isClosed {point : space} (hx : IsClosed {point}) :
    ∃ _ : IsDomain (space.presheaf.stalk point), IsDiscreteValuationRing (space.presheaf.stalk point) :=
  have := SmoothOfRelativeDimension.smooth 1 morphism
  letI (point : space) : IsRegularLocalRing (space.presheaf.stalk point) :=
    SmoothOfRelativeDimension.isRegularLocalRing_stalk morphism 1 point
  ⟨inferInstance, IsRegularLocalRing.isDiscreteValuationRing _
    (ringKrullDim_stalk_eq_one_of_isClosed morphism hx)⟩


/-- Stalks of smooth curves are regular and closed-point stalks are discrete valuation rings. -/
theorem isRegularLocalRing_stalk_and_isDiscreteValuationRing (point : space) :
    IsRegularLocalRing (space.presheaf.stalk point) ∧ ∃ _ : IsDomain (space.presheaf.stalk point),
      IsClosed {point} → IsDiscreteValuationRing (space.presheaf.stalk point) :=
  have := SmoothOfRelativeDimension.smooth 1 morphism
  letI (point : space) : IsRegularLocalRing (space.presheaf.stalk point) :=
    SmoothOfRelativeDimension.isRegularLocalRing_stalk morphism 1 point
  ⟨inferInstance, inferInstance, fun hx ↦ by
    obtain ⟨_, dimension_bound⟩ := isDiscreteValuationRing_stalk_of_isClosed morphism hx
    exact dimension_bound⟩


/-- Every local ring of an integral smooth curve is a valuation ring. -/
theorem valuationRing_stalk [IsIntegral space] (point : space) : ValuationRing (space.presheaf.stalk point) := by
  have := SmoothOfRelativeDimension.smooth 1 morphism
  have : IsLocallyNoetherian space := LocallyOfFiniteType.isLocallyNoetherian morphism
  letI (point : space) : IsRegularLocalRing (space.presheaf.stalk point) :=
    SmoothOfRelativeDimension.isRegularLocalRing_stalk morphism 1 point
  have hdim : ringKrullDim (space.presheaf.stalk point) ≤ topologicalKrullDim space := by
    rw [ringKrullDim_stalk_eq_coheight, topologicalKrullDim,
      Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints]
    exact Order.coheight_le_krullDim point
  have hle : ringKrullDim (space.presheaf.stalk point) ≤ 1 :=
    hdim.trans
      (by exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension morphism 1)
  by_cases h1 : ringKrullDim (space.presheaf.stalk point) = 1
  · have := IsRegularLocalRing.isDiscreteValuationRing _ h1
    infer_instance
  · have h0 : ringKrullDim (space.presheaf.stalk point) ≤ 0 := by
      generalize ringKrullDim (space.presheaf.stalk point) = codimension at *
      induction codimension using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe dimension =>
        induction dimension using ENat.recTopCoe with
        | top => exact absurd hle (by decide)
        | coe maximalIdealLocal =>
          have : maximalIdealLocal ≤ 1 := by exact_mod_cast hle
          have : maximalIdealLocal ≠ 1 := fun dimension_bound ↦ h1 (by rw [dimension_bound]; rfl)
          have : maximalIdealLocal = 0 := by omega
          subst this; rfl
    have : Ring.KrullDimLE 0 (space.presheaf.stalk point) := ⟨by exact_mod_cast h0⟩
    let := (Ring.KrullDimLE.isField_of_isDomain (R := space.presheaf.stalk point)).toField
    infer_instance

end SmoothCurve

/-- A nonclosed point of an integral curve is its generic point. -/
theorem eq_genericPoint_of_not_isClosed {thirdSpace : Scheme.{u}} [IrreducibleSpace thirdSpace]
    (dimension_bound : topologicalKrullDim thirdSpace ≤ 1) {thirdPoint : thirdSpace} (hz : ¬ IsClosed {thirdPoint}) : thirdPoint = genericPoint thirdSpace := by
  have : closure {thirdPoint} = (Set.univ : Set thirdSpace) := by
    by_contra hne
    exact hz (IsOpen.isClosed_singleton_of_mem_compl dimension_bound isClosed_closure.isOpen_compl
      (Set.nonempty_compl.mpr hne) fun hmem ↦ hmem (subset_closure rfl))
  exact (show IsGenericPoint thirdPoint ⊤ from this).eq (genericPoint_spec thirdSpace)

end Scheme
end AlgebraicGeometry
