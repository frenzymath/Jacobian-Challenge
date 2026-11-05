import Jacobian.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import Jacobian.AlgebraicGeometry.Curve.Dimension
import Jacobian.RingTheory.LocalRing.ResidueField.RegularFiber
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Relative effective Cartier divisors on smooth curves

A closed subscheme of a smooth relative curve which is flat, locally of finite
presentation and locally quasi-finite over the base is an effective Cartier
divisor. In particular this holds for finite flat families of finite presentation.
The proof identifies regular principal ideals on the smooth curve fibres and
lifts their local equations using the local flatness criterion.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe universeLevel

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {scheme baseScheme : Scheme.{universeLevel}}

open scoped AlgebraicGeometry.Scheme.Modules

open Limits TensorProduct

/-- A relative effective Cartier divisor has an invertible ideal and is flat over the base. -/
def IsRelativeEffectiveCartier (ideal : scheme.IdealSheafData) (π : scheme ⟶ baseScheme) : Prop :=
  ideal.IsInvertible ∧ Flat (ideal.subschemeι ≫ π)

/-- Affine charts of a fibre product are spectra of tensor products. -/
lemma _root_.CategoryTheory.IsPullback.exists_isOpenImmersion_spec_tensorProduct
    {X' multiplicativeSet : Scheme.{universeLevel}} {g' : X' ⟶ scheme} {π' : X' ⟶ multiplicativeSet} {π : scheme ⟶ baseScheme} {localizer : multiplicativeSet ⟶ baseScheme}
    (condition : IsPullback g' π' π localizer) {baseOpen : baseScheme.Opens} (hW : IsAffineOpen baseOpen) {affineOpen : scheme.Opens}
    (hU : IsAffineOpen affineOpen) (hUW : affineOpen ≤ π ⁻¹ᵁ baseOpen) {otherOpen : multiplicativeSet.Opens} (hV : IsAffineOpen otherOpen)
    (hVW : otherOpen ≤ localizer ⁻¹ᵁ baseOpen) :
    letI := (π.appLE baseOpen affineOpen hUW).hom.toAlgebra
    letI := (localizer.appLE baseOpen otherOpen hVW).hom.toAlgebra
    ∃ ι : Spec (.of (Γ(scheme, affineOpen) ⊗[Γ(baseScheme, baseOpen)] Γ(multiplicativeSet, otherOpen))) ⟶ X', IsOpenImmersion ι ∧
      ι ≫ g' = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
        hU.fromSpec ∧
      ι ≫ π' = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
        hV.fromSpec ∧
      ∀ x' : X', g' x' ∈ affineOpen → π' x' ∈ otherOpen → x' ∈ Set.range ι := by
  let := (π.appLE baseOpen affineOpen hUW).hom.toAlgebra
  let := (localizer.appLE baseOpen otherOpen hVW).hom.toAlgebra
  have e₁ : Spec.map (CommRingCat.ofHom (algebraMap Γ(baseScheme, baseOpen) Γ(scheme, affineOpen))) ≫ hW.fromSpec =
      hU.fromSpec ≫ π := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
    exact IsAffineOpen.SpecMap_appLE_fromSpec π hW hU hUW
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap Γ(baseScheme, baseOpen) Γ(multiplicativeSet, otherOpen))) ≫ hW.fromSpec =
      hV.fromSpec ≫ localizer := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
    exact IsAffineOpen.SpecMap_appLE_fromSpec localizer hW hV hVW
  have : IsOpenImmersion (pullback.map _ _ π localizer hU.fromSpec hV.fromSpec hW.fromSpec e₁ e₂) :=
    Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ e₁ e₂
  refine ⟨(pullbackSpecIso Γ(baseScheme, baseOpen) Γ(scheme, affineOpen) Γ(multiplicativeSet, otherOpen)).inv ≫
    pullback.map _ _ π localizer hU.fromSpec hV.fromSpec hW.fromSpec e₁ e₂ ≫ condition.isoPullback.inv,
    inferInstance, ?_, ?_, fun x' hxU hxV ↦ ?_⟩
  · rw [Category.assoc, Category.assoc, condition.isoPullback_inv_fst, pullback.lift_fst,
      ← Category.assoc, pullbackSpecIso_inv_fst]
  · rw [Category.assoc, Category.assoc, condition.isoPullback_inv_snd, pullback.lift_snd,
      ← Category.assoc, pullbackSpecIso_inv_snd]
    rfl
  · obtain ⟨otherValue, hy⟩ : condition.isoPullback.hom x' ∈
        Set.range (pullback.map _ _ π localizer hU.fromSpec hV.fromSpec hW.fromSpec e₁ e₂) := by
      rw [Scheme.Pullback.range_map, IsAffineOpen.range_fromSpec, IsAffineOpen.range_fromSpec]
      refine ⟨?_, ?_⟩
      · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, condition.isoPullback_hom_fst]
        exact hxU
      · rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, condition.isoPullback_hom_snd]
        exact hxV
    refine ⟨(pullbackSpecIso _ _ _).hom otherValue, ?_⟩
    simp [← Scheme.Hom.comp_apply, hy]

/-- Flatness of a closed subscheme over the base gives flatness of its affine coordinate rings. -/
lemma flat_app_subschemeι_comp_appLE {π : scheme ⟶ baseScheme} {ideal : scheme.IdealSheafData}
    (hflat : Flat (ideal.subschemeι ≫ π)) (baseOpen : baseScheme.affineOpens) (affineOpen : scheme.affineOpens)
    (hUW : affineOpen.1 ≤ π ⁻¹ᵁ baseOpen.1) :
    ((ideal.subschemeι.app affineOpen.1).hom.comp (π.appLE baseOpen affineOpen hUW).hom).Flat := by
  have := (ideal.subschemeι ≫ π).flat_appLE baseOpen.2 (affineOpen.2.preimage ideal.subschemeι)
    (ideal.subschemeι.preimage_mono hUW)
  rwa [← Scheme.Hom.appLE_comp_appLE _ _ _ affineOpen.1 _ hUW le_rfl, CommRingCat.hom_comp,
    ← Scheme.Hom.app_eq_appLE] at this

/-- An invertible ideal on an affine scheme is regular principal on a principal neighborhood of each
prime. -/
lemma IsInvertible.exists_isRegularPrincipal_map_localizationAway {ring : Type universeLevel} [CommRing ring]
    {ideal : (Spec (.of ring)).IdealSheafData} (hJ : ideal.IsInvertible) {sectionIdeal : Ideal ring}
    (hI : ideal.ideal ⟨⊤, isAffineOpen_top _⟩ = sectionIdeal.map (Scheme.ΓSpecIso (.of ring)).inv.hom)
    (primeIdeal : Ideal ring) [primeIdeal.IsPrime] :
    ∃ localizer ∉ primeIdeal, (sectionIdeal.map (algebraMap ring (Localization.Away localizer))).IsRegularPrincipal := by
  let P' : Spec (.of ring) := ⟨primeIdeal, inferInstance⟩
  obtain ⟨otherOpen, hPV, hV⟩ := hJ P'
  obtain ⟨_, ⟨localizer, rfl⟩, hPg, hgV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hPV otherOpen.1.isOpen
  let g₀ := (Scheme.ΓSpecIso (.of ring)).inv localizer
  let neighborhood := (Spec (.of ring)).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) g₀
  have hD : (neighborhood : (Spec (.of ring)).Opens) = PrimeSpectrum.basicOpen localizer :=
    basicOpen_eq_of_affine localizer
  have hDV : neighborhood ≤ otherOpen := by
    intro point hx
    rw [hD] at hx
    exact hgV hx
  have hJD : (ideal.ideal neighborhood).IsRegularPrincipal := by
    rw [← ideal.map_ideal hDV]
    exact hV.map_of_flat (Scheme.Hom.flat_appLE (𝟙 _) otherOpen.2 neighborhood.2 hDV)
  refine ⟨localizer, hPg, ?_⟩
  have hDtop : neighborhood.1 ≤ (⟨⊤, isAffineOpen_top _⟩ : (Spec (.of ring)).affineOpens).1 := le_top
  let ρ := ((Spec (.of ring)).presheaf.map (homOfLE hDtop).op).hom
  let φ := ρ.comp (Scheme.ΓSpecIso (.of ring)).inv.hom
  let := φ.toAlgebra
  have : IsLocalization.Away localizer Γ(Spec (.of ring), neighborhood) := by
    let := ρ.toAlgebra
    have := (isAffineOpen_top (Spec (.of ring))).isLocalization_of_eq_basicOpen g₀
      (homOfLE hDtop) rfl
    have := IsLocalization.isLocalization_of_base_ringEquiv (Submonoid.powers g₀)
      Γ(Spec (.of ring), neighborhood) (Scheme.ΓSpecIso (.of ring)).commRingCatIsoToRingEquiv
    have hg : (Scheme.ΓSpecIso (.of ring)).commRingCatIsoToRingEquiv g₀ = localizer :=
      Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of ring)) localizer
    rw [Submonoid.map_powers, hg] at this
    exact this
  have hφ : sectionIdeal.map φ = ideal.ideal neighborhood := by
    rw [← ideal.map_ideal hDtop, hI, Ideal.map_map]
    rfl
  let equivalence := IsLocalization.algEquiv (Submonoid.powers localizer) (Localization.Away localizer) Γ(Spec (.of ring), neighborhood)
  have he : equivalence.symm.toRingEquiv.toRingHom.comp φ = algebraMap ring (Localization.Away localizer) :=
    equivalence.symm.toAlgHom.comp_algebraMap
  rw [← hφ] at hJD
  have := hJD.map_of_bijective (f := equivalence.symm.toRingEquiv.toRingHom) equivalence.symm.toRingEquiv.bijective
  rwa [Ideal.map_map, he] at this

/-- Invertibility on a fibre gives regular principal equations on tensor-product charts of that
fibre. -/
lemma exists_isRegularPrincipal_map_tensorProduct_of_isInvertible_comap_fiberι (π : scheme ⟶ baseScheme)
    {ideal : scheme.IdealSheafData} (basePoint : baseScheme) (hJs : (ideal.comap (π.fiberι basePoint)).IsInvertible) {baseOpen : baseScheme.Opens}
    (hW : IsAffineOpen baseOpen) (hsW : ⊤ ≤ baseScheme.fromSpecResidueField basePoint ⁻¹ᵁ baseOpen) (affineOpen : scheme.affineOpens)
    (hUW : affineOpen.1 ≤ π ⁻¹ᵁ baseOpen) :
    letI := (π.appLE baseOpen affineOpen hUW).hom.toAlgebra
    letI := ((baseScheme.fromSpecResidueField basePoint).appLE baseOpen ⊤ hsW).hom.toAlgebra
    ∀ primeIdeal : Ideal (Γ(scheme, affineOpen) ⊗[Γ(baseScheme, baseOpen)] Γ(Spec (baseScheme.residueField basePoint), ⊤)), primeIdeal.IsPrime →
      ∃ localizer ∉ primeIdeal, (((ideal.ideal affineOpen).map Algebra.TensorProduct.includeLeftRingHom).map
        (algebraMap (Γ(scheme, affineOpen) ⊗[Γ(baseScheme, baseOpen)] Γ(Spec (baseScheme.residueField basePoint), ⊤))
          (Localization.Away localizer))).IsRegularPrincipal := by
  intro primeIdeal _
  obtain ⟨ι, hι, hιg, -, -⟩ := IsPullback.exists_isOpenImmersion_spec_tensorProduct
    (IsPullback.of_hasPullback π (baseScheme.fromSpecResidueField basePoint)) hW affineOpen.2 hUW (isAffineOpen_top _) hsW
  have : (ideal.comap (ι ≫ pullback.fst π (baseScheme.fromSpecResidueField basePoint))).IsInvertible := by
    rw [comap_comp]
    exact @IsInvertible.comap_of_isOpenImmersion _ _ _ hJs ι hι
  rw [hιg] at this
  exact this.exists_isRegularPrincipal_map_localizationAway
    (ideal_top_comap_specMap_ofHom_fromSpec ideal affineOpen _) primeIdeal

/-- Global sections of the spectrum of a residue field form a field. -/
lemma isField_residueField_sections (basePoint : baseScheme) : IsField Γ(Spec (baseScheme.residueField basePoint), ⊤) :=
  MulEquiv.isField (Field.toIsField (baseScheme.residueField basePoint))
    (Scheme.ΓSpecIso (baseScheme.residueField basePoint)).commRingCatIsoToRingEquiv.toMulEquiv

/-- The kernel of the coordinate map to a residue field is the prime corresponding to the base
point. -/
lemma ker_appLE_fromSpecResidueField (π : scheme ⟶ baseScheme) (basePoint : baseScheme) {baseOpen : baseScheme.Opens} (hW : IsAffineOpen baseOpen)
    (hsW : ⊤ ≤ baseScheme.fromSpecResidueField basePoint ⁻¹ᵁ baseOpen) {affineOpen : scheme.Opens} (hU : IsAffineOpen affineOpen)
    (hUW : affineOpen ≤ π ⁻¹ᵁ baseOpen) (prime : Spec Γ(scheme, affineOpen)) (hq : π (hU.fromSpec prime) = basePoint) :
    RingHom.ker ((baseScheme.fromSpecResidueField basePoint).appLE baseOpen ⊤ hsW).hom =
      prime.asIdeal.comap (π.appLE baseOpen affineOpen hUW).hom := by
  let := (isField_residueField_sections basePoint).toField
  let pt : Spec Γ(Spec (baseScheme.residueField basePoint), ⊤) := ⟨⊥, Ideal.isPrime_bot⟩
  have e₁ : hW.fromSpec (Spec.map ((baseScheme.fromSpecResidueField basePoint).appLE baseOpen ⊤ hsW) pt) = basePoint := by
    rw [← Scheme.Hom.comp_apply, IsAffineOpen.SpecMap_appLE_fromSpec _ hW (isAffineOpen_top _),
      Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have e₂ : hW.fromSpec (Spec.map (π.appLE baseOpen affineOpen hUW) prime) = basePoint := by
    rw [← Scheme.Hom.comp_apply, IsAffineOpen.SpecMap_appLE_fromSpec _ hW hU, Scheme.Hom.comp_apply,
      hq]
  have := congrArg PrimeSpectrum.asIdeal (hW.fromSpec.isOpenEmbedding.injective (e₁.trans e₂.symm))
  rw [RingHom.ker_eq_comap_bot]
  exact this

/-- A locally quasi-finite closed subscheme of a smooth curve over a field is an effective Cartier
divisor. -/
theorem isInvertible_of_locallyQuasiFinite_of_field {baseField : Type universeLevel} [Field baseField] {curve : Scheme.{universeLevel}}
    (structureMap : curve ⟶ Spec (.of baseField)) [SmoothOfRelativeDimension 1 structureMap] {ideal : curve.IdealSheafData}
    [LocallyQuasiFinite (ideal.subschemeι ≫ structureMap)] : ideal.IsInvertible := by
  have := SmoothOfRelativeDimension.smooth 1 structureMap
  have : IsLocallyNoetherian curve := LocallyOfFiniteType.isLocallyNoetherian structureMap
  have hreg (otherValue : curve) : IsRegularLocalRing (curve.presheaf.stalk otherValue) :=
    SmoothOfRelativeDimension.isRegularLocalRing_stalk structureMap 1 otherValue
  have hdim := topologicalKrullDim_le_of_smoothOfRelativeDimension structureMap 1
  have hdisc : DiscreteTopology ideal.subscheme := by
    rw [← isDiscrete_univ_iff]
    rcases isEmpty_or_nonempty ideal.subscheme with condition | ⟨⟨auxiliaryFactor⟩⟩
    · rw [Set.univ_eq_empty_iff.mpr condition]
      exact ⟨inferInstance⟩
    · convert (ideal.subschemeι ≫ structureMap).isDiscrete_preimage_singleton ((ideal.subschemeι ≫ structureMap) auxiliaryFactor)
      ext equivalence
      simp only [Set.mem_univ, Set.mem_preimage, Set.mem_singleton_iff, true_iff]
      exact Subsingleton.elim _ _
  intro point
  have : IsRegularLocalRing (curve.presheaf.stalk point) := hreg point
  by_cases hx : point ∈ ideal.support
  swap
  · obtain ⟨affineOpen, hU, hxU, hUs⟩ := exists_isAffineOpen_mem_and_subset
      (U := ⟨(ideal.support : Set curve)ᶜ, ideal.support.isClosed.isOpen_compl⟩) hx
    refine ⟨⟨affineOpen, hU⟩, hxU, 1, one_mem _, ?_⟩
    rw [Ideal.span_singleton_one]
    have emptyLocus : curve.zeroLocus (U := affineOpen) (ideal.ideal ⟨affineOpen, hU⟩) ∩
        (affineOpen : Set curve) ⊆ (∅ : Set curve) := fun candidate membership ↦
      (hUs membership.2
        (ideal.zeroLocus_inter_subset_supportSet ⟨affineOpen, hU⟩ membership)).elim
    have imageEmpty := (hU.fromSpec_image_zeroLocus _).trans_subset emptyLocus
    simp only [Set.subset_empty_iff, Set.image_eq_empty] at imageEmpty
    exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp imageEmpty
  obtain ⟨affineOpen, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := point) trivial
  let xU : affineOpen := ⟨point, hxU⟩
  set prime := hU.primeIdealOf xU with hq
  let := TopCat.Presheaf.algebra_section_stalk curve.presheaf xU
  have := hU.isLocalization_stalk xU
  have : IsNoetherianRing Γ(curve, affineOpen) := IsLocallyNoetherian.component_noetherian ⟨affineOpen, hU⟩
  obtain ⟨sectionIdeal, hIdef⟩ : ∃ sectionIdeal, sectionIdeal = ideal.ideal ⟨affineOpen, hU⟩ := ⟨_, rfl⟩
  have hmem (function : Γ(curve, affineOpen)) : point ∈ curve.basicOpen function ↔ function ∉ prime.asIdeal := by
    have equivalence : hU.fromSpec prime = point := hU.fromSpec_primeIdealOf xU
    have condition : prime ∈ hU.fromSpec ⁻¹ᵁ curve.basicOpen function ↔ prime ∈ PrimeSpectrum.basicOpen function := by
      rw [hU.fromSpec_preimage_basicOpen]
    rw [← equivalence]
    exact condition

  have hI0 : sectionIdeal.map (algebraMap Γ(curve, affineOpen) (curve.presheaf.stalk point)) ≠ ⊥ := by
    intro h0
    have hk (factor : Γ(curve, affineOpen)) (ha : factor ∈ sectionIdeal) : ∃ multiplierValue ∉ prime.asIdeal, multiplierValue * factor = 0 := by
      have : algebraMap _ (curve.presheaf.stalk point) factor = 0 := by
        rw [← Ideal.mem_bot, ← h0]
        exact Ideal.mem_map_of_mem _ ha
      obtain ⟨⟨multiplierValue, hu⟩, condition⟩ := (IsLocalization.map_eq_zero_iff prime.asIdeal.primeCompl _ factor).1 this
      exact ⟨multiplierValue, hu, condition⟩
    obtain ⟨baseScheme, hS⟩ := (IsNoetherian.noetherian sectionIdeal : sectionIdeal.FG)
    have hk' (factor : Γ(curve, affineOpen)) (ha : factor ∈ baseScheme) : ∃ multiplierValue ∉ prime.asIdeal, multiplierValue * factor = 0 := by
      refine hk factor ?_
      rw [← hS]
      exact Ideal.subset_span ha
    choose! multiplierValue hu hu' using hk'
    have hg : ∏ factor ∈ baseScheme, multiplierValue factor ∉ prime.asIdeal := prime.asIdeal.primeCompl.prod_mem fun factor ha ↦ hu factor ha
    have hgI (factor : Γ(curve, affineOpen)) (ha : factor ∈ sectionIdeal) : (∏ factor ∈ baseScheme, multiplierValue factor) * factor = 0 := by
      rw [← hS] at ha
      refine Ideal.mem_bot.1 (Ideal.mul_mem_of_mem_span_of_forall _ ⊥ _ (fun otherFactor hb ↦ ?_) ha)
      obtain ⟨multiplier, hc⟩ := Finset.dvd_prod_of_mem multiplierValue hb
      rw [Ideal.mem_bot, hc, mul_comm (multiplierValue otherFactor) multiplier, mul_assoc, hu' otherFactor hb, mul_zero]
    let openSubscheme := curve.basicOpen (∏ factor ∈ baseScheme, multiplierValue factor)
    have hZ (otherValue : curve) (hy : otherValue ∈ openSubscheme) : otherValue ∈ Set.range ideal.subschemeι := by
      rw [range_subschemeι, SetLike.mem_coe,
        mem_support_iff_of_mem (U := ⟨affineOpen, hU⟩) (curve.basicOpen_le _ hy), Scheme.mem_zeroLocus_iff,
        ← hIdef]
      intro factor ha hya
      have : otherValue ∈ curve.basicOpen ((∏ factor ∈ baseScheme, multiplierValue factor) * factor) := by
        rw [Scheme.basicOpen_mul]
        exact ⟨hy, hya⟩
      rw [hgI factor ha, Scheme.basicOpen_zero] at this
      exact this
    have : DiscreteTopology openSubscheme := by
      refine discreteTopology_iff_isOpen_singleton.mpr fun thirdValue ↦ ?_
      obtain ⟨auxiliaryFactor, hd⟩ := hZ thirdValue.1 thirdValue.2
      obtain ⟨parameter, ht, htd⟩ := ideal.subschemeι.isEmbedding.isOpen_iff.mp (isOpen_discrete {auxiliaryFactor})
      refine isOpen_induced_iff.mpr ⟨parameter, ht, Set.ext fun witness ↦ ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩⟩
      · obtain ⟨d', hd'⟩ := hZ witness.1 witness.2
        have : d' ∈ ideal.subschemeι ⁻¹' parameter := by
          rw [Set.mem_preimage, hd']
          exact hw
        rw [htd, Set.mem_singleton_iff] at this
        rw [Set.mem_singleton_iff]
        exact Subtype.ext (hd'.symm.trans (this ▸ hd))
      · rw [Set.mem_singleton_iff] at hw
        have : auxiliaryFactor ∈ ideal.subschemeι ⁻¹' parameter := htd ▸ Set.mem_singleton auxiliaryFactor
        rw [Set.mem_preimage, hd] at this
        rw [hw]
        exact this
    have : Nonempty openSubscheme := ⟨⟨point, (hmem _).mpr hg⟩⟩
    have : SmoothOfRelativeDimension 1 (openSubscheme.ι ≫ structureMap) :=
      (zero_add 1) ▸ (inferInstance : SmoothOfRelativeDimension (0 + 1) (openSubscheme.ι ≫ structureMap))
    have h1 := topologicalKrullDim_eq_of_smoothOfRelativeDimension (openSubscheme.ι ≫ structureMap) 1
    have h0 := topologicalKrullDim_zero_of_discreteTopology openSubscheme
    rw [h1] at h0
    exact absurd h0 (by norm_num)

  have : IsPrincipalIdealRing (curve.presheaf.stalk point) := by
    refine ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain _).out 5 0).mp ?_
    have condition := (IsRegularLocalRing.iff_finrank_cotangentSpace (curve.presheaf.stalk point)).mp
      inferInstance
    have local_dimension : ringKrullDim (curve.presheaf.stalk point) ≤ topologicalKrullDim curve := by
      rw [ringKrullDim_stalk_eq_coheight, topologicalKrullDim,
        Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints]
      exact Order.coheight_le_krullDim point
    have h' := local_dimension.trans hdim
    rw [← condition] at h'
    exact_mod_cast h'
  obtain ⟨parameter, ht⟩ := (IsPrincipalIdealRing.principal
    (sectionIdeal.map (algebraMap Γ(curve, affineOpen) (curve.presheaf.stalk point)))).principal
  obtain ⟨localizer, hgq, hg⟩ := Ideal.exists_notMem_isRegularPrincipal_map_away prime.asIdeal
    (curve.presheaf.stalk point) sectionIdeal (t := parameter) (by rw [ht, Ideal.submodule_span_eq])
    fun ht0 ↦ hI0 (by rw [ht, Ideal.submodule_span_eq, ht0, Ideal.span_singleton_eq_bot])
  let neighborhood := curve.affineBasicOpen (U := ⟨affineOpen, hU⟩) localizer
  have hDU : neighborhood.1 ≤ affineOpen := curve.basicOpen_le localizer
  let := (curve.presheaf.map (homOfLE hDU).op).hom.toAlgebra
  have : IsLocalization.Away localizer Γ(curve, neighborhood) := hU.isLocalization_of_eq_basicOpen localizer (homOfLE hDU) rfl
  refine ⟨neighborhood, (hmem localizer).mpr hgq, ?_⟩
  rw [← ideal.map_ideal (V := ⟨affineOpen, hU⟩) hDU, ← hIdef]
  exact hg Γ(curve, neighborhood)

/-- Local finite presentation of a closed subscheme gives finite presentation of its affine
coordinate rings. -/
lemma finitePresentation_app_subschemeι_comp_appLE {π : scheme ⟶ baseScheme} {ideal : scheme.IdealSheafData}
    (hlfp : LocallyOfFinitePresentation (ideal.subschemeι ≫ π)) (baseOpen : baseScheme.affineOpens)
    (affineOpen : scheme.affineOpens) (hUW : affineOpen.1 ≤ π ⁻¹ᵁ baseOpen.1) :
    ((ideal.subschemeι.app affineOpen.1).hom.comp (π.appLE baseOpen affineOpen hUW).hom).FinitePresentation := by
  have := HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) _ hlfp baseOpen
    ⟨_, affineOpen.2.preimage ideal.subschemeι⟩ (ideal.subschemeι.preimage_mono hUW)
  rwa [← Scheme.Hom.appLE_comp_appLE _ _ _ affineOpen.1 _ hUW le_rfl, CommRingCat.hom_comp,
    ← Scheme.Hom.app_eq_appLE] at this

/-- A locally quasi-finite closed subscheme remains locally quasi-finite after base change. -/
theorem locallyQuasiFinite_comap_subschemeι_comp_of_isPullback {π : scheme ⟶ baseScheme}
    {ideal : scheme.IdealSheafData} (hqf : LocallyQuasiFinite (ideal.subschemeι ≫ π)) {X' multiplicativeSet : Scheme.{universeLevel}}
    {g' : X' ⟶ scheme} {π' : X' ⟶ multiplicativeSet} {localizer : multiplicativeSet ⟶ baseScheme} (condition : IsPullback g' π' π localizer) :
    LocallyQuasiFinite ((ideal.comap g').subschemeι ≫ π') := by
  have sq : IsPullback (pullback.snd g' ideal.subschemeι) (pullback.fst g' ideal.subschemeι ≫ π')
      (ideal.subschemeι ≫ π) localizer := (IsPullback.of_hasPullback g' ideal.subschemeι).flip.paste_vert condition
  have auxiliaryProperty := MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) sq hqf
  have H' : LocallyQuasiFinite (ideal.comapIso g').hom := inferInstance
  rw [← comapIso_hom_fst, Category.assoc]
  exact MorphismProperty.comp_mem @LocallyQuasiFinite _ _ H' auxiliaryProperty

/-- A flat locally quasi-finite closed subscheme of finite presentation in a smooth relative curve
is an effective Cartier divisor. -/
theorem isInvertible_of_locallyQuasiFinite_of_flat (π : scheme ⟶ baseScheme) [SmoothOfRelativeDimension 1 π]
    {ideal : scheme.IdealSheafData} (hqf : LocallyQuasiFinite (ideal.subschemeι ≫ π))
    (hflat : Flat (ideal.subschemeι ≫ π)) (hlfp : LocallyOfFinitePresentation (ideal.subschemeι ≫ π)) :
    ideal.IsInvertible := by
  have := SmoothOfRelativeDimension.smooth 1 π
  intro point
  obtain ⟨baseOpen, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (x := π point) (U := ⊤) trivial
  obtain ⟨affineOpen, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset (U := π ⁻¹ᵁ baseOpen) (x := point) hsW
  obtain ⟨prime, hq⟩ : point ∈ Set.range hU.fromSpec := by
    rw [IsAffineOpen.range_fromSpec]
    exact hxU
  have hsW' : ⊤ ≤ baseScheme.fromSpecResidueField (π point) ⁻¹ᵁ baseOpen := fun otherValue _ ↦ by
    rw [Scheme.Hom.mem_preimage, Scheme.fromSpecResidueField_apply]
    exact hsW
  have hfib : (ideal.comap (π.fiberι (π point))).IsInvertible := by
    have : SmoothOfRelativeDimension 1
        (pullback.snd π (baseScheme.fromSpecResidueField (π point))) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
        (IsPullback.of_hasPullback π (baseScheme.fromSpecResidueField (π point)))
        inferInstance
    have := locallyQuasiFinite_comap_subschemeι_comp_of_isPullback hqf
      (IsPullback.of_hasPullback π (baseScheme.fromSpecResidueField (π point)))
    exact @isInvertible_of_locallyQuasiFinite_of_field (baseScheme.residueField (π point)) _ _
      (pullback.snd π (baseScheme.fromSpecResidueField (π point))) _
      (ideal.comap (pullback.fst π (baseScheme.fromSpecResidueField (π point)))) this
  let := (π.appLE baseOpen affineOpen hUW).hom.toAlgebra
  let := ((baseScheme.fromSpecResidueField (π point)).appLE baseOpen ⊤ hsW').hom.toAlgebra
  have : Module.Flat Γ(baseScheme, baseOpen) Γ(scheme, affineOpen) := π.flat_appLE hW hU hUW
  have : Algebra.FinitePresentation Γ(baseScheme, baseOpen) Γ(scheme, affineOpen) :=
    HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) π inferInstance ⟨baseOpen, hW⟩
      ⟨affineOpen, hU⟩ hUW
  have := prime.isPrime
  obtain ⟨localizer, hgq, hg⟩ := Algebra.exists_notMem_isRegularPrincipal_of_flat_of_fiber
    (isField_residueField_sections _) (ideal.subschemeι.app affineOpen).hom
    (ideal.subschemeι_app_surjective ⟨affineOpen, hU⟩)
    (flat_app_subschemeι_comp_appLE hflat ⟨baseOpen, hW⟩ ⟨affineOpen, hU⟩ hUW)
    (finitePresentation_app_subschemeι_comp_appLE hlfp ⟨baseOpen, hW⟩ ⟨affineOpen, hU⟩ hUW) prime.asIdeal
    (ker_appLE_fromSpecResidueField π _ hW hsW' hU hUW prime (by rw [hq]))
    (by
      rw [ker_subschemeι_app ideal ⟨affineOpen, hU⟩]
      exact exists_isRegularPrincipal_map_tensorProduct_of_isInvertible_comap_fiberι π _ hfib
        hW hsW' ⟨affineOpen, hU⟩ hUW)
  let neighborhood := scheme.affineBasicOpen (U := ⟨affineOpen, hU⟩) localizer
  have hDU : neighborhood.1 ≤ affineOpen := scheme.basicOpen_le localizer
  let := (scheme.presheaf.map (homOfLE hDU).op).hom.toAlgebra
  have : IsLocalization.Away localizer Γ(scheme, neighborhood) := hU.isLocalization_of_eq_basicOpen localizer (homOfLE hDU) rfl
  refine ⟨neighborhood, ?_, ?_⟩
  · have : prime ∈ hU.fromSpec ⁻¹ᵁ scheme.basicOpen localizer := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact hgq
    rw [← hq]
    exact this
  · rw [← ideal.map_ideal (V := ⟨affineOpen, hU⟩) hDU, ← ker_subschemeι_app ideal ⟨affineOpen, hU⟩]
    exact hg Γ(scheme, neighborhood)

/-- A finite flat closed subscheme of finite presentation in a smooth relative curve has an
invertible ideal. -/
theorem isInvertible_of_isFinite_of_flat (π : scheme ⟶ baseScheme) [SmoothOfRelativeDimension 1 π]
    {ideal : scheme.IdealSheafData} (hfin : IsFinite (ideal.subschemeι ≫ π)) (hflat : Flat (ideal.subschemeι ≫ π))
    (hlfp : LocallyOfFinitePresentation (ideal.subschemeι ≫ π)) : ideal.IsInvertible := by
  letI : IsFinite (ideal.subschemeι ≫ π) := hfin
  exact isInvertible_of_locallyQuasiFinite_of_flat π inferInstance hflat hlfp

/-- A finite flat closed subscheme of finite presentation in a smooth relative curve is a relative
effective Cartier divisor. -/
theorem isRelativeEffectiveCartier_of_isFinite (π : scheme ⟶ baseScheme) [SmoothOfRelativeDimension 1 π]
    {ideal : scheme.IdealSheafData} [IsFinite (ideal.subschemeι ≫ π)] [Flat (ideal.subschemeι ≫ π)]
    [LocallyOfFinitePresentation (ideal.subschemeι ≫ π)] :
    ideal.IsRelativeEffectiveCartier π :=
  ⟨isInvertible_of_isFinite_of_flat π inferInstance inferInstance inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.IdealSheafData
