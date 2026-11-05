import Mathlib.Algebra.Module.SpanRank
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Domains and discrete valuation rings from regular local rings

Regular local rings are domains, by induction on the number of generators of
 the maximal ideal. In dimension one the maximal ideal is principal, so the
 ring is a discrete valuation ring.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open IsLocalRing

/-- Quotienting by an element nonzero in the cotangent space removes a maximal-ideal generator. -/
theorem IsLocalRing.spanFinrank_map_quotient_span_singleton_add_one_le {ring : Type*} [CommRing ring]
    [IsLocalRing ring] [IsNoetherianRing ring] {point : ring}
    (hx : point ∈ maximalIdeal ring) (hx2 : point ∉ maximalIdeal ring ^ 2) :
    ((maximalIdeal ring).map (Ideal.Quotient.mk (Ideal.span {point}))).spanFinrank + 1 ≤
      (maximalIdeal ring).spanFinrank := by
  classical
  set maximalIdealLocal := maximalIdeal ring
  set v := maximalIdealLocal.toCotangent ⟨point, hx⟩
  have hv : v ≠ 0 := by rwa [Ne, Ideal.toCotangent_eq_zero]
  have hs : LinearIndepOn (ResidueField ring) id {v} := LinearIndepOn.singleton hv
  set basisIndex := hs.extend (Set.subset_univ _)
  have hvB : v ∈ basisIndex := hs.subset_extend _ rfl
  let basis := Module.Basis.extend hs
  have hBfin : basisIndex.Finite := Set.toFinite basisIndex
  have hBcard : basisIndex.ncard = maximalIdealLocal.spanFinrank := by
    rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, Module.finrank_eq_nat_card_basis basis,
      Nat.card_coe_set_eq]
  let ringMap : CotangentSpace ring → maximalIdealLocal := Function.surjInv maximalIdealLocal.toCotangent_surjective
  have hg (w) : maximalIdealLocal.toCotangent (ringMap w) = w := Function.surjInv_eq _ w
  set closedSet : Set maximalIdealLocal := insert ⟨point, hx⟩ (ringMap '' (basisIndex \ {v}))
  have himg : maximalIdealLocal.toCotangent '' closedSet = basisIndex := by
    rw [Set.image_insert_eq, Set.image_image]
    simp only [hg, Set.image_id']
    exact Set.insert_sdiff_singleton.trans (Set.insert_eq_of_mem hvB)
  have hspan : Submodule.span ring closedSet = ⊤ := by
    rw [← CotangentSpace.span_image_eq_top_iff, himg]
    simpa [basis, Module.Basis.coe_extend] using basis.span_eq
  have hm : maximalIdealLocal = Ideal.span (Subtype.val '' closedSet) := by
    change maximalIdealLocal = Submodule.span ring (maximalIdealLocal.subtype '' closedSet)
    rw [Submodule.span_image, hspan, Submodule.map_top, Submodule.range_subtype]
  have hmap : maximalIdealLocal.map (Ideal.Quotient.mk (Ideal.span {point})) =
      Ideal.span ((fun w ↦ Ideal.Quotient.mk (Ideal.span {point}) (ringMap w : ring)) '' (basisIndex \ {v})) := by
    conv_lhs => rw [hm]
    rw [Ideal.map_span, Set.image_image, Set.image_insert_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self point)]
    unfold Ideal.span
    rw [Submodule.span_insert_zero, Set.image_image]
  rw [hmap]
  calc _ ≤ ((fun w ↦ Ideal.Quotient.mk (Ideal.span {point}) (ringMap w : ring)) '' (basisIndex \ {v})).ncard + 1 := by
        gcongr
        exact Submodule.spanFinrank_span_le_ncard_of_finite ((hBfin.sdiff).image _)
    _ ≤ (basisIndex \ {v}).ncard + 1 := by gcongr; exact Set.ncard_image_le hBfin.sdiff
    _ = maximalIdealLocal.spanFinrank := by
        rw [Set.ncard_sdiff_singleton_add_one hvB hBfin, hBcard]


/-- Quotienting a regular local ring by a cotangent-space generator preserves regularity. -/
theorem IsRegularLocalRing.quotient_span_singleton {ring : Type u} [CommRing ring] [IsRegularLocalRing ring]
    {point : ring} (hx : point ∈ maximalIdeal ring) (hx2 : point ∉ maximalIdeal ring ^ 2) :
    ∃ _ : IsLocalRing (ring ⧸ Ideal.span {point}), IsRegularLocalRing (ring ⧸ Ideal.span {point}) ∧
      (maximalIdeal (ring ⧸ Ideal.span {point})).spanFinrank + 1 = (maximalIdeal ring).spanFinrank := by
  have hne : Ideal.span {point} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (mem_maximalIdeal point).1 hx
  have : Nontrivial (ring ⧸ Ideal.span {point}) := Ideal.Quotient.nontrivial_iff.2 hne
  have hloc : IsLocalRing (ring ⧸ Ideal.span {point}) :=
    .of_surjective' _ Ideal.Quotient.mk_surjective
  have hmax := map_maximalIdeal_of_surjective _ (Ideal.Quotient.mk_surjective (I := Ideal.span {point}))
  have h1 := IsLocalRing.spanFinrank_map_quotient_span_singleton_add_one_le hx hx2
  rw [hmax] at h1
  have h2 : ringKrullDim ring ≤ ringKrullDim (ring ⧸ Ideal.span {point}) + 1 := by
    have := ringKrullDim_le_ringKrullDim_quotient_add_card {point} (by
      simpa [ringJacobson_eq_maximalIdeal] using hx)
    rwa [Finset.coe_singleton, Finset.card_singleton, Nat.cast_one] at this
  have h3 := ringKrullDim_le_spanFinrank_maximalIdeal (R := ring ⧸ Ideal.span {point})
  have h4 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := ring)
  have h5 : (0 : WithBot ℕ∞) ≤ ringKrullDim (ring ⧸ Ideal.span {point}) :=
    ringKrullDim_nonneg_of_nontrivial
  set equivalence := (maximalIdeal (ring ⧸ Ideal.span {point})).spanFinrank
  set codimension := (maximalIdeal ring).spanFinrank
  obtain ⟨dimension, hn⟩ : ∃ dimension : ℕ, ringKrullDim (ring ⧸ Ideal.span {point}) = dimension := by
    obtain ⟨element, ha⟩ := WithBot.ne_bot_iff_exists.1 (ne_bot_of_le_ne_bot WithBot.coe_ne_bot h5)
    rw [← ha] at h3
    have ha' : element ≤ equivalence := by exact_mod_cast h3
    obtain ⟨dimension, rfl⟩ : ∃ dimension : ℕ, element = dimension :=
      ⟨element.toNat, (ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top equivalence) ha')).symm⟩
    exact ⟨dimension, ha.symm⟩
  rw [hn] at h2 h3
  rw [← h4] at h2
  have h2' : codimension ≤ dimension + 1 := by exact_mod_cast h2
  have h3' : dimension ≤ equivalence := by exact_mod_cast h3
  refine ⟨hloc, (isRegularLocalRing_iff _).2 ?_, by omega⟩
  rw [hn]
  congr 1
  omega


/-- A regular local ring with finitely many maximal-ideal generators is a domain. -/
theorem IsRegularLocalRing.isDomain_of_spanFinrank_eq :
    ∀ (dimension : ℕ) (ring : Type u) [CommRing ring] [IsRegularLocalRing ring],
      (maximalIdeal ring).spanFinrank = dimension → IsDomain ring
  | 0, ring, _, _, dimension_bound => by
    rw [Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal ring).fg_of_isNoetherianRing,
      ← isField_iff_maximalIdeal_eq] at dimension_bound
    let := dimension_bound.toField
    infer_instance
  | dimension + 1, ring, _, _, dimension_bound => by
    classical
    set maximalIdealLocal := maximalIdeal ring
    have hdim : ringKrullDim ring = (dimension + 1 : ℕ) := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, dimension_bound]
    have hfin := minimalPrimes.finite_of_isNoetherianRing ring
    let morphism : Option (Ideal ring) → Ideal ring := fun i ↦ i.elim (maximalIdealLocal ^ 2) id
    let finiteSet : Finset (Option (Ideal ring)) := insert none (hfin.toFinset.image some)
    have hnot : ¬ (maximalIdealLocal : Set ring) ⊆ ⋃ i ∈ (finiteSet : Set (Option (Ideal ring))), (morphism i : Set ring) := by
      rw [Ideal.subset_union_prime none none (by
        rintro (_ | prime) hp h1 -
        · exact absurd rfl h1
        · simp only [finiteSet, Finset.mem_insert, reduceCtorEq, Finset.mem_image, Set.Finite.mem_toFinset,
            Option.some.injEq, exists_eq_right, false_or] at hp
          exact hp.1.1)]
      rintro ⟨_ | prime, hp, hle⟩
      · have : maximalIdealLocal = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot maximalIdealLocal maximalIdealLocal
          maximalIdealLocal.fg_of_isNoetherianRing (by rw [smul_eq_mul, ← pow_two]; exact hle)
          (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top])
        rw [this, Submodule.spanFinrank_bot] at dimension_bound
        omega
      · simp only [finiteSet, Finset.mem_insert, reduceCtorEq, Finset.mem_image, Set.Finite.mem_toFinset,
          Option.some.injEq, exists_eq_right, false_or] at hp
        have hpm : prime = maximalIdealLocal := le_antisymm (le_maximalIdeal hp.1.1.ne_top) hle
        have := Ideal.height_eq_zero_iff.2 (hpm ▸ hp)
        rw [← maximalIdeal_height_eq_ringKrullDim, this] at hdim
        have : (0 : ℕ) = dimension + 1 := by exact_mod_cast hdim
        omega
    obtain ⟨point, hxm, hx⟩ := Set.not_subset.1 hnot
    simp only [Set.mem_iUnion, not_exists] at hx
    have hx2 : point ∉ maximalIdealLocal ^ 2 := hx none (by simp [finiteSet])
    have hxp (prime : Ideal ring) (hp : prime ∈ minimalPrimes ring) : point ∉ prime :=
      hx (some prime) (by simp only [finiteSet, Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff,
        reduceCtorEq, Set.mem_image, Finset.mem_coe, Set.Finite.mem_toFinset, Option.some.injEq,
        exists_eq_right, false_or]; exact hp)
    obtain ⟨_, hreg, hrank⟩ := IsRegularLocalRing.quotient_span_singleton hxm hx2
    have := isDomain_of_spanFinrank_eq dimension (ring ⧸ Ideal.span {point}) (by
      have := hrank.trans dimension_bound
      omega)
    have hprime := (Ideal.Quotient.isDomain_iff_prime _).1 this
    obtain ⟨prime, hp, hpx⟩ := Ideal.exists_minimalPrimes_le (bot_le (a := Ideal.span {point}))
    have hp' : prime ∈ minimalPrimes ring := hp
    have : prime = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot maximalIdealLocal prime prime.fg_of_isNoetherianRing
        (fun otherPoint hy ↦ ?_) (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top])
      obtain ⟨thirdPoint, rfl⟩ := Ideal.mem_span_singleton'.1 (hpx hy)
      have hz : thirdPoint ∈ prime := (hp'.1.1.mem_or_mem hy).resolve_right (hxp prime hp')
      rw [mul_comm]
      exact Submodule.smul_mem_smul hxm hz
    have hbot : (⊥ : Ideal ring).IsPrime := this ▸ hp'.1.1
    exact IsDomain.of_bot_isPrime ring


/-- Every regular local ring is an integral domain. -/
instance IsRegularLocalRing.isDomain (ring : Type*) [CommRing ring] [IsRegularLocalRing ring] :
    IsDomain ring :=
  isDomain_of_spanFinrank_eq _ ring rfl

/-- A one-dimensional regular local ring is a discrete valuation ring. -/
theorem IsRegularLocalRing.isDiscreteValuationRing (ring : Type*) [CommRing ring]
    [IsRegularLocalRing ring] (dimension : ringKrullDim ring = 1) :
    IsDiscreteValuationRing ring := by
  apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
  have equality := (IsRegularLocalRing.iff_finrank_cotangentSpace (R := ring)).mp
    (inferInstance : IsRegularLocalRing ring)
  rw [dimension] at equality
  exact_mod_cast equality
