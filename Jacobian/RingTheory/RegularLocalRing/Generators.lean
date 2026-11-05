import Jacobian.RingTheory.RegularLocalRing.Domain
import Jacobian.RingTheory.KrullDimension.Quotient
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Independent equations for regular local quotients

An ideal with regular local quotient in a regular local ring admits generators
whose images in the cotangent space are linearly independent.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open IsLocalRing


/-- In a noetherian local ring, the cotangent space has dimension the number of elements of any
linearly independent family spanning it. -/
theorem IsLocalRing.spanFinrank_maximalIdeal_eq_ncard {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {b : Set (maximalIdeal R)} (hfin : b.Finite)
    (hb : LinearIndepOn (ResidueField R) (maximalIdeal R).toCotangent b)
    (hspan : Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' b) = ⊤) :
    (maximalIdeal R).spanFinrank = b.ncard := by
  have := (hfin.image (maximalIdeal R).toCotangent).fintype
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, ← finrank_top, ← hspan,
    finrank_span_set_eq_card hb.id_image, ← Set.ncard_eq_toFinset_card',
    hb.injOn.ncard_image]

/-- A Krull dimension bounded by natural numbers is a natural number. -/
private theorem WithBot.exists_natCast_eq_of_le {d : WithBot ℕ∞} (h₀ : 0 ≤ d) {e : ℕ}
    (h : d ≤ e) : ∃ n : ℕ, d = n := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h₀
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((e : ℕ∞) : WithBot ℕ∞) := h
      exact absurd (top_le_iff.1 (WithBot.coe_le_coe.1 this)) (ENat.natCast_ne_top e)
    | coe a => exact ⟨a, rfl⟩

/-- A regular local quotient is cut out by equations independent in the cotangent space. -/
theorem IsRegularLocalRing.exists_span_eq_of_isRegularLocalRing_quotient {R : Type u}
    [CommRing R] [IsRegularLocalRing R] (I : Ideal R) (hI : I ≤ maximalIdeal R)
    [IsRegularLocalRing (R ⧸ I)] :
    ∃ s : Set (maximalIdeal R), s.Finite ∧ Ideal.span (Subtype.val '' s) = I ∧
      LinearIndepOn (ResidueField R) (maximalIdeal R).toCotangent s := by
  classical
  set m := maximalIdeal R
  set t : Set m := {x | (x : R) ∈ I}
  obtain ⟨s, hst, -, hts, hs⟩ := exists_linearIndepOn_extension (v := m.toCotangent)
    (linearIndepOn_empty (ResidueField R) _) (Set.empty_subset t)
  obtain ⟨b, -, hsb, hb_span, hb⟩ := exists_linearIndepOn_extension hs (Set.subset_univ s)
  have hspan_b : Submodule.span (ResidueField R) (m.toCotangent '' b) = ⊤ := by
    rw [eq_top_iff]
    rintro v -
    obtain ⟨x, rfl⟩ := m.toCotangent_surjective v
    exact hb_span ⟨x, trivial, rfl⟩
  have : Finite b := LinearIndependent.finite_of_isNoetherian hb
  have hbfin : b.Finite := Set.toFinite b
  have hsfin := hbfin.subset hsb
  have hn : m.spanFinrank = b.ncard := spanFinrank_maximalIdeal_eq_ncard hbfin hb hspan_b
  have hdimR : ringKrullDim R = b.ncard := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, hn]
  have hcard : (b \ s).ncard + s.ncard = b.ncard := Set.ncard_sdiff_add_ncard_of_subset hsb hbfin
  have hm : m = Ideal.span (Subtype.val '' b) := by
    have : Submodule.span R b = ⊤ := CotangentSpace.span_image_eq_top_iff.1 hspan_b
    change m = Submodule.span R (m.subtype '' b)
    rw [Submodule.span_image, this, Submodule.map_top, Submodule.range_subtype]
  set J := Ideal.span (Subtype.val '' s)
  have hJI : J ≤ I := Ideal.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hst hx)
  have hJne : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (hJI.trans hI)
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJne
  have : IsLocalRing (R ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hmapJ : maximalIdeal (R ⧸ J) =
      Ideal.span ((fun x : m ↦ Ideal.Quotient.mk J x) '' (b \ s)) := by
    rw [← map_maximalIdeal_of_surjective _ (Ideal.Quotient.mk_surjective (I := J))]
    conv_lhs => rw [show maximalIdeal R = Ideal.span (Subtype.val '' b) from hm]
    rw [Ideal.map_span, Set.image_image]
    refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono (Set.image_mono Set.sdiff_subset))
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxs : x ∈ s
    · change Ideal.Quotient.mk J x ∈ _
      rw [Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.subset_span (Set.mem_image_of_mem Subtype.val hxs))]
      exact zero_mem _
    · exact Ideal.subset_span ⟨x, ⟨hx, hxs⟩, rfl⟩
  have hembJ : (maximalIdeal (R ⧸ J)).spanFinrank ≤ (b \ s).ncard := by
    rw [hmapJ]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (hbfin.sdiff.image _)).trans
      (Set.ncard_image_le hbfin.sdiff)
  have hkrull : ringKrullDim R ≤ ringKrullDim (R ⧸ J) + s.ncard := by
    have := ringKrullDim_le_ringKrullDim_quotient_add_card (hsfin.toFinset.image Subtype.val)
      (by
        intro x hx
        simp only [Finset.coe_image, Set.Finite.coe_toFinset, Set.mem_image] at hx
        obtain ⟨y, -, rfl⟩ := hx
        rw [ringJacobson_eq_maximalIdeal]
        exact y.2)
    rwa [Finset.coe_image, Set.Finite.coe_toFinset,
      Finset.card_image_of_injective _ Subtype.val_injective,
      ← Set.ncard_eq_toFinset_card s hsfin] at this
  have hdim : ringKrullDim (R ⧸ J) ≤ ((b \ s).ncard : ℕ) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ J)).trans (by exact_mod_cast hembJ)
  obtain ⟨d, hd⟩ := WithBot.exists_natCast_eq_of_le ringKrullDim_nonneg_of_nontrivial hdim
  have hd₁ : d ≤ (b \ s).ncard := by
    rw [hd] at hdim
    exact_mod_cast hdim
  have hd₂ : b.ncard ≤ d + s.ncard := by
    rw [hdimR, hd] at hkrull
    exact_mod_cast hkrull
  have : IsRegularLocalRing (R ⧸ J) := .of_spanFinrank_maximalIdeal_le _ (by
    rw [hd]
    exact_mod_cast hembJ.trans (by omega))
  refine ⟨s, hsfin, ?_, hs⟩
  by_contra hne
  have hne' : I.map (Ideal.Quotient.mk J) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact fun h ↦ hne (le_antisymm hJI h)
  have h₁ := ringKrullDim_quotient_add_one_le_of_ne_bot hne'
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJI), hd,
    ← IsRegularLocalRing.spanFinrank_maximalIdeal] at h₁
  set e := (maximalIdeal (R ⧸ I)).spanFinrank
  have h₁' : e + 1 ≤ d := by exact_mod_cast h₁
  obtain ⟨H, hHcard, hHspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal (R ⧸ I)))
  have hlift (h : R ⧸ I) (hh : h ∈ maximalIdeal (R ⧸ I)) :
      ∃ y : m, Ideal.Quotient.mk I y = h := by
    rw [← map_maximalIdeal_of_surjective _ (Ideal.Quotient.mk_surjective (I := I)),
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hh
    obtain ⟨y, hy, rfl⟩ := hh
    exact ⟨⟨y, hy⟩, rfl⟩
  choose! g hg using hlift
  have hHm (h) (hh : h ∈ H) : h ∈ maximalIdeal (R ⧸ I) := hHspan ▸ Ideal.subset_span hh
  set L : Set m := g '' (H : Set (R ⧸ I))
  have hLfin : L.Finite := (H.finite_toSet).image g
  have hLcard : L.ncard ≤ e := by
    rw [show e = H.card from hHcard.symm, ← Set.ncard_coe_finset]
    exact Set.ncard_image_le H.finite_toSet
  have htop : Submodule.span R (t ∪ L) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    have hy : Ideal.Quotient.mk I (y : R) ∈ maximalIdeal (R ⧸ I) := by
      rw [← map_maximalIdeal_of_surjective _ (Ideal.Quotient.mk_surjective (I := I))]
      exact Ideal.mem_map_of_mem _ y.2
    rw [← hHspan, Submodule.mem_span_finset] at hy
    obtain ⟨c, -, hc⟩ := hy
    choose r hr using fun h : R ⧸ I ↦ Ideal.Quotient.mk_surjective (c h)
    set z : m := y - ∑ h ∈ H, r h • g h
    have hz : z ∈ t := by
      change ((y - ∑ h ∈ H, r h • g h : m) : R) ∈ I
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [AddSubgroupClass.coe_sub, Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul,
        map_sub, map_sum, map_mul, hr]
      rw [← hc, sub_eq_zero]
      exact Finset.sum_congr rfl fun h hh ↦ by rw [hg h (hHm h hh), smul_eq_mul]
    have : y = z + ∑ h ∈ H, r h • g h := by simp [z]
    rw [this]
    refine add_mem (Submodule.subset_span (Or.inl hz)) (sum_mem fun h hh ↦ ?_)
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨h, hh, rfl⟩))
  rw [← CotangentSpace.span_image_eq_top_iff, Set.image_union, Submodule.span_union] at htop
  have hle : (⊤ : Submodule (ResidueField R) (CotangentSpace R)) ≤
      Submodule.span (ResidueField R) (m.toCotangent '' s) ⊔
        Submodule.span (ResidueField R) (m.toCotangent '' L) := by
    rw [← htop]
    exact sup_le_sup_right (Submodule.span_le.2 hts) _
  have := (hsfin.image m.toCotangent).fintype
  have := (hLfin.image m.toCotangent).fintype
  have hfin := (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)
  rw [finrank_top, ← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hn] at hfin
  have h₂ : Module.finrank (ResidueField R) (Submodule.span (ResidueField R)
      (m.toCotangent '' s : Set (CotangentSpace R))) ≤ (m.toCotangent '' s).ncard := by
    rw [Set.ncard_eq_toFinset_card']
    exact finrank_span_le_card _
  have h₃ : Module.finrank (ResidueField R) (Submodule.span (ResidueField R)
      (m.toCotangent '' L : Set (CotangentSpace R))) ≤ (m.toCotangent '' L).ncard := by
    rw [Set.ncard_eq_toFinset_card']
    exact finrank_span_le_card _
  have h₄ := Set.ncard_image_le (f := m.toCotangent) hsfin
  have h₅ := Set.ncard_image_le (f := m.toCotangent) hLfin
  omega
