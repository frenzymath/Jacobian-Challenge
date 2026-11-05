import Jacobian.AlgebraicGeometry.AffineScheme.FiniteSet
import Jacobian.AlgebraicGeometry.Hilbert.AffineRepresentability
import Jacobian.AlgebraicGeometry.Hilbert.OpenImmersion
import Jacobian.AlgebraicGeometry.Morphisms.FiniteRank

/-!
# Representability and separatedness of the Hilbert functor

For a separated morphism, affine open neighborhoods of finite subsets of fibers
supply a cover of the Hilbert functor by the Hilbert schemes of affine restrictions.
The finite flat rank bounds the number of fiber points needed for these neighborhoods.
The diagonal of a representing scheme is closed, by the closed containment loci.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- For a separated morphism, the degree-`d` Hilbert functor is representable
if every set of at most `d` points in a fiber lies in one affine open of the source.
The representing schemes of affine restrictions glue along their open support loci. -/
theorem isRepresentable_hilbertPresheaf (f : X ⟶ S) [IsSeparated f] (d : ℕ)
    (hf : ∀ (s : S) (t : Finset (f.fiber s)), t.card ≤ d →
      ∃ U : X.affineOpens, ∀ x ∈ t, (f.fiberι s).base x ∈ U.1) :
    (hilbertPresheaf f d).IsRepresentable := by
  let P := hilbertPresheaf f d
  let ι := {p : S.affineOpens × X.affineOpens // p.2.1 ≤ f ⁻¹ᵁ p.1.1}
  have hrep (i : ι) := (isRepresentable_hilbertPresheaf_of_isAffine
    (f.resLE i.1.1.1 i.1.2.1 i.2) d).has_representation
  choose Y hY using hrep
  let e (i : ι) := (hY i).some
  let Φ (i : ι) := hilbertPresheafResLEι f i.2 d
  let X' (i : ι) : Over S := (Over.map i.1.1.1.ι).obj (Y i)
  let ξ (i : ι) : P.obj (op (X' i)) := (Φ i).app (op (Y i)) ((e i).homEquiv (𝟙 _))
  have hξ (i : ι) {W' : Over i.1.1.1.toScheme} (b' : W' ⟶ Y i) :
      P.map ((Over.map i.1.1.1.ι).map b').op (ξ i) = (Φ i).app (op W') ((e i).homEquiv b') := by
    rw [← Category.comp_id b', (e i).homEquiv_comp]
    exact (NatTrans.naturality_apply (Φ i) b'.op _).symm
  have hlift (i : ι) (W : Over S) (hW : Set.range W.hom ⊆ i.1.1.1) :
      ∃ (W' : Over i.1.1.1.toScheme) (ε : (Over.map i.1.1.1.ι).obj W' ≅ W),
        ∀ c : W ⟶ X' i, ∃ c' : W' ⟶ Y i, (Over.map i.1.1.1.ι).map c' = ε.hom ≫ c := by
    have hW' : Set.range W.hom ⊆ Set.range i.1.1.1.ι := by rwa [Scheme.Opens.range_ι]
    refine ⟨Over.mk (IsOpenImmersion.lift _ _ hW'),
      Over.isoMk (Iso.refl _) (by simp [IsOpenImmersion.lift_fac]), fun c ↦ ?_⟩
    have hc : c.left ≫ (Y i).hom = IsOpenImmersion.lift _ _ hW' := by
      rw [← cancel_mono i.1.1.1.ι]
      simpa [IsOpenImmersion.lift_fac, X'] using Over.w c
    exact ⟨Over.homMk c.left hc, by ext; simp⟩
  have hrange (i : ι) {W : Over S} (c : W ⟶ X' i) : Set.range W.hom ⊆ i.1.1.1 := by
    rw [← Over.w c]
    rintro _ ⟨w, rfl⟩
    simp [X']
  have hP {T W : Over S} (a : W ⟶ T) (x : P.obj (op T)) :
      (P.map a.op x).1 = x.1.comap (baseChangeMap f a) := rfl
  have hPiso {W W' : Over S} (ε : W' ≅ W) (x : P.obj (op W)) :
      P.map ε.inv.op (P.map ε.hom.op x) = x := by
    rw [← Functor.map_comp_apply, ← op_comp, ε.inv_hom_id, op_id, Functor.map_id_apply]
  have hPiso' {W W' : Over S} (ε : W' ≅ W) (x : P.obj (op W')) :
      P.map ε.hom.op (P.map ε.inv.op x) = x := by
    rw [← Functor.map_comp_apply, ← op_comp, ε.hom_inv_id, op_id, Functor.map_id_apply]
  have hinj (i : ι) {T : Over S} (a b : T ⟶ X' i) (hab : P.map a.op (ξ i) = P.map b.op (ξ i)) :
      a = b := by
    obtain ⟨W', ε, hc⟩ := hlift i T (hrange i a)
    obtain ⟨a', ha'⟩ := hc a
    obtain ⟨b', hb'⟩ := hc b
    have ha : a = ε.inv ≫ (Over.map i.1.1.1.ι).map a' := by simp [ha']
    have hb : b = ε.inv ≫ (Over.map i.1.1.1.ι).map b' := by simp [hb']
    rw [ha, hb, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
      hξ, hξ] at hab
    have hab' := congrArg (P.map ε.hom.op) hab
    rw [hPiso', hPiso'] at hab'
    have := hilbertPresheafResLEι_app_injective f i.2 d W' hab'
    rw [ha, hb, (e i).homEquiv.injective this]
  have hopen' (i : ι) (T : Over S) (x : P.obj (op T)) : ∃ O : T.left.Opens,
      (∀ t, t ∈ O ↔ T.hom t ∈ i.1.1.1 ∧ ∀ z ∈ x.1.support, pullback.snd f T.hom z = t →
        pullback.fst f T.hom z ∈ i.1.2.1) ∧
      ∀ (W : Over S) (a : W ⟶ T),
        (∃ b : W ⟶ X' i, P.map a.op x = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ O := by
    have := x.2.1
    obtain ⟨O, hOmem, hO⟩ := x.1.exists_opens_support_comap_subset f i.1.2.1
    refine ⟨T.hom ⁻¹ᵁ i.1.1.1 ⊓ O, fun t ↦ ?_, fun W a ↦ ?_⟩
    · rw [← hOmem]
      rfl
    change _ ↔ Set.range a.left ⊆ T.hom ⁻¹' i.1.1.1 ∩ O
    rw [Set.subset_inter_iff, ← hO]
    constructor
    · rintro ⟨b, hb⟩
      have hW := hrange i b
      refine ⟨?_, ?_⟩
      · rintro _ ⟨w, rfl⟩
        refine hW ⟨w, ?_⟩
        rw [← Over.w a]
        rfl
      · obtain ⟨W', ε, hc⟩ := hlift i W hW
        obtain ⟨b', hb'⟩ := hc b
        rw [← hP, hb, show b = ε.inv ≫ (Over.map i.1.1.1.ι).map b' by simp [hb'], op_comp,
          Functor.map_comp_apply, hξ, hP]
        exact Scheme.IdealSheafData.support_comap_baseChangeMap_subset f _
          (support_hilbertPresheafResLEι_app_subset f i.2 d _)
    · rintro ⟨hV, hU⟩
      have hW : Set.range W.hom ⊆ i.1.1.1 := by
        rintro _ ⟨w, rfl⟩
        rw [← Over.w a]
        exact hV ⟨w, rfl⟩
      obtain ⟨W', ε, hc⟩ := hlift i W hW
      let y := P.map ε.hom.op (P.map a.op x)
      have hy : (y.1.support : Set _) ⊆ pullback.fst f ((Over.map i.1.1.1.ι).obj W').hom ⁻¹'
          i.1.2.1 :=
        Scheme.IdealSheafData.support_comap_baseChangeMap_subset f _ hU
      obtain ⟨J, hJ⟩ := exists_hilbertPresheafResLEι_app_eq f i.2 d y hy
      refine ⟨ε.inv ≫ (Over.map i.1.1.1.ι).map ((e i).homEquiv.symm J), ?_⟩
      rw [op_comp, Functor.map_comp_apply, hξ, Equiv.apply_symm_apply, hJ, hPiso]
  have hopen (i : ι) (T : Over S) (x : P.obj (op T)) : ∃ O : T.left.Opens,
      ∀ (W : Over S) (a : W ⟶ T),
        (∃ b : W ⟶ X' i, P.map a.op x = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ O := by
    obtain ⟨O, -, hO⟩ := hopen' i T x
    exact ⟨O, hO⟩
  have hcov (T : Over S) (x : P.obj (op T)) (t : T.left) :
      ∃ (i : ι) (W : Over S) (a : W ⟶ T) (b : W ⟶ X' i),
        t ∈ Set.range a.left ∧ P.map a.op x = P.map b.op (ξ i) := by
    obtain ⟨-, -, -, hdeg⟩ := x.2
    have := x.2.1
    have := x.2.2.1
    have := x.2.2.2.1
    let p := x.1.subschemeι ≫ pullback.snd f T.hom
    let s := T.hom t
    obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
    let V : S.affineOpens := ⟨V, hV⟩
    let F : Set X := (fun y ↦ pullback.fst f T.hom (x.1.subschemeι y)) '' (p ⁻¹' {t})
    have hFfin : F.Finite := (p.finite_preimage_singleton t).image _
    have hFcard : F.ncard ≤ d :=
      (Set.ncard_image_le (p.finite_preimage_singleton t)).trans
        ((p.ncard_preimage_singleton_le_finrank t).trans (hdeg t).le)
    have hFs : F ⊆ f ⁻¹' {s} := by
      rintro _ ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
      have : f (pullback.fst f T.hom (x.1.subschemeι y)) = T.hom (p y) := by
        simp only [p, ← Scheme.Hom.comp_apply, Category.assoc, pullback.condition]
      rw [this, hy]
    have hinjι : Function.Injective (f.fiberι s) := fun a b hab ↦
      (f.fiberHomeo s).injective (Subtype.ext (by simpa using hab))
    have hGfin : (f.fiberι s ⁻¹' F).Finite := hFfin.preimage hinjι.injOn
    obtain ⟨U', hU'⟩ := hf s hGfin.toFinset (by
      rw [← Set.ncard_eq_toFinset_card _ hGfin]
      exact (Set.ncard_preimage_of_injective_subset_range hinjι
        (hFs.trans (f.range_fiberι s).symm.subset)).le.trans hFcard)
    have hFU' : F ⊆ U'.1 := by
      intro x' hx'
      obtain ⟨y, rfl⟩ := (f.range_fiberι s).symm.subset (hFs hx')
      exact hU' y (by simpa using hx')
    obtain ⟨r, hFr, hr⟩ := U'.2.exists_basicOpen_le_of_finite (O := U'.1 ⊓ f ⁻¹ᵁ V.1)
      inf_le_left hFfin (fun x' hx' ↦ ⟨hFU' hx', by
        change f x' ∈ (V.1 : Set S)
        rw [(hFs hx' : f x' = s)]
        exact hsV⟩)
    let i : ι := ⟨(V, ⟨X.basicOpen r, U'.2.basicOpen r⟩), hr.trans inf_le_right⟩
    obtain ⟨O, hOmem, hO⟩ := hopen' i T x
    have htO : t ∈ O := by
      refine (hOmem t).2 ⟨hsV, fun z hz hzt ↦ hFr ?_⟩
      have hz' : z ∈ Set.range x.1.subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]
        exact hz
      obtain ⟨y, rfl⟩ := hz'
      exact ⟨y, by simpa [p] using hzt, rfl⟩
    let a : Over.mk (O.ι ≫ T.hom) ⟶ T := Over.homMk O.ι rfl
    obtain ⟨b, hb⟩ := (hO _ a).2 (by simp [a])
    exact ⟨i, _, a, b, by simpa [a] using htO, hb⟩
  exact Scheme.LocalRepresentability.isRepresentable_of_isSheaf_over P
    (isSheaf_zariskiTopology_hilbertPresheaf f d) X' ξ hinj hopen hcov


variable (f : X ⟶ S)

/-- A scheme representing the Hilbert functor of a separated morphism is separated.
Its diagonal is the intersection of the two closed containment loci. -/
theorem isSeparated_of_representableBy_hilbertPresheaf {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] {d : ℕ} {H : Over S} (e : (hilbertPresheaf f d).RepresentableBy H) :
    IsSeparated H.hom := by
  let P : Over S := Over.mk (pullback.fst H.hom H.hom ≫ H.hom)
  let p₁ : P ⟶ H := Over.homMk (pullback.fst H.hom H.hom)
  let p₂ : P ⟶ H := Over.homMk (pullback.snd H.hom H.hom) pullback.condition.symm
  obtain ⟨K₁, hK₁⟩ := exists_idealSheafData_le_ker_iff_comap_le f (e.homEquiv p₁).2
    (e.homEquiv p₂).1
  obtain ⟨K₂, hK₂⟩ := exists_idealSheafData_le_ker_iff_comap_le f (e.homEquiv p₂).2
    (e.homEquiv p₁).1
  have key (T' : Over S) (φ : T' ⟶ P) : K₁ ⊔ K₂ ≤ φ.left.ker ↔ φ ≫ p₁ = φ ≫ p₂ := by
    rw [sup_le_iff, hK₁, hK₂, ← le_antisymm_iff, ← hilbertPresheaf_homEquiv_comp_val,
      ← hilbertPresheaf_homEquiv_comp_val]
    refine ⟨fun h ↦ e.homEquiv.injective (Subtype.ext h.symm), fun h ↦ by rw [h]⟩
  set K := K₁ ⊔ K₂
  let c : Over.mk (K.subschemeι ≫ P.hom) ⟶ P := Over.homMk K.subschemeι
  have hc : c ≫ p₁ = c ≫ p₂ := (key _ c).mp (by simp [c, K.ker_subschemeι])
  let δ : Over.mk H.hom ⟶ P := Over.homMk (pullback.diagonal H.hom) (by simp [P])
  have hδ : K ≤ δ.left.ker := (key _ δ).mpr (by
    ext1
    simp [δ, p₁, p₂])
  let h : H.left ⟶ K.subscheme := δ.left.toImage ≫ Scheme.IdealSheafData.inclusion hδ
  have hh : h ≫ K.subschemeι = pullback.diagonal H.hom := by simp [h, δ]
  let g : K.subscheme ⟶ H.left := K.subschemeι ≫ pullback.fst H.hom H.hom
  have : IsIso h := by
    refine ⟨g, ?_, ?_⟩
    · simp [g, reassoc_of% hh]
    · rw [← cancel_mono K.subschemeι, Category.assoc, hh, Category.id_comp]
      apply pullback.hom_ext
      · simp [g]
      · have := congrArg CommaMorphism.left hc
        simp only [Over.comp_left, Over.homMk_left, c, p₁, p₂] at this
        simp [g, this]
  refine ⟨?_⟩
  rw [← hh]
  infer_instance

end AlgebraicGeometry
