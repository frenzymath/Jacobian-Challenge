import Jacobian.AlgebraicGeometry.Hilbert.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Open subschemes and the Hilbert functor

Finite families supported in an open subscheme form an open subfunctor.
For a separated ambient morphism, these families are precisely the finite
flat families of the open subscheme itself.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

lemma Scheme.IdealSheafData.support_comap_baseChangeMap_subset (f : X ⟶ S) {T W : Over S}
    (a : W ⟶ T) {I : (pullback f T.hom).IdealSheafData} {U : Set X}
    (hI : (I.support : Set _) ⊆ pullback.fst f T.hom ⁻¹' U) :
    ((I.comap (baseChangeMap f a)).support : Set _) ⊆ pullback.fst f W.hom ⁻¹' U := by
  intro z hz
  rw [coe_support_comap] at hz
  have := hI hz
  simp only [Set.mem_preimage, ← Scheme.Hom.comp_apply, baseChangeMap,
    pullback.lift_fst] at this ⊢
  simpa using this

namespace Scheme.IdealSheafData

/-- For a universally closed family, containment in an open subscheme is an
open condition on the parameter scheme, compatible with arbitrary base change. -/
theorem exists_opens_support_comap_subset (f : X ⟶ S) {T : Over S}
    (I : (pullback f T.hom).IdealSheafData)
    [UniversallyClosed (I.subschemeι ≫ pullback.snd f T.hom)] (U : X.Opens) :
    ∃ O : T.left.Opens,
      (∀ t, t ∈ O ↔ ∀ z ∈ I.support, pullback.snd f T.hom z = t → pullback.fst f T.hom z ∈ U) ∧
      ∀ (W : Over S) (a : W ⟶ T),
        ((I.comap (baseChangeMap f a)).support : Set _) ⊆ pullback.fst f W.hom ⁻¹' U ↔
          Set.range a.left ⊆ O := by
  let q := I.subschemeι ≫ pullback.snd f T.hom
  let B : Set T.left := q '' ((I.subschemeι ≫ pullback.fst f T.hom) ⁻¹' (U : Set X)ᶜ)
  have hB : IsClosed B :=
    q.isClosedMap _ (U.isOpen.isClosed_compl.preimage (Scheme.Hom.continuous _))
  have hsupp {z} : z ∈ I.support ↔ z ∈ Set.range I.subschemeι := by
    rw [range_subschemeι]
    rfl
  refine ⟨⟨Bᶜ, hB.isOpen_compl⟩, fun t ↦ ?_, fun W a ↦ ?_⟩
  · change t ∉ B ↔ _
    constructor
    · intro ht z hz hzt
      by_contra hzU
      obtain ⟨y, rfl⟩ := hsupp.1 hz
      exact ht ⟨y, hzU, hzt⟩
    · rintro H ⟨y, hyU, rfl⟩
      exact hyU (H _ (hsupp.2 ⟨y, rfl⟩) rfl)
  · rw [coe_support_comap]
    change _ ↔ Set.range a.left ⊆ Bᶜ
    have hfst (z) : pullback.fst f T.hom (baseChangeMap f a z) = pullback.fst f W.hom z := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    have hsnd (z) : pullback.snd f T.hom (baseChangeMap f a z) =
        a.left (pullback.snd f W.hom z) := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply]
    constructor
    · rintro H _ ⟨w, rfl⟩ ⟨y, hyU, hyt⟩
      obtain ⟨z, hz₁, hz₂⟩ := exists_preimage_of_isPullback (isPullback_baseChangeMap f a)
        (I.subschemeι y) w hyt
      have := H (show baseChangeMap f a z ∈ I.support from hz₁ ▸ hsupp.2 ⟨y, rfl⟩)
      rw [Set.mem_preimage, ← hfst, hz₁] at this
      exact hyU this
    · intro H z hz
      by_contra hzU
      obtain ⟨y, hy⟩ := hsupp.1 hz
      refine H ⟨pullback.snd f W.hom z, rfl⟩ ⟨y, ?_, ?_⟩
      · simpa [Scheme.Hom.comp_apply, hy, hfst] using hzU
      · simp [q, hy, hsnd]

end Scheme.IdealSheafData

section ResLE

variable (f : X ⟶ S) {V : S.Opens} {U : X.Opens} (h : U ≤ f ⁻¹ᵁ V)

noncomputable abbrev pullbackResLEMap (W : Over V.toScheme) :
    pullback (f.resLE V U h) W.hom ⟶ pullback f ((Over.map V.ι).obj W).hom :=
  pullback.map _ _ _ _ U.ι (𝟙 _) V.ι (by simp [Scheme.Hom.resLE_comp_ι]) (by simp)

@[reassoc (attr := simp)]
lemma pullbackResLEMap_snd (W : Over V.toScheme) :
    pullbackResLEMap f h W ≫ pullback.snd f ((Over.map V.ι).obj W).hom =
      pullback.snd (f.resLE V U h) W.hom :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma isPullback_pullbackResLEMap (W : Over V.toScheme) :
    IsPullback (pullback.fst _ _) (pullbackResLEMap f h W) U.ι
      (pullback.fst f ((Over.map V.ι).obj W).hom) := by
  have h₁ : IsPullback (pullback.snd _ _ ≫ 𝟙 _) (pullback.fst (f.resLE V U h) W.hom)
      (W.hom ≫ V.ι) (f.resLE V U h ≫ V.ι) :=
    (IsPullback.of_hasPullback _ _).flip.paste_horiz (IsPullback.of_horiz_isIso_mono ⟨by simp⟩)
  rw [Category.comp_id, Scheme.Hom.resLE_comp_ι,
    ← pullbackResLEMap_snd f h W] at h₁
  exact (IsPullback.of_right h₁ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback _ _).flip).flip

instance (W : Over V.toScheme) : IsOpenImmersion (pullbackResLEMap f h W) :=
  MorphismProperty.of_isPullback (isPullback_pullbackResLEMap f h W) inferInstance

lemma range_pullbackResLEMap (W : Over V.toScheme) :
    Set.range (pullbackResLEMap f h W) = pullback.fst f ((Over.map V.ι).obj W).hom ⁻¹' U := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← (isPullback_pullbackResLEMap f h W).w,
      Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι U]
    exact ⟨_, rfl⟩
  · intro hz
    rw [Set.mem_preimage, ← Scheme.Opens.range_ι U] at hz
    obtain ⟨u, hu⟩ := hz
    obtain ⟨y, -, hy⟩ :=
      Scheme.exists_preimage_of_isPullback (isPullback_pullbackResLEMap f h W) u z hu
    exact ⟨y, hy⟩

lemma isClosedImmersion_subschemeι_comp_pullbackResLEMap [IsSeparated f] {W : Over V.toScheme}
    (J : (pullback (f.resLE V U h) W.hom).IdealSheafData)
    [UniversallyClosed (J.subschemeι ≫ pullback.snd _ W.hom)] :
    IsClosedImmersion (J.subschemeι ≫ pullbackResLEMap f h W) := by
  have : UniversallyClosed ((J.subschemeι ≫ pullbackResLEMap f h W) ≫
      pullback.snd f ((Over.map V.ι).obj W).hom) := by
    rw [Category.assoc, pullbackResLEMap_snd]
    infer_instance
  have := UniversallyClosed.of_comp_of_isSeparated (J.subschemeι ≫ pullbackResLEMap f h W)
    (pullback.snd f ((Over.map V.ι).obj W).hom)
  exact .of_isPreimmersion _ (Scheme.Hom.isClosedMap _).isClosed_range

lemma IsHilbertSubscheme.map_pullbackResLEMap [IsSeparated f] {d : ℕ} {W : Over V.toScheme}
    {J : (pullback (f.resLE V U h) W.hom).IdealSheafData}
    (hJ : IsHilbertSubscheme (f.resLE V U h) d W J) :
    IsHilbertSubscheme f d ((Over.map V.ι).obj W) (J.map (pullbackResLEMap f h W)) := by
  have := hJ.1
  have := isClosedImmersion_subschemeι_comp_pullbackResLEMap f h J
  have key : (J.subschemeι ≫ pullbackResLEMap f h W).toImage ≫
      (J.map (pullbackResLEMap f h W)).subschemeι ≫ pullback.snd f _ =
      J.subschemeι ≫ pullback.snd _ W.hom := by
    rw [← Category.assoc]
    erw [Scheme.Hom.toImage_imageι]
    rw [Category.assoc]
    exact congrArg (J.subschemeι ≫ ·) (pullbackResLEMap_snd f h W)
  unfold IsHilbertSubscheme at hJ ⊢
  rw [← key] at hJ
  exact (isFinite_flat_finrank_iso_comp_iff _ _ d).1 hJ

lemma IsHilbertSubscheme.comap_pullbackResLEMap {d : ℕ} {W : Over V.toScheme}
    {I : (pullback f ((Over.map V.ι).obj W).hom).IdealSheafData}
    (hI : IsHilbertSubscheme f d ((Over.map V.ι).obj W) I)
    (hIU : (I.support : Set _) ⊆ pullback.fst f ((Over.map V.ι).obj W).hom ⁻¹' U) :
    IsHilbertSubscheme (f.resLE V U h) d W (I.comap (pullbackResLEMap f h W)) := by
  have hI' : Set.range I.subschemeι ⊆ Set.range (pullbackResLEMap f h W) := by
    rwa [Scheme.IdealSheafData.range_subschemeι, range_pullbackResLEMap]
  have hpb : IsPullback (IsOpenImmersion.lift _ I.subschemeι hI') (𝟙 _)
      (pullbackResLEMap f h W) I.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have : IsIso (pullback.snd (pullbackResLEMap f h W) I.subschemeι) := by
    rw [← hpb.isoPullback_inv_snd, Category.comp_id]
    infer_instance
  have key : ((I.comapIso _).hom ≫ pullback.snd (pullbackResLEMap f h W) I.subschemeι) ≫
      I.subschemeι ≫ pullback.snd f _ =
      (I.comap (pullbackResLEMap f h W)).subschemeι ≫ pullback.snd _ W.hom := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Category.assoc,
      ← pullback.condition_assoc, pullbackResLEMap_snd]
  unfold IsHilbertSubscheme at hI ⊢
  rw [← key]
  exact (isFinite_flat_finrank_iso_comp_iff _ _ d).2 hI

/-- A finite flat family in an open subscheme pushes forward to the ambient
separated scheme, giving an injective map of Hilbert functors over the open base. -/
noncomputable def hilbertPresheafResLEι [IsSeparated f] (d : ℕ) :
    hilbertPresheaf (f.resLE V U h) d ⟶ (Over.map V.ι).op ⋙ hilbertPresheaf f d where
  app W := TypeCat.ofHom fun J ↦
    ⟨J.1.map (pullbackResLEMap f h W.unop), J.2.map_pullbackResLEMap f h⟩
  naturality W W' b := by
    ext J : 3
    apply Subtype.ext
    change (J.1.comap (baseChangeMap _ b.unop)).map (pullbackResLEMap f h W'.unop) =
      (J.1.map (pullbackResLEMap f h W.unop)).comap
        (baseChangeMap f ((Over.map V.ι).map b.unop))
    obtain ⟨J, hJ⟩ := J
    have := hJ.1
    have := isClosedImmersion_subschemeι_comp_pullbackResLEMap f h J
    have hsq : pullbackResLEMap f h W'.unop ≫ baseChangeMap f ((Over.map V.ι).map b.unop) =
        baseChangeMap (f.resLE V U h) b.unop ≫ pullbackResLEMap f h W.unop := by
      apply pullback.hom_ext <;> simp [pullbackResLEMap, baseChangeMap]
    rw [← Scheme.IdealSheafData.map_comap_of_subset_range (pullbackResLEMap f h W'.unop)
      ((J.map (pullbackResLEMap f h W.unop)).comap _)]
    · rw [← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp,
        Scheme.IdealSheafData.comap_map_of_isClosedImmersion]
    · rw [range_pullbackResLEMap]
      refine Scheme.IdealSheafData.support_comap_baseChangeMap_subset f _ ?_
      rw [← range_pullbackResLEMap f h]
      exact Scheme.IdealSheafData.support_map_subset_range _ _

lemma hilbertPresheafResLEι_app_coe [IsSeparated f] (d : ℕ) {W : Over V.toScheme}
    (J : (hilbertPresheaf (f.resLE V U h) d).obj (op W)) :
    ((hilbertPresheafResLEι f h d).app (op W) J).1 = J.1.map (pullbackResLEMap f h W) :=
  rfl

lemma hilbertPresheafResLEι_app_injective [IsSeparated f] (d : ℕ) (W : Over V.toScheme) :
    Function.Injective ((hilbertPresheafResLEι f h d).app (op W)) := by
  intro J₁ J₂ hJ
  have := J₁.2.1
  have := J₂.2.1
  have := isClosedImmersion_subschemeι_comp_pullbackResLEMap f h J₁.1
  have := isClosedImmersion_subschemeι_comp_pullbackResLEMap f h J₂.1
  apply Subtype.ext
  rw [← Scheme.IdealSheafData.comap_map_of_isClosedImmersion (pullbackResLEMap f h W) J₁.1,
    ← Scheme.IdealSheafData.comap_map_of_isClosedImmersion (pullbackResLEMap f h W) J₂.1]
  exact congrArg (fun I ↦ Scheme.IdealSheafData.comap I _) (congrArg Subtype.val hJ)

lemma support_hilbertPresheafResLEι_app_subset [IsSeparated f] (d : ℕ) {W : Over V.toScheme}
    (J : (hilbertPresheaf (f.resLE V U h) d).obj (op W)) :
    ((J.1.map (pullbackResLEMap f h W)).support : Set _) ⊆
      pullback.fst f ((Over.map V.ι).obj W).hom ⁻¹' U := by
  have := J.2.1
  have := isClosedImmersion_subschemeι_comp_pullbackResLEMap f h J.1
  rw [← range_pullbackResLEMap f h W]
  exact Scheme.IdealSheafData.support_map_subset_range _ _

lemma exists_hilbertPresheafResLEι_app_eq [IsSeparated f] (d : ℕ) {W : Over V.toScheme}
    (I : (hilbertPresheaf f d).obj (op ((Over.map V.ι).obj W)))
    (hIU : (I.1.support : Set _) ⊆ pullback.fst f ((Over.map V.ι).obj W).hom ⁻¹' U) :
    ∃ J, (hilbertPresheafResLEι f h d).app (op W) J = I := by
  refine ⟨⟨I.1.comap (pullbackResLEMap f h W), I.2.comap_pullbackResLEMap f h hIU⟩,
    Subtype.ext ?_⟩
  rw [hilbertPresheafResLEι_app_coe]
  exact Scheme.IdealSheafData.map_comap_of_subset_range _ _
    (hIU.trans (range_pullbackResLEMap f h W).symm.subset)

end ResLE

end AlgebraicGeometry
