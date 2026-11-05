import Jacobian.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Scheme-theoretic images and flat base change

The map to the scheme-theoretic image has zero kernel. For a quasi-compact
morphism, flat base change pulls back its kernel ideal sheaf.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {T Y : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g]

  {Y' : Scheme.{u}} (q : Y' ⟶ Y) [Flat q]



/-- The kernel of a quasi-compact morphism commutes with flat base change. -/
theorem Scheme.Hom.ker_pullback_snd : (pullback.snd g q).ker = g.ker.comap q := by
  have w : pullback.snd g q ≫ q = (pullback.fst g q ≫ g.toImage) ≫ g.imageι := by
    rw [Category.assoc, g.toImage_imageι, pullback.condition]
  set c := pullback.lift (pullback.snd g q) (pullback.fst g q ≫ g.toImage) w with hc
  have hfst : c ≫ pullback.fst q g.imageι = pullback.snd g q := pullback.lift_fst _ _ _
  have hsq : IsPullback c (pullback.fst g q) (pullback.snd q g.imageι) g.toImage := by
    refine .of_right ?_ (pullback.lift_snd _ _ _) (.of_hasPullback q g.imageι)
    rw [hc, pullback.lift_fst, g.toImage_imageι]
    exact (IsPullback.of_hasPullback g q).flip
  have : IsSchemeTheoreticallyDominant c := .of_isPullback hsq.flip
  rw [← hfst, Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot c, Scheme.IdealSheafData.map_bot,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The closed subscheme of a pulled-back ideal is the base change of the original subscheme. -/
lemma isPullback_comap {source target : Scheme.{u}} (ideal : target.IdealSheafData)
    (morphism : source ⟶ target) :
    IsPullback (ideal.comap morphism).subschemeι
      ((ideal.comapIso morphism).hom ≫ pullback.snd morphism ideal.subschemeι)
      morphism ideal.subschemeι :=
  IsPullback.of_iso_pullback ⟨by simp⟩ (ideal.comapIso morphism) (by simp) rfl

/-- Direct image along a closed immersion commutes with arbitrary base change. -/
theorem map_comap_of_isPullback_of_isClosedImmersion {X' Y' X Y : Scheme.{u}}
    (B : Y.IdealSheafData) {g : Y ⟶ X} [IsClosedImmersion g] {q : X' ⟶ X} {g' : Y' ⟶ X'}
    {p : Y' ⟶ Y} (h : IsPullback p g' g q) : (B.map g).comap q = (B.comap p).map g' := by
  have H := ((IsPullback.of_hasPullback p B.subschemeι).paste_horiz h.flip)
  rw [map, map, ← ker_fst_of_isClosedImmersion, ← comapIso_hom_fst, Category.assoc,
    Scheme.Hom.ker_comp_of_isIso, ← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

/-- An ideal containing the kernel of a closed immersion is recovered from its pullback. -/
lemma map_comap_of_ker_le {U Y : Scheme.{u}} (j : U ⟶ Y) [IsClosedImmersion j]
    (I : Y.IdealSheafData) (hI : j.ker ≤ I) : (I.comap j).map j = I := by
  have hI' : j.ker ≤ I.subschemeι.ker := by rwa [ker_subschemeι]
  have hpb : IsPullback (IsClosedImmersion.lift j I.subschemeι hI') (𝟙 _) j I.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have : IsIso (pullback.snd j I.subschemeι) := by
    rw [← hpb.isoPullback_inv_snd, Category.comp_id]
    infer_instance
  rw [map, ← comapIso_hom_fst, Category.assoc, Scheme.Hom.ker_comp_of_isIso, pullback.condition,
    Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]

variable {X Y : Scheme.{u}}

/-- The underlying set of the support of the pullback of an ideal sheaf is the preimage
of the underlying set of its support: the set-level form of
`AlgebraicGeometry.Scheme.IdealSheafData.support_comap`. -/
lemma coe_support_comap (I : Y.IdealSheafData) (f : X ⟶ Y) :
    ((I.comap f).support : Set X) = f ⁻¹' (I.support : Set Y) := by
  rw [support_comap, TopologicalSpace.Closeds.coe_preimage]


variable {U : Scheme.{u}} (j : U ⟶ Y)

/-- If the closed subscheme of `J` stays closed in `Y` under a monomorphism `j : U ⟶ Y`, then
pulling back the pushforward of `J` along `j` recovers `J`. -/
lemma comap_map_of_isClosedImmersion [Mono j] (J : U.IdealSheafData)
    [IsClosedImmersion (J.subschemeι ≫ j)] : (J.map j).comap j = J := by
  have h : IsPullback (𝟙 _) J.subschemeι (J.subschemeι ≫ j) j :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  rw [map, ← ker_fst_of_isClosedImmersion, ← h.flip.isoPullback_inv_fst,
    Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]

/-- The support of the pushforward of `J` along `j` lies in the range of `j`, provided the
closed subscheme of `J` stays closed in `Y`. -/
lemma support_map_subset_range (J : U.IdealSheafData) [IsClosedImmersion (J.subschemeι ≫ j)] :
    ((J.map j).support : Set Y) ⊆ Set.range j := by
  rw [map, Scheme.Hom.support_ker,
    (J.subschemeι ≫ j).isClosedEmbedding.isClosed_range.closure_eq, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp]
  exact Set.image_subset_range _ _

/-- An ideal sheaf whose support lies in the range of an open immersion `j` is the pushforward
of its pullback along `j`. -/
lemma map_comap_of_subset_range [IsOpenImmersion j] (I : Y.IdealSheafData)
    (hI : (I.support : Set Y) ⊆ Set.range j) : (I.comap j).map j = I := by
  have hI' : Set.range I.subschemeι ⊆ Set.range j := by rwa [range_subschemeι]
  have h : IsPullback (IsOpenImmersion.lift j I.subschemeι hI') (𝟙 _) j I.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  rw [comap, ← h.isoPullback_inv_fst, Scheme.Hom.ker_comp_of_isIso, map_ker,
    IsOpenImmersion.lift_fac, ker_subschemeι]

end AlgebraicGeometry.Scheme.IdealSheafData
