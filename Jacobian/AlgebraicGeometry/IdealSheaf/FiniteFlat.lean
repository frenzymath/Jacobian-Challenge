import Jacobian.AlgebraicGeometry.IdealSheaf.Colon
import Jacobian.AlgebraicGeometry.IdealSheaf.FiniteRank
import Jacobian.AlgebraicGeometry.IdealSheaf.Image
import Jacobian.AlgebraicGeometry.IdealSheaf.Multiplication
import Jacobian.AlgebraicGeometry.IdealSheaf.RelativeCartierPullback
import Jacobian.AlgebraicGeometry.Morphisms.FiniteRank
import Jacobian.RingTheory.Flat.Exact
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finite flat sums and differences of Cartier divisors

Multiplication of Cartier ideals preserves finiteness and flatness of the closed
subschemes. Colon subtraction preserves flatness. On residue-field fibers, the
rank of a sum is the sum of the ranks.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {Y T : Scheme.{u}}

/-- On the preimage of an affine open `W ⊆ Y`, the ring map induced by `V(I) ⟶ Y ⟶ T` is the
composite of `Γ(T, U) ⟶ Γ(Y, W)` with the quotient map by `I(W)`, up to isomorphism; in
particular it is flat if and only if `Γ(Y, W) ⧸ I(W)` is flat over `Γ(T, U)`. -/
lemma flat_appLE_subschemeι_comp_iff (π : Y ⟶ T) (I : Y.IdealSheafData) (U : T.Opens)
    (W : Y.affineOpens) (hWU : W.1 ≤ π ⁻¹ᵁ U) :
    ((I.subschemeι ≫ π).appLE U (I.subschemeι ⁻¹ᵁ W.1)
        (by rw [Scheme.Hom.comp_preimage]; exact I.subschemeι.preimage_mono hWU)).hom.Flat ↔
      ((Ideal.Quotient.mk (I.ideal W)).comp (π.appLE U W hWU).hom).Flat := by
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ W.1 _ hWU le_rfl, Scheme.Hom.appLE_eq_app,
    subschemeι_app, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_assoc,
    RingHom.Flat.comp_iff_of_bijective_left]
  · rfl
  · exact ConcreteCategory.bijective_of_isIso _

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {Y T : Scheme.{u}}

lemma flat_quotient_iff {R B : Type*} [CommRing R] [CommRing B] (φ : R →+* B) (I : Ideal B) :
    ((Ideal.Quotient.mk I).comp φ).Flat ↔
      letI := φ.toAlgebra
      Module.Flat R (B ⧸ I) := by
  let := φ.toAlgebra
  rw [← RingHom.flat_algebraMap_iff, IsScalarTower.algebraMap_eq R B (B ⧸ I),
    Ideal.Quotient.algebraMap_eq]
  rfl

/-- **Sums of relative effective Cartier divisors are flat.** If `I` and `J` are invertible
ideal sheaves on `Y` whose closed subschemes are flat over `T`, then so is the closed subscheme of
`I * J`: locally it is `B ⧸ (v₁ v₂)`, an extension of `B ⧸ (v₁)` by `B ⧸ (v₂)`. -/
lemma flat_subschemeι_mul_comp (π : Y ⟶ T) {I J : Y.IdealSheafData} (hI : I.IsInvertible)
    (hJ : J.IsInvertible) [Flat (I.subschemeι ≫ π)] [Flat (J.subschemeι ≫ π)] :
    Flat ((I * J).subschemeι ≫ π) := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @Flat)
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).1]
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := π ((I * J).subschemeι x)) trivial
  obtain ⟨W, hxW, hWU, ⟨a, ha, haI⟩, ⟨b, hb, hbJ⟩⟩ :=
    exists_affineOpens_isRegularPrincipal hI hJ (x := (I * J).subschemeι x) (O := π ⁻¹ᵁ U) hxU
  refine ⟨⟨U, hU⟩, ⟨_, W.2.preimage (I * J).subschemeι⟩, hxW,
    by rw [Scheme.Hom.comp_preimage]; exact (I * J).subschemeι.preimage_mono hWU, ?_⟩
  rw [flat_appLE_subschemeι_comp_iff π _ U W hWU, flat_quotient_iff, ideal_mul, Pi.mul_apply,
    haI, hbJ, Ideal.span_singleton_mul_span_singleton]
  have h₁ := HasRingHomProperty.appLE (P := @Flat) (I.subschemeι ≫ π) inferInstance ⟨U, hU⟩
    ⟨_, W.2.preimage I.subschemeι⟩
    (by rw [Scheme.Hom.comp_preimage]; exact I.subschemeι.preimage_mono hWU)
  have h₂ := HasRingHomProperty.appLE (P := @Flat) (J.subschemeι ≫ π) inferInstance ⟨U, hU⟩
    ⟨_, W.2.preimage J.subschemeι⟩
    (by rw [Scheme.Hom.comp_preimage]; exact J.subschemeι.preimage_mono hWU)
  rw [flat_appLE_subschemeι_comp_iff π _ U W hWU, flat_quotient_iff, haI] at h₁
  rw [flat_appLE_subschemeι_comp_iff π _ U W hWU, flat_quotient_iff, hbJ] at h₂
  let := (π.appLE U W hWU).hom.toAlgebra
  exact Ideal.Quotient.flat_span_singleton_mul a b ha

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {Y T : Scheme.{u}}

/-- Every point of the closed subscheme of `I * J` lies in the closed subscheme of `I` or in
that of `J`. -/
lemma mem_range_inclusion_or_of_mul (I J : Y.IdealSheafData) (x : (I * J).subscheme) :
    x ∈ Set.range (inclusion (show I * J ≤ I from fun _ ↦ Ideal.mul_le_left)) ∨
      x ∈ Set.range (inclusion (show I * J ≤ J from fun _ ↦ Ideal.mul_le_right)) := by
  have hx : (I * J).subschemeι x ∈ ((I * J).support : Set Y) := by
    rw [← range_subschemeι]
    exact ⟨x, rfl⟩
  rw [support_mul] at hx
  rcases hx with hx | hx
  · left
    rw [← range_subschemeι] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, (I * J).subschemeι.isEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, inclusion_subschemeι, hy])⟩
  · right
    rw [← range_subschemeι] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, (I * J).subschemeι.isEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, inclusion_subschemeι, hy])⟩

/-- **Sums of finite closed subschemes are finite.** If the closed subschemes of `I` and `J`
are finite over `T`, then so is the closed subscheme of `I * J`, whose underlying set is the
union of theirs. It is proper, being separated and universally closed since it is covered by
the two finite closed subschemes, and it has finite fibres. -/
lemma isFinite_subschemeι_mul_comp (π : Y ⟶ T) [LocallyOfFiniteType π] {I J : Y.IdealSheafData}
    [IsFinite (I.subschemeι ≫ π)] [IsFinite (J.subschemeι ≫ π)] :
    IsFinite ((I * J).subschemeι ≫ π) := by
  set g := (I * J).subschemeι ≫ π
  set j₁ := inclusion (show I * J ≤ I from fun _ ↦ Ideal.mul_le_left)
  set j₂ := inclusion (show I * J ≤ J from fun _ ↦ Ideal.mul_le_right)
  have hj₁ : j₁ ≫ g = I.subschemeι ≫ π := by simp [j₁, g, inclusion_subschemeι_assoc]
  have hj₂ : j₂ ≫ g = J.subschemeι ≫ π := by simp [j₂, g, inclusion_subschemeι_assoc]
  have hcover := mem_range_inclusion_or_of_mul I J
  have : Surjective (coprod.desc j₁ j₂) := ⟨fun x ↦ by
    rcases hcover x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨(coprod.inl : _ ⟶ I.subscheme ⨿ J.subscheme) y, by
        rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
    · exact ⟨(coprod.inr : _ ⟶ I.subscheme ⨿ J.subscheme) y, by
        rw [← Scheme.Hom.comp_apply, coprod.inr_desc]⟩⟩
  have : UniversallyClosed (coprod.desc j₁ j₂ ≫ g) := by
    rw [coprod.desc_comp, hj₁, hj₂]
    infer_instance
  have : UniversallyClosed g := .of_comp_surjective (coprod.desc j₁ j₂) g
  have hclosed {Z : Scheme.{u}} (j : Z ⟶ (I * J).subscheme) [IsClosedImmersion j]
      [IsFinite (j ≫ g)] :
      IsClosed (Set.range (pullback.diagonal (j ≫ g) ≫
        pullback.map (j ≫ g) (j ≫ g) g g j j (𝟙 T) (by simp) (by simp))) := by
    have : IsClosedImmersion (pullback.map (j ≫ g) (j ≫ g) g g j j (𝟙 T) (by simp) (by simp)) :=
      MorphismProperty.pullbackMap (P := @IsClosedImmersion) ‹_› ‹_› rfl rfl
    exact (Scheme.Hom.isClosedEmbedding _).isClosed_range
  have : IsFinite (j₁ ≫ g) := by rw [hj₁]; infer_instance
  have : IsFinite (j₂ ≫ g) := by rw [hj₂]; infer_instance
  have : IsSeparated g := by
    refine ⟨IsClosedImmersion.of_isPreimmersion _ ?_⟩
    have hrange : Set.range (pullback.diagonal g) =
        Set.range (pullback.diagonal (j₁ ≫ g) ≫
          pullback.map (j₁ ≫ g) (j₁ ≫ g) g g j₁ j₁ (𝟙 T) (by simp) (by simp)) ∪
        Set.range (pullback.diagonal (j₂ ≫ g) ≫
          pullback.map (j₂ ≫ g) (j₂ ≫ g) g g j₂ j₂ (𝟙 T) (by simp) (by simp)) := by
      rw [← pullback.comp_diagonal, ← pullback.comp_diagonal]
      apply subset_antisymm
      · rintro _ ⟨x, rfl⟩
        rcases hcover x with ⟨y, rfl⟩ | ⟨y, rfl⟩
        · exact Or.inl ⟨y, rfl⟩
        · exact Or.inr ⟨y, rfl⟩
      · rintro _ (⟨y, rfl⟩ | ⟨y, rfl⟩)
        · exact ⟨j₁ y, rfl⟩
        · exact ⟨j₂ y, rfl⟩
    rw [hrange]
    exact (hclosed j₁).union (hclosed j₂)
  have : LocallyQuasiFinite g := by
    refine .of_finite_preimage_singleton _ fun t ↦ ?_
    refine (((I.subschemeι ≫ π).finite_preimage_singleton t).image j₁).union
      (((J.subschemeι ≫ π).finite_preimage_singleton t).image j₂) |>.subset ?_
    intro x hx
    rcases hcover x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · refine Or.inl ⟨y, ?_, rfl⟩
      rw [Set.mem_preimage, ← hj₁]
      exact hx
    · refine Or.inr ⟨y, ?_, rfl⟩
      rw [Set.mem_preimage, ← hj₂]
      exact hx
  have : IsProper g := ⟨⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry
section Rank


/-- The rank of a finite flat closed family is the dimension of its residue-field fiber. -/
lemma Scheme.IdealSheafData.finrank_subschemeι_comp_eq_finrankΓ {Y T : Scheme.{u}} (π : Y ⟶ T)
    (I : Y.IdealSheafData) [IsFinite (I.subschemeι ≫ π)] [Flat (I.subschemeι ≫ π)] (t : T) :
    (I.subschemeι ≫ π).finrank t =
      ((I.comap (π.fiberι t)).subschemeι ≫ π.fiberToSpecResidueField t).finrankΓ := by
  let g : (I.comap (π.fiberι t)).subscheme ⟶ Spec (T.residueField t) :=
    (I.comap (π.fiberι t)).subschemeι ≫ π.fiberToSpecResidueField t
  let q : (I.comap (π.fiberι t)).subscheme ⟶ I.subscheme :=
    (I.comapIso (π.fiberι t)).hom ≫ pullback.snd (π.fiberι t) I.subschemeι
  have hsq : IsPullback q g (I.subschemeι ≫ π) (T.fromSpecResidueField t) :=
    (I.isPullback_comap (π.fiberι t)).flip.paste_vert (.of_hasPullback π _)
  have : IsFinite g := MorphismProperty.of_isPullback (P := @IsFinite) hsq ‹_›
  have : Flat g := MorphismProperty.of_isPullback (P := @Flat) hsq ‹_›
  have key : g.finrank (IsLocalRing.closedPoint (T.residueField t)) =
      (I.subschemeι ≫ π).finrank t := by
    simpa only [T.fromSpecResidueField_apply] using
      (Scheme.Hom.finrank_of_isPullback q g (I.subschemeι ≫ π)
        (T.fromSpecResidueField t) hsq (IsLocalRing.closedPoint (T.residueField t)))
  exact key.symm.trans (Scheme.Hom.finrank_eq_finrankΓ_of_field g
    (IsLocalRing.closedPoint (T.residueField t)))

end Rank
end AlgebraicGeometry
namespace AlgebraicGeometry

section Rank

/-- The base change to a fibre of the closed subscheme of `I` is finite if `V(I)` is finite. -/
lemma Scheme.IdealSheafData.isFinite_comap_fiberι {Y T : Scheme.{u}} (π : Y ⟶ T)
    (I : Y.IdealSheafData) [IsFinite (I.subschemeι ≫ π)] (t : T) :
    IsFinite ((I.comap (π.fiberι t)).subschemeι ≫ π.fiberToSpecResidueField t) :=
  MorphismProperty.of_isPullback (P := @IsFinite)
    ((I.isPullback_comap (π.fiberι t)).flip.paste_vert (.of_hasPullback π _)) ‹_›

/-- **The degree is additive on sums of relative effective Cartier divisors.** Let
`π : Y ⟶ T` be flat and locally of finite presentation and let `I, J` be invertible ideal sheaves
on `Y` such that `V(I)`, `V(J)` and `V(I * J)` are finite and flat over `T`. Then the rank of
`V(I * J)` over `T` is the sum of the ranks of `V(I)` and `V(J)`: on the fibre over `t` this is
`Scheme.IdealSheafData.finrankΓ_subschemeι_mul_comp`. -/
lemma Scheme.IdealSheafData.finrank_subschemeι_mul_comp {Y T : Scheme.{u}} (π : Y ⟶ T) [Flat π]
    [LocallyOfFinitePresentation π] {I J : Y.IdealSheafData} (hI : I.IsInvertible)
    (hJ : J.IsInvertible) [IsFinite (I.subschemeι ≫ π)] [Flat (I.subschemeι ≫ π)]
    [IsFinite (J.subschemeι ≫ π)] [Flat (J.subschemeι ≫ π)]
    [IsFinite ((I * J).subschemeι ≫ π)] [Flat ((I * J).subschemeι ≫ π)] (t : T) :
    ((I * J).subschemeι ≫ π).finrank t =
      (I.subschemeι ≫ π).finrank t + (J.subschemeι ≫ π).finrank t := by
  have hI' : (I.comap (π.fiberι t)).IsInvertible :=
    (IsRelativeEffectiveCartier.isRelativeEffectiveCartier_comap_of_isPullback ⟨hI, ‹_›⟩
      (IsPullback.of_hasPullback π (T.fromSpecResidueField t))).1
  have hJ' : (J.comap (π.fiberι t)).IsInvertible :=
    (IsRelativeEffectiveCartier.isRelativeEffectiveCartier_comap_of_isPullback ⟨hJ, ‹_›⟩
      (IsPullback.of_hasPullback π (T.fromSpecResidueField t))).1
  have := I.isFinite_comap_fiberι π t
  have := J.isFinite_comap_fiberι π t
  have := (I * J).isFinite_comap_fiberι π t
  rw [Scheme.IdealSheafData.comap_mul] at this
  rw [finrank_subschemeι_comp_eq_finrankΓ, finrank_subschemeι_comp_eq_finrankΓ,
    finrank_subschemeι_comp_eq_finrankΓ, Scheme.IdealSheafData.comap_mul]
  exact finrankΓ_subschemeι_mul_comp (K := T.residueField t) (π.fiberToSpecResidueField t) hI' hJ'

end Rank

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {Y T : Scheme.{u}}

/-- **Differences of relative effective Cartier divisors are flat.** If `D ≤ E` are invertible
ideal sheaves on `Y` whose closed subschemes are flat over `T`, then so is the closed subscheme
of `(D : E)`: locally it is `B ⧸ (g)` where `D = (v g)` and `E = (v)`, the kernel of the
surjection `B ⧸ (v g) ⟶ B ⧸ (v)` of flat modules. -/
lemma flat_subschemeι_colon_comp (π : Y ⟶ T) {D E : Y.IdealSheafData} (hD : D.IsInvertible)
    (hE : E.IsInvertible) (hle : D ≤ E) [Flat (D.subschemeι ≫ π)] [Flat (E.subschemeι ≫ π)] :
    Flat ((D.colon E hE.fg_ideal).subschemeι ≫ π) := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @Flat)
    (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Flat.holdsForLocalizationAway).1]
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := π ((D.colon E hE.fg_ideal).subschemeι x)) trivial
  obtain ⟨W, hxW, hWU, v, g, hv, -, hvE, hgD⟩ := exists_affineOpens_eq_span_mul hD hE hle
    (x := (D.colon E hE.fg_ideal).subschemeι x) (O := π ⁻¹ᵁ U) hxU
  refine ⟨⟨U, hU⟩, ⟨_, W.2.preimage (D.colon E hE.fg_ideal).subschemeι⟩, hxW,
    by rw [Scheme.Hom.comp_preimage]; exact (D.colon E _).subschemeι.preimage_mono hWU, ?_⟩
  rw [flat_appLE_subschemeι_comp_iff π _ U W hWU, flat_quotient_iff,
    ideal_colon_of_eq_span hE.fg_ideal hv hvE hgD]
  have h₁ := HasRingHomProperty.appLE (P := @Flat) (D.subschemeι ≫ π) inferInstance ⟨U, hU⟩
    ⟨_, W.2.preimage D.subschemeι⟩
    (by rw [Scheme.Hom.comp_preimage]; exact D.subschemeι.preimage_mono hWU)
  have h₂ := HasRingHomProperty.appLE (P := @Flat) (E.subschemeι ≫ π) inferInstance ⟨U, hU⟩
    ⟨_, W.2.preimage E.subschemeι⟩
    (by rw [Scheme.Hom.comp_preimage]; exact E.subschemeι.preimage_mono hWU)
  rw [flat_appLE_subschemeι_comp_iff π _ U W hWU, flat_quotient_iff, hgD] at h₁
  rw [flat_appLE_subschemeι_comp_iff π _ U W hWU, flat_quotient_iff, hvE] at h₂
  let := (π.appLE U W hWU).hom.toAlgebra
  exact Module.Flat.of_exact_of_flat_of_flat_right _ _
    (Ideal.Quotient.injective_mulSpanSingleton v g hv)
    (Ideal.Quotient.surjective_factorSpanSingleton v g)
    (Ideal.Quotient.exact_mulSpanSingleton_factorSpanSingleton v g)

end AlgebraicGeometry.Scheme.IdealSheafData
