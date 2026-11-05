import Jacobian.AlgebraicGeometry.AffineCover.GenericPoints
import Jacobian.AlgebraicGeometry.IdealSheaf.Image.Opens
import Jacobian.AlgebraicGeometry.Scheme.Opens

/-!
# The dense affine-cover reduction in Chow's lemma

A quasi-compact quasi-separated scheme with finitely many irreducible components
has a surjective closed model with a finite affine cover whose intersection is
scheme-theoretically dense. The closed model is an isomorphism over a dense open
of the original scheme. This construction depends only on the source scheme,
not on a choice of structure morphism.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A closed model with a finite affine cover having scheme-theoretically dense intersection. -/
structure ChowReduction (sourceScheme : Scheme.{u}) where
  coverCard : ℕ
  model : Scheme.{u}
  closedImmersion : model ⟶ sourceScheme
  [isClosedImmersion_closedImmersion : IsClosedImmersion closedImmersion]
  [surjective_closedImmersion : Surjective closedImmersion]
  opens : Fin coverCard → model.Opens
  isAffineOpen_opens : ∀ index, IsAffineOpen (opens index)
  iSup_opens : ⨆ index, opens index = ⊤
  denseOpen : sourceScheme.Opens
  dense_denseOpen : Dense (denseOpen : Set sourceScheme)
  preimage_denseOpen : closedImmersion ⁻¹ᵁ denseOpen = ⨅ index, opens index
  [isIso_restriction : IsIso (closedImmersion ∣_ denseOpen)]
  [isSchemeTheoreticallyDominant_intersection :
    IsSchemeTheoreticallyDominant (⨅ index, opens index).ι]

attribute [instance] ChowReduction.isClosedImmersion_closedImmersion
  ChowReduction.surjective_closedImmersion ChowReduction.isIso_restriction
  ChowReduction.isSchemeTheoreticallyDominant_intersection

/-- The dense affine-cover reduction for schemes with finitely many irreducible components. -/
theorem nonempty_chowReduction {sourceScheme : Scheme.{u}} [CompactSpace sourceScheme]
    [QuasiSeparatedSpace sourceScheme]
    (finiteComponents : (irreducibleComponents sourceScheme).Finite) :
    Nonempty (ChowReduction sourceScheme) := by
  obtain ⟨coverCard, cover, affine_cover, generic_cover, sup_cover⟩ :=
    exists_isAffineOpen_cover_genericPoints_subset finiteComponents
  let denseOpen : sourceScheme.Opens := ⨅ index, cover index
  have dense_denseOpen : Dense (denseOpen : Set sourceScheme) :=
    dense_iInf_of_genericPoints_subset generic_cover
  have compact_denseOpen : IsCompact (denseOpen : Set sourceScheme) := by
    have compact_intersection := QuasiSeparatedSpace.isCompact_sInter (α := sourceScheme)
      (s := Set.range fun index ↦ (cover index : Set sourceScheme)) (Set.finite_range _)
      (by rintro _ ⟨index, rfl⟩; exact Or.inl (cover index).isOpen)
      (by rintro _ ⟨index, rfl⟩; exact (affine_cover index).isCompact)
    rwa [Set.sInter_range, ← TopologicalSpace.Opens.coe_iInf] at compact_intersection
  have : CompactSpace denseOpen := isCompact_iff_compactSpace.mp compact_denseOpen
  have : QuasiCompact denseOpen.ι :=
    (quasiCompact_iff_compactSpace denseOpen.ι).mpr inferInstance
  have preimage_intersection :
      (⨅ index, denseOpen.ι.imageι ⁻¹ᵁ cover index) = denseOpen.ι.imageι ⁻¹ᵁ denseOpen := by
    rw [← denseOpen.ι.imageι.preimage_iInf]
  exact ⟨{
    coverCard := coverCard
    model := denseOpen.ι.image
    closedImmersion := denseOpen.ι.imageι
    surjective_closedImmersion := denseOpen.surjective_imageι_ι dense_denseOpen
    opens := fun index ↦ denseOpen.ι.imageι ⁻¹ᵁ cover index
    isAffineOpen_opens := fun index ↦ (affine_cover index).preimage denseOpen.ι.imageι
    iSup_opens := denseOpen.ι.imageι.iSup_preimage_eq_top sup_cover
    denseOpen := denseOpen
    dense_denseOpen := dense_denseOpen
    preimage_denseOpen := preimage_intersection.symm
    isSchemeTheoreticallyDominant_intersection := preimage_intersection ▸ inferInstance }⟩

/-- An empty finite cover can be replaced by the singleton cover of the empty model. -/
theorem ChowReduction.exists_coverCard_ne_zero {sourceScheme : Scheme.{u}}
    (reduction : ChowReduction sourceScheme) :
    ∃ normalized : ChowReduction sourceScheme, normalized.coverCard ≠ 0 := by
  rcases eq_or_ne reduction.coverCard 0 with card_eq_zero | card_ne_zero
  · have : IsEmpty (Fin reduction.coverCard) := by rw [card_eq_zero]; infer_instance
    have bot_eq_top : (⊥ : reduction.model.Opens) = ⊤ :=
      (iSup_of_empty reduction.opens).symm.trans reduction.iSup_opens
    have : IsEmpty reduction.model := Set.univ_eq_empty_iff.mp
      (congrArg (fun openSet : reduction.model.Opens ↦ (openSet : Set reduction.model))
        bot_eq_top.symm)
    have opens_eq : ∀ openSet otherOpen : reduction.model.Opens, openSet = otherOpen := by
      intro openSet otherOpen
      ext point
      exact isEmptyElim point
    refine ⟨{ reduction with
      coverCard := 1
      opens := fun _ ↦ ⊤
      isAffineOpen_opens := fun _ ↦ isAffineOpen_top reduction.model
      iSup_opens := opens_eq _ _
      preimage_denseOpen := opens_eq _ _
      isSchemeTheoreticallyDominant_intersection := ?_ }, one_ne_zero⟩
    rw [opens_eq (⨅ _ : Fin 1, (⊤ : reduction.model.Opens)) ⊤]
    infer_instance
  · exact ⟨reduction, card_ne_zero⟩

end AlgebraicGeometry
