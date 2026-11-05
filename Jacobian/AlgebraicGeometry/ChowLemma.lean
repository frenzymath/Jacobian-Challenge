import Jacobian.AlgebraicGeometry.ChowLemma.Reduction
import Jacobian.AlgebraicGeometry.ChowLemma.Modification
import Jacobian.AlgebraicGeometry.ChowLemma.ProjectiveEmbedding

/-!
# Chow's lemma

A separated finite-type scheme with finitely many irreducible components over
a quasi-compact quasi-separated base admits a proper surjective modification
which is an isomorphism over a dense open and immerses into projective space
above the base.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Chow's lemma over a quasi-compact quasi-separated base. -/
theorem exists_chowModification_of_finite_irreducibleComponents {sourceScheme baseScheme : Scheme.{u}} (baseMap : sourceScheme ⟶ baseScheme)
    [CompactSpace baseScheme] [QuasiSeparatedSpace baseScheme] [IsSeparated baseMap] [LocallyOfFiniteType baseMap]
    [QuasiCompact baseMap] (hX : (irreducibleComponents sourceScheme).Finite) :
    ∃ (modificationScheme : Scheme.{u}) (modification : modificationScheme ⟶ sourceScheme) (coordinates : Type u) (_ : Finite coordinates) (immersion : modificationScheme ⟶ ℙ(coordinates; baseScheme)),
      IsProper modification ∧ Surjective modification ∧ IsImmersion immersion ∧ immersion ≫ ℙ(coordinates; baseScheme) ↘ baseScheme = modification ≫ baseMap ∧
      ∃ denseOpen : sourceScheme.Opens, Dense (denseOpen : Set sourceScheme) ∧ IsIso (modification ∣_ denseOpen) := by
  have : CompactSpace sourceScheme := QuasiCompact.compactSpace_of_compactSpace baseMap
  have : QuasiSeparatedSpace sourceScheme := quasiSeparatedSpace_of_quasiSeparated baseMap
  obtain ⟨reduction, hn⟩ := (nonempty_chowReduction hX).some
    |>.exists_coverCard_ne_zero
  have : Nonempty (Fin reduction.coverCard) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have : CompactSpace reduction.model := QuasiCompact.compactSpace_of_compactSpace (reduction.closedImmersion ≫ baseMap)
  have : QuasiSeparatedSpace reduction.model := quasiSeparatedSpace_of_quasiSeparated (reduction.closedImmersion ≫ baseMap)
  have closedModels : ∀ index, ProperClosedModel ((reduction.opens index).ι ≫ reduction.closedImmersion ≫ baseMap) := fun index ↦
    have : IsAffine (reduction.opens index) := reduction.isAffineOpen_opens index
    (nonempty_properClosedModel _).some
  have hc : IsCompact ((⨅ index, reduction.opens index : reduction.model.Opens) : Set reduction.model) := by
    have witness := QuasiSeparatedSpace.isCompact_sInter (α := reduction.model)
      (s := Set.range fun index ↦ (reduction.opens index : Set reduction.model)) (Set.finite_range _)
      (by rintro _ ⟨index, rfl⟩; exact Or.inl (reduction.opens index).isOpen)
      (by rintro _ ⟨index, rfl⟩; exact (reduction.isAffineOpen_opens index).isCompact)
    rwa [Set.sInter_range, ← TopologicalSpace.Opens.coe_iInf] at witness
  have : CompactSpace (⨅ index, reduction.opens index : reduction.model.Opens) := isCompact_iff_compactSpace.mp hc
  have : QuasiCompact (⨅ index, reduction.opens index).ι := (quasiCompact_iff_compactSpace _).mpr inferInstance
  have : QuasiCompact (ChowGraph.tuple closedModels) := by
    have : CompactSpace (ChowGraph.ambient closedModels).left :=
      QuasiCompact.compactSpace_of_compactSpace (ChowGraph.ambient closedModels).hom
    have : QuasiSeparatedSpace (ChowGraph.ambient closedModels).left :=
      quasiSeparatedSpace_of_quasiSeparated (ChowGraph.ambient closedModels).hom
    exact (quasiCompact_iff_compactSpace _).mpr inferInstance
  obtain ⟨coordinates, hNfin, projectiveEmbedding, hg, hgS⟩ := ChowGraph.exists_isClosedImmersion_over closedModels
  have : IsProper (ChowGraph.modificationMap closedModels) :=
    ChowGraph.isProper_modificationMap closedModels reduction.iSup_opens
  have hq : IsIso (ChowGraph.modificationMap closedModels ∣_ ⨅ index, reduction.opens index) :=
    inferInstance
  refine ⟨(⨆ index, ChowGraph.projPreimage closedModels index).toScheme, ChowGraph.modificationMap closedModels ≫ reduction.closedImmersion, coordinates,
    hNfin, (⨆ index, ChowGraph.projPreimage closedModels index).ι ≫ projectiveEmbedding, inferInstance, inferInstance,
    inferInstance, ?_, ?_⟩
  · simp only [Category.assoc]
    rw [hgS, ChowGraph.modificationMap_over]
  · refine ⟨reduction.denseOpen, reduction.dense_denseOpen, ?_⟩
    have hcV : IsIso (ChowGraph.modificationMap closedModels ∣_ reduction.closedImmersion ⁻¹ᵁ reduction.denseOpen) := by
      rw [reduction.preimage_denseOpen]
      exact hq
    rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' hcV reduction.isIso_restriction

/-- A proper scheme as above has a projective proper surjective modification. -/
theorem exists_projectiveModification_of_finite_irreducibleComponents
    {sourceScheme baseScheme : Scheme.{u}} (baseMap : sourceScheme ⟶ baseScheme)
    [CompactSpace baseScheme] [QuasiSeparatedSpace baseScheme] [IsProper baseMap]
    (finiteComponents : (irreducibleComponents sourceScheme).Finite) :
    ∃ (model : Scheme.{u}) (modification : model ⟶ sourceScheme)
      (coordinates : Type u) (_ : Finite coordinates) (embedding : model ⟶ ℙ(coordinates; baseScheme)),
      IsProper modification ∧ Surjective modification ∧ IsClosedImmersion embedding ∧
      embedding ≫ ℙ(coordinates; baseScheme) ↘ baseScheme = modification ≫ baseMap ∧
      ∃ denseOpen : sourceScheme.Opens, Dense (denseOpen : Set sourceScheme) ∧
        IsIso (modification ∣_ denseOpen) := by
  obtain ⟨model, modification, coordinates, finite_coordinates, embedding,
    proper_modification, surjective_modification, immersion_embedding, commutes, denseOpen⟩ :=
    exists_chowModification_of_finite_irreducibleComponents baseMap finiteComponents
  have : IsProper (embedding ≫ ℙ(coordinates; baseScheme) ↘ baseScheme) := by
    rw [commutes]
    infer_instance
  have : IsProper embedding := .of_comp _ (ℙ(coordinates; baseScheme) ↘ baseScheme)
  exact ⟨model, modification, coordinates, finite_coordinates, embedding,
    proper_modification, surjective_modification,
    .of_isPreimmersion _ embedding.isClosedMap.isClosed_range, commutes, denseOpen⟩

end AlgebraicGeometry
