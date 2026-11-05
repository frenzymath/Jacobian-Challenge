import Jacobian.AlgebraicGeometry.ChowLemma.Glue

/-!
# Global properties of the glued graph modification

The glued projections are proper when the original opens cover the target.
They restrict to an isomorphism on the common intersection. If that intersection
is dense, the proper modification is surjective.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ChowGraph

variable {coverIndex : Type*} [Finite coverIndex] [Nonempty coverIndex]
  {sourceScheme baseScheme : Scheme.{u}} {baseMap : sourceScheme ⟶ baseScheme}
  {cover : coverIndex → sourceScheme.Opens}
  (closedModels : ∀ index, ProperClosedModel ((cover index).ι ≫ baseMap))
  [QuasiCompact (tuple closedModels)] [IsSeparated baseMap]

theorem isProper_modificationMap (covers : ⨆ index, cover index = ⊤) :
    IsProper (modificationMap closedModels) :=
  IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper)
    (f := modificationMap closedModels) cover covers fun index ↦
      isProper_morphismRestrict_modificationMap closedModels index

instance isDominant_modificationMap
    [IsDominant (⨅ index, cover index).ι] :
    IsDominant (modificationMap closedModels) := by
  have dominant_intersection : IsDominant ((⨅ index, cover index).ι) := inferInstance
  rw [← toGraph_modificationMap closedModels] at dominant_intersection
  have : IsDominant ((ChowGraph closedModels).homOfLE
      (opensRange_toGraph_le_iSup closedModels) ≫ modificationMap closedModels) :=
    IsDominant.of_comp (toGraph closedModels).isoOpensRange.hom _
  exact IsDominant.of_comp
    ((ChowGraph closedModels).homOfLE (opensRange_toGraph_le_iSup closedModels)) _

instance surjective_modificationMap [IsProper (modificationMap closedModels)]
    [IsDominant (⨅ index, cover index).ι] :
    Surjective (modificationMap closedModels) := inferInstance

instance isIso_morphismRestrict_modificationMap :
    IsIso (modificationMap closedModels ∣_ ⨅ index, cover index) := by
  have inclusion_comp : (ChowGraph closedModels).homOfLE
      (opensRange_toGraph_le_iSup closedModels) ≫ modificationMap closedModels =
      (toGraph closedModels).isoOpensRange.inv ≫ (⨅ index, cover index).ι :=
    (Iso.eq_inv_comp _).mpr (toGraph_modificationMap closedModels)
  have image_le : ((ChowGraph closedModels).homOfLE
      (opensRange_toGraph_le_iSup closedModels)).opensRange ≤
      modificationMap closedModels ⁻¹ᵁ ⨅ index, cover index := by
    rintro point ⟨preimagePoint, rfl⟩
    have membership : (modificationMap closedModels).base
        (((ChowGraph closedModels).homOfLE
          (opensRange_toGraph_le_iSup closedModels)).base preimagePoint) ∈
        ⨅ index, cover index := by
      rw [← Scheme.Hom.comp_apply, inclusion_comp, Scheme.Hom.comp_apply]
      exact ((toGraph closedModels).isoOpensRange.inv.base preimagePoint).2
    exact membership
  have composite_id : ((toGraph closedModels).isoOpensRange ≪≫
      ((ChowGraph closedModels).homOfLE (opensRange_toGraph_le_iSup closedModels)).isoOpensRange).hom ≫
      ((⨆ index, projPreimage closedModels index).toScheme.homOfLE image_le ≫
        (modificationMap closedModels ∣_ ⨅ index, cover index)) = 𝟙 _ := by
    rw [← cancel_mono (⨅ index, cover index).ι]
    simp only [Iso.trans_hom, Category.assoc, Category.id_comp]
    rw [morphismRestrict_ι, Scheme.homOfLE_ι_assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc,
      toGraph_modificationMap]
  have : IsIso ((⨆ index, projPreimage closedModels index).toScheme.homOfLE image_le ≫
      (modificationMap closedModels ∣_ ⨅ index, cover index)) := by
    rw [(Iso.hom_comp_eq_id _).mp composite_id]
    infer_instance
  have image_eq : ((ChowGraph closedModels).homOfLE
      (opensRange_toGraph_le_iSup closedModels)).opensRange =
      modificationMap closedModels ⁻¹ᵁ ⨅ index, cover index := by
    have dense_graph : Dense ((toGraph closedModels).opensRange : Set (ChowGraph closedModels)) := by
      rw [Scheme.Hom.coe_opensRange]
      exact (toGraph closedModels).denseRange
    have dense_preimage : Dense ((⨆ index, projPreimage closedModels index).ι.base ⁻¹'
        ((toGraph closedModels).opensRange : Set (ChowGraph closedModels))) := by
      rw [dense_iff_closure_eq, ← (⨆ index, projPreimage closedModels index).ι.isOpenEmbedding.isOpenMap
        |>.preimage_closure_eq_closure_preimage (⨆ index, projPreimage closedModels index).ι.continuous,
        dense_graph.closure_eq, Set.preimage_univ]
    have dense_image : Dense ((((ChowGraph closedModels).homOfLE
        (opensRange_toGraph_le_iSup closedModels)).opensRange :
        Set (⨆ index, projPreimage closedModels index).toScheme)) := by
      rw [Scheme.opensRange_homOfLE]
      exact dense_preimage
    exact Scheme.Opens.eq_of_isProper_of_dense image_le
      (modificationMap closedModels ∣_ ⨅ index, cover index) fun point _ ↦ dense_image point
  have : IsIso ((⨆ index, projPreimage closedModels index).toScheme.homOfLE image_le) :=
    inferInstanceAs (IsIso ((⨆ index, projPreimage closedModels index).toScheme.isoOfEq image_eq).hom)
  exact IsIso.of_isIso_comp_left
    ((⨆ index, projPreimage closedModels index).toScheme.homOfLE image_le) _

end AlgebraicGeometry.ChowGraph
