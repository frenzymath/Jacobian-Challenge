import Jacobian.AlgebraicGeometry.ChowLemma.Graph
import Jacobian.AlgebraicGeometry.Gluing
import Jacobian.AlgebraicGeometry.Morphisms.Proper

/-!
# Gluing the projections of a Chow graph

The proper projections agree on the scheme-theoretically dense intersection,
so they glue to a modification map over a separated base. Its inverse image
of each chosen open is exactly the corresponding projection open, and the
restriction there is proper.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

namespace ChowGraph

variable {coverIndex : Type*} [Finite coverIndex] {sourceScheme baseScheme : Scheme.{u}} {baseMap : sourceScheme ⟶ baseScheme} {cover : coverIndex → sourceScheme.Opens}
  (closedModels : ∀ index, ProperClosedModel ((cover index).ι ≫ baseMap)) [QuasiCompact (tuple closedModels)]

noncomputable def projPreimage (index : coverIndex) : (ChowGraph closedModels).Opens := projection closedModels index ⁻¹ᵁ (closedModels index).inclusion.opensRange

noncomputable def projRestrict (index : coverIndex) : (projPreimage closedModels index).toScheme ⟶ (cover index).toScheme :=
  (projection closedModels index ∣_ (closedModels index).inclusion.opensRange) ≫ (closedModels index).inclusion.isoOpensRange.inv

instance isProper_projRestrict (index : coverIndex) : IsProper (projRestrict closedModels index) := by
  unfold projRestrict; infer_instance

@[reassoc (attr := simp)]
lemma projRestrict_ι (index : coverIndex) :
    projRestrict closedModels index ≫ (closedModels index).inclusion = (projPreimage closedModels index).ι ≫ projection closedModels index := by
  rw [projRestrict, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

lemma projRestrict_ι_over (index : coverIndex) :
    (projRestrict closedModels index ≫ (cover index).ι) ≫ baseMap = (projPreimage closedModels index).ι ≫ structureMap closedModels := by
  rw [Category.assoc, ← (closedModels index).commutes, projRestrict_ι_assoc, projection_structureMap]

noncomputable def projPreimageIsoOfLE (index : coverIndex) :
    (projPreimage closedModels index).toScheme ≅
      ((⨆ index, projPreimage closedModels index).ι ⁻¹ᵁ projPreimage closedModels index).toScheme :=
  ((ChowGraph closedModels).homOfLE (le_iSup (projPreimage closedModels) index)).isoOpensRange ≪≫
    (⨆ index, projPreimage closedModels index).toScheme.isoOfEq (Scheme.opensRange_homOfLE _)

@[reassoc (attr := simp)]
lemma projPreimageIsoOfLE_hom_ι (index : coverIndex) :
    (projPreimageIsoOfLE closedModels index).hom ≫
        ((⨆ index, projPreimage closedModels index).ι ⁻¹ᵁ projPreimage closedModels index).ι =
      (ChowGraph closedModels).homOfLE (le_iSup (projPreimage closedModels) index) := by
  rw [projPreimageIsoOfLE, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
    Scheme.Hom.isoOpensRange_hom_ι]

section Nonempty

variable [Nonempty coverIndex]

instance quasiCompact_opensRange_toGraph : QuasiCompact (toGraph closedModels).opensRange.ι :=
  (toGraph closedModels).isoOpensRange_inv_comp ▸ inferInstance

lemma opensRange_toGraph_le_projPreimage (index : coverIndex) :
    (toGraph closedModels).opensRange ≤ projPreimage closedModels index :=
  opensRange_toGraph_le_preimage closedModels index

lemma homOfLE_projRestrict (index : coverIndex) :
    (ChowGraph closedModels).homOfLE (opensRange_toGraph_le_projPreimage closedModels index) ≫ projRestrict closedModels index =
      (toGraph closedModels).isoOpensRange.inv ≫ sourceScheme.homOfLE (iInf_le cover index) := by
  rw [← cancel_mono (closedModels index).inclusion, Category.assoc, projRestrict_ι, Scheme.homOfLE_ι_assoc,
    Category.assoc, ← toGraph_projection, Scheme.Hom.isoOpensRange_inv_comp_assoc]

lemma homOfLE_projRestrict_ι (index : coverIndex) :
    (ChowGraph closedModels).homOfLE (opensRange_toGraph_le_projPreimage closedModels index) ≫
        projRestrict closedModels index ≫ (cover index).ι =
      (toGraph closedModels).isoOpensRange.inv ≫ (⨅ index, cover index).ι := by
  rw [← Category.assoc, homOfLE_projRestrict, Category.assoc, sourceScheme.homOfLE_ι]

lemma opensRange_toGraph_le_iSup : (toGraph closedModels).opensRange ≤ ⨆ index, projPreimage closedModels index :=
  (opensRange_toGraph_le_projPreimage closedModels (Classical.arbitrary coverIndex)).trans (le_iSup _ _)

variable [IsSeparated baseMap]

noncomputable def modificationMap : (⨆ index, projPreimage closedModels index).toScheme ⟶ sourceScheme :=
  Scheme.Opens.glueMorphismsOfDominant (projPreimage closedModels) (toGraph closedModels).opensRange
    (opensRange_toGraph_le_projPreimage closedModels) baseMap (structureMap closedModels) (fun index ↦ projRestrict closedModels index ≫ (cover index).ι)
    (projRestrict_ι_over closedModels) fun index j ↦ by
      rw [homOfLE_projRestrict_ι, homOfLE_projRestrict_ι]

@[reassoc (attr := simp)]
lemma homOfLE_modificationMap (index : coverIndex) :
    (ChowGraph closedModels).homOfLE (le_iSup (projPreimage closedModels) index) ≫ modificationMap closedModels =
      projRestrict closedModels index ≫ (cover index).ι :=
  Scheme.Opens.homOfLE_glueMorphismsOfDominant (projPreimage closedModels) (toGraph closedModels).opensRange
    (opensRange_toGraph_le_projPreimage closedModels) baseMap (structureMap closedModels) _ _ _ index

@[reassoc (attr := simp)]
lemma modificationMap_over :
    modificationMap closedModels ≫ baseMap = (⨆ index, projPreimage closedModels index).ι ≫ structureMap closedModels :=
  Scheme.Opens.glueMorphismsOfDominant_comp (projPreimage closedModels) (toGraph closedModels).opensRange
    (opensRange_toGraph_le_projPreimage closedModels) baseMap (structureMap closedModels) _ _ _

lemma toGraph_modificationMap :
    (toGraph closedModels).isoOpensRange.hom ≫ (ChowGraph closedModels).homOfLE (opensRange_toGraph_le_iSup closedModels) ≫
      modificationMap closedModels = (⨅ index, cover index).ι := by
  obtain ⟨index⟩ := ‹Nonempty coverIndex›
  have key : (ChowGraph closedModels).homOfLE (opensRange_toGraph_le_iSup closedModels) =
      (ChowGraph closedModels).homOfLE (opensRange_toGraph_le_projPreimage closedModels index) ≫
        (ChowGraph closedModels).homOfLE (le_iSup (projPreimage closedModels) index) :=
    ((ChowGraph closedModels).homOfLE_homOfLE _ _).symm
  rw [key, Category.assoc, homOfLE_modificationMap, homOfLE_projRestrict_ι,
    Iso.hom_inv_id_assoc]

instance isSeparated_modificationMap : IsSeparated (modificationMap closedModels) :=
  have : IsSeparated (modificationMap closedModels ≫ baseMap) := by rw [modificationMap_over]; infer_instance
  .of_comp (f := modificationMap closedModels) (g := baseMap)

lemma le_preimage_modificationMap (index : coverIndex) :
    (⨆ index, projPreimage closedModels index).ι ⁻¹ᵁ projPreimage closedModels index ≤ modificationMap closedModels ⁻¹ᵁ cover index := by
  rw [← Scheme.opensRange_homOfLE (le_iSup (projPreimage closedModels) index)]
  rintro point ⟨sourcePoint, rfl⟩
  have membership : (modificationMap closedModels).base
      (((ChowGraph closedModels).homOfLE (le_iSup (projPreimage closedModels) index)).base sourcePoint) ∈ cover index := by
    rw [← Scheme.Hom.comp_apply, homOfLE_modificationMap, Scheme.Hom.comp_apply]
    exact ((projRestrict closedModels index).base sourcePoint).2
  exact membership

lemma projPreimageIsoOfLE_hom_homOfLE_morphismRestrict (index : coverIndex) :
    (projPreimageIsoOfLE closedModels index).hom ≫
      (⨆ index, projPreimage closedModels index).toScheme.homOfLE (le_preimage_modificationMap closedModels index) ≫
        (modificationMap closedModels ∣_ cover index) = projRestrict closedModels index := by
  rw [← cancel_mono (cover index).ι, Category.assoc, Category.assoc, morphismRestrict_ι,
    Scheme.homOfLE_ι_assoc, projPreimageIsoOfLE_hom_ι_assoc, homOfLE_modificationMap]

instance isProper_homOfLE_morphismRestrict (index : coverIndex) :
    IsProper ((⨆ index, projPreimage closedModels index).toScheme.homOfLE (le_preimage_modificationMap closedModels index) ≫
      (modificationMap closedModels ∣_ cover index)) := by
  refine (MorphismProperty.cancel_left_of_respectsIso @IsProper
    (projPreimageIsoOfLE closedModels index).hom _).mp ?_
  rw [projPreimageIsoOfLE_hom_homOfLE_morphismRestrict]
  infer_instance

theorem preimage_modificationMap (index : coverIndex) :
    modificationMap closedModels ⁻¹ᵁ cover index = (⨆ index, projPreimage closedModels index).ι ⁻¹ᵁ projPreimage closedModels index := by
  have h1 : Dense ((toGraph closedModels).opensRange : Set (ChowGraph closedModels)) := by
    rw [Scheme.Hom.coe_opensRange]
    exact (toGraph closedModels).denseRange
  have h2 : Dense ((⨆ index, projPreimage closedModels index).ι.base ⁻¹'
      (projPreimage closedModels index : Set (ChowGraph closedModels))) := by
    rw [dense_iff_closure_eq, ← (⨆ index, projPreimage closedModels index).ι.isOpenEmbedding.isOpenMap
      |>.preimage_closure_eq_closure_preimage (⨆ index, projPreimage closedModels index).ι.continuous,
      (h1.mono (opensRange_toGraph_le_projPreimage closedModels index)).closure_eq, Set.preimage_univ]
  exact (Scheme.Opens.eq_of_isProper_of_dense (le_preimage_modificationMap closedModels index)
    (modificationMap closedModels ∣_ cover index) fun point _ ↦ h2 point).symm

instance isProper_morphismRestrict_modificationMap (index : coverIndex) :
    IsProper (modificationMap closedModels ∣_ cover index) := by
  have inclusion_iso : IsIso ((⨆ index, projPreimage closedModels index).toScheme.homOfLE
      (le_preimage_modificationMap closedModels index)) :=
    inferInstanceAs (IsIso ((⨆ index, projPreimage closedModels index).toScheme.isoOfEq
      (preimage_modificationMap closedModels index).symm).hom)
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper
    ((⨆ index, projPreimage closedModels index).toScheme.homOfLE (le_preimage_modificationMap closedModels index)) _).mp
    inferInstance

end Nonempty

end ChowGraph

end AlgebraicGeometry
