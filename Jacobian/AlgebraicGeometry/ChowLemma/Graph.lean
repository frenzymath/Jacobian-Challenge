import Jacobian.AlgebraicGeometry.ChowLemma.ClosedModel
import Jacobian.CategoryTheory.MorphismProperty.Products
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The closure of a tuple of projective immersions

Proper closed models of finitely many open subschemes give a tuple morphism
from their intersection. Its scheme-theoretic image is proper over the base,
contains that intersection as a dense open when the tuple is quasi-compact
and the index family is nonempty,
and projects properly to each closed model.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

namespace ChowGraph

variable {coverIndex : Type*} [Finite coverIndex] {sourceScheme baseScheme : Scheme.{u}} {baseMap : sourceScheme ⟶ baseScheme} {cover : coverIndex → sourceScheme.Opens}
  (closedModels : ∀ index, ProperClosedModel ((cover index).ι ≫ baseMap))

noncomputable def ambient : Over baseScheme := ∏ᶜ fun index ↦ Over.mk (ℙ((closedModels index).coordinates; baseScheme) ↘ baseScheme)

instance isProper_ambient_hom : IsProper (ambient closedModels).hom :=
  haveI (index : coverIndex) : IsProper (Over.mk (ℙ((closedModels index).coordinates; baseScheme) ↘ baseScheme)).hom :=
    inferInstanceAs (IsProper (ℙ((closedModels index).coordinates; baseScheme) ↘ baseScheme))
  MorphismProperty.pi_hom (categoryType := Scheme.{u}) (baseObject := baseScheme) @IsProper
    (fun index : coverIndex ↦ Over.mk (ℙ((closedModels index).coordinates; baseScheme) ↘ baseScheme))
    (fun _ ↦ inferInstance)

noncomputable def ambientπ (index : coverIndex) : (ambient closedModels).left ⟶ ℙ((closedModels index).coordinates; baseScheme) :=
  (Pi.π (fun index ↦ Over.mk (ℙ((closedModels index).coordinates; baseScheme) ↘ baseScheme)) index).left

@[reassoc (attr := simp)]
lemma ambientπ_over (index : coverIndex) : ambientπ closedModels index ≫ ℙ((closedModels index).coordinates; baseScheme) ↘ baseScheme = (ambient closedModels).hom :=
  Over.w (Pi.π (fun index ↦ Over.mk (ℙ((closedModels index).coordinates; baseScheme) ↘ baseScheme)) index)

noncomputable def toProjectiveSpace (index : coverIndex) : ↑(⨅ index, cover index) ⟶ ℙ((closedModels index).coordinates; baseScheme) :=
  sourceScheme.homOfLE (iInf_le cover index) ≫ (closedModels index).inclusion ≫ (closedModels index).embedding

instance isImmersion_toProjectiveSpace (index : coverIndex) : IsImmersion (toProjectiveSpace closedModels index) := by
  unfold toProjectiveSpace; infer_instance

omit [Finite coverIndex] in
@[reassoc (attr := simp)]
lemma toProjectiveSpace_over (index : coverIndex) :
    toProjectiveSpace closedModels index ≫ ℙ((closedModels index).coordinates; baseScheme) ↘ baseScheme = (⨅ index, cover index).ι ≫ baseMap := by
  rw [toProjectiveSpace, Category.assoc, Category.assoc, (closedModels index).commutes, ← Category.assoc,
    sourceScheme.homOfLE_ι]

noncomputable def tuple : ↑(⨅ index, cover index) ⟶ (ambient closedModels).left :=
  (Pi.lift (f := fun index ↦ Over.mk (ℙ((closedModels index).coordinates; baseScheme) ↘ baseScheme))
    (fun index ↦ Over.homMk (U := Over.mk ((⨅ index, cover index).ι ≫ baseMap)) (toProjectiveSpace closedModels index)
      (toProjectiveSpace_over closedModels index))).left

@[reassoc (attr := simp)]
lemma tuple_ambientπ (index : coverIndex) : tuple closedModels ≫ ambientπ closedModels index = toProjectiveSpace closedModels index := by
  rw [tuple, ambientπ, ← Over.comp_left, Pi.lift_comp_π]
  rfl

@[reassoc (attr := simp)]
lemma tuple_over : tuple closedModels ≫ (ambient closedModels).hom = (⨅ index, cover index).ι ≫ baseMap :=
  Over.w _

instance isImmersion_tuple [Nonempty coverIndex] : IsImmersion (tuple closedModels) := by
  obtain ⟨index⟩ := ‹Nonempty coverIndex›
  have : IsImmersion (tuple closedModels ≫ ambientπ closedModels index) := by
    rw [tuple_ambientπ]
    infer_instance
  exact .of_comp _ (ambientπ closedModels index)

end ChowGraph

noncomputable def ChowGraph {coverIndex : Type*} [Finite coverIndex] {sourceScheme baseScheme : Scheme.{u}} {baseMap : sourceScheme ⟶ baseScheme}
    {cover : coverIndex → sourceScheme.Opens} (closedModels : ∀ index, ProperClosedModel ((cover index).ι ≫ baseMap)) : Scheme.{u} :=
  (ChowGraph.tuple closedModels).image

namespace ChowGraph

variable {coverIndex : Type*} [Finite coverIndex] {sourceScheme baseScheme : Scheme.{u}} {baseMap : sourceScheme ⟶ baseScheme} {cover : coverIndex → sourceScheme.Opens}
  (closedModels : ∀ index, ProperClosedModel ((cover index).ι ≫ baseMap))

noncomputable def embedding : ChowGraph closedModels ⟶ (ambient closedModels).left := (tuple closedModels).imageι

instance isClosedImmersion_embedding : IsClosedImmersion (embedding closedModels) := by
  unfold embedding; infer_instance

noncomputable def toGraph : ↑(⨅ index, cover index) ⟶ ChowGraph closedModels := (tuple closedModels).toImage

@[reassoc (attr := simp)]
lemma toGraph_embedding : toGraph closedModels ≫ embedding closedModels = tuple closedModels := (tuple closedModels).toImage_imageι

noncomputable def structureMap : ChowGraph closedModels ⟶ baseScheme := embedding closedModels ≫ (ambient closedModels).hom

instance isProper_structureMap : IsProper (structureMap closedModels) := by
  unfold structureMap; infer_instance

@[reassoc (attr := simp)]
lemma toGraph_structureMap : toGraph closedModels ≫ structureMap closedModels = (⨅ index, cover index).ι ≫ baseMap := by
  rw [structureMap, toGraph_embedding_assoc, tuple_over]

instance quasiCompact_tuple [NoetherianSpace sourceScheme] : QuasiCompact (tuple closedModels) := by
  have : NoetherianSpace ↑(⨅ index, cover index) :=
    inferInstanceAs (NoetherianSpace ((⨅ index, cover index : sourceScheme.Opens) : Set sourceScheme))
  infer_instance

section QuasiCompact

variable [QuasiCompact (tuple closedModels)]

instance quasiCompact_toGraph : QuasiCompact (toGraph closedModels) := by
  unfold toGraph
  infer_instance

instance isSchemeTheoreticallyDominant_toGraph :
    IsSchemeTheoreticallyDominant (toGraph closedModels) := by
  unfold toGraph; infer_instance

instance isDominant_toGraph : IsDominant (toGraph closedModels) := by
  unfold toGraph; infer_instance

instance isOpenImmersion_toGraph [Nonempty coverIndex] : IsOpenImmersion (toGraph closedModels) := by
  unfold toGraph; infer_instance

instance isSchemeTheoreticallyDominant_opensRange_toGraph [Nonempty coverIndex] :
    IsSchemeTheoreticallyDominant (toGraph closedModels).opensRange.ι :=
  (toGraph closedModels).isoOpensRange_inv_comp ▸ inferInstance

noncomputable def projection (index : coverIndex) : ChowGraph closedModels ⟶ (closedModels index).model :=
  IsClosedImmersion.lift (closedModels index).embedding (embedding closedModels ≫ ambientπ closedModels index) <| by
    have key : (embedding closedModels ≫ ambientπ closedModels index).ker = (tuple closedModels ≫ ambientπ closedModels index).ker := by
      conv_rhs => rw [← toGraph_embedding closedModels, Category.assoc]
      exact (Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant (toGraph closedModels)
        (embedding closedModels ≫ ambientπ closedModels index)).symm
    rw [key, tuple_ambientπ, toProjectiveSpace, ← Category.assoc]
    exact Scheme.Hom.le_ker_comp _ _

@[reassoc (attr := simp)]
lemma projection_embedding (index : coverIndex) : projection closedModels index ≫ (closedModels index).embedding = embedding closedModels ≫ ambientπ closedModels index :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
lemma projection_structureMap (index : coverIndex) : projection closedModels index ≫ (closedModels index).embedding ≫ ℙ((closedModels index).coordinates; baseScheme) ↘ baseScheme = structureMap closedModels := by
  rw [← Category.assoc, projection_embedding, Category.assoc, ambientπ_over, structureMap]

instance isProper_projection (index : coverIndex) : IsProper (projection closedModels index) := by
  have : IsProper (projection closedModels index ≫ (closedModels index).embedding ≫ ℙ((closedModels index).coordinates; baseScheme) ↘ baseScheme) := by
    rw [projection_structureMap]; infer_instance
  exact IsProper.of_comp (f := projection closedModels index) (g := (closedModels index).embedding ≫ ℙ((closedModels index).coordinates; baseScheme) ↘ baseScheme)

@[reassoc (attr := simp)]
lemma toGraph_projection (index : coverIndex) :
    toGraph closedModels ≫ projection closedModels index = sourceScheme.homOfLE (iInf_le cover index) ≫ (closedModels index).inclusion := by
  rw [← cancel_mono (closedModels index).embedding, Category.assoc, projection_embedding, toGraph_embedding_assoc, tuple_ambientπ,
    toProjectiveSpace, Category.assoc]

lemma opensRange_toGraph_le_preimage [Nonempty coverIndex] (index : coverIndex) :
    (toGraph closedModels).opensRange ≤ projection closedModels index ⁻¹ᵁ (closedModels index).inclusion.opensRange := by
  rintro point ⟨intersectionPoint, rfl⟩
  exact ⟨sourceScheme.homOfLE (iInf_le cover index) intersectionPoint, by
    rw [← Scheme.Hom.comp_apply, ← toGraph_projection, Scheme.Hom.comp_apply]⟩

end QuasiCompact

end ChowGraph

end AlgebraicGeometry
