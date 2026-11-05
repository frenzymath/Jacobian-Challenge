import Jacobian.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
import Jacobian.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Proper closed models of affine schemes

The scheme-theoretic image of a projective immersion gives a projective model
containing the source as a scheme-theoretically dense open subscheme.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A projective model containing the source as a scheme-theoretically dense open. -/
structure ProperClosedModel {sourceScheme baseScheme : Scheme.{u}}
    (structureMap : sourceScheme ⟶ baseScheme) where
  coordinates : Type u
  [finite_coordinates : Finite coordinates]
  model : Scheme.{u}
  embedding : model ⟶ ℙ(coordinates; baseScheme)
  [isClosedImmersion_embedding : IsClosedImmersion embedding]
  inclusion : sourceScheme ⟶ model
  [isOpenImmersion_inclusion : IsOpenImmersion inclusion]
  [isSchemeTheoreticallyDominant_inclusion : IsSchemeTheoreticallyDominant inclusion]
  commutes : inclusion ≫ embedding ≫ ℙ(coordinates; baseScheme) ↘ baseScheme = structureMap

attribute [instance] ProperClosedModel.finite_coordinates
  ProperClosedModel.isClosedImmersion_embedding ProperClosedModel.isOpenImmersion_inclusion
  ProperClosedModel.isSchemeTheoreticallyDominant_inclusion

namespace ProperClosedModel

variable {sourceScheme baseScheme : Scheme.{u}} {structureMap : sourceScheme ⟶ baseScheme}
  (closedModel : ProperClosedModel structureMap)

instance isProper_embedding_comp_over :
    IsProper (closedModel.embedding ≫ ℙ(closedModel.coordinates; baseScheme) ↘ baseScheme) :=
  inferInstance

end ProperClosedModel

/-- An affine scheme of finite type over a quasi-compact quasi-separated base
admits a proper closed model. -/
theorem nonempty_properClosedModel {sourceScheme baseScheme : Scheme.{u}}
    [IsAffine sourceScheme] [CompactSpace baseScheme] [QuasiSeparatedSpace baseScheme]
    (structureMap : sourceScheme ⟶ baseScheme) [LocallyOfFiniteType structureMap] :
    Nonempty (ProperClosedModel structureMap) := by
  obtain ⟨coordinates, _, immersion, _, commutes⟩ :=
    exists_isImmersion_projectiveSpace structureMap
  have : CompactSpace ℙ(coordinates; baseScheme) :=
    QuasiCompact.compactSpace_of_compactSpace (ℙ(coordinates; baseScheme) ↘ baseScheme)
  have : QuasiSeparatedSpace ℙ(coordinates; baseScheme) :=
    quasiSeparatedSpace_of_quasiSeparated (ℙ(coordinates; baseScheme) ↘ baseScheme)
  have : QuasiCompact immersion := (quasiCompact_iff_compactSpace immersion).mpr inferInstance
  exact ⟨{
    coordinates := coordinates
    model := immersion.image
    embedding := immersion.imageι
    inclusion := immersion.toImage
    commutes := by rw [immersion.toImage_imageι_assoc, commutes] }⟩

end AlgebraicGeometry
