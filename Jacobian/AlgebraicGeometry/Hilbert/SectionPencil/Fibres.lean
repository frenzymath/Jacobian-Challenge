import Jacobian.AlgebraicGeometry.Hilbert.SectionPencil.Coordinates
import Jacobian.AlgebraicGeometry.Hilbert.SectionPencil.ProjectiveLine

/-!
# Nonvanishing on every residue fibre of a pencil

Independence of the two sections is preserved by the canonical field-extension
map. The actual coordinate coefficients of each residue-field point are not
both zero, so the section defining the pencil is nonzero on that fibre.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory
open CategoryTheory.Limits (zero_comp comp_zero)
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.SectionPencil

/-- An independent pencil is nonzero on every scheme-theoretic residue fibre. -/
theorem projectiveLineSection_residue_fibre_ne_zero
    {baseField : Type u} [Field baseField] {source : Scheme.{u}}
    [source.Over (Spec (.of baseField))]
    [QuasiCompact (source ↘ Spec (.of baseField))]
    [QuasiSeparated (source ↘ Spec (.of baseField))]
    (lineBundle : source.Modules) [lineBundle.IsQuasicoherent]
    (firstClass secondClass : lineBundle.H 0)
    (independent : LinearIndependent baseField ![firstClass, secondClass])
    (point : ProjectiveLine.relativeLine (Spec (.of baseField))) :
    (pullback ((Limits.pullback.snd (source ↘ Spec (.of baseField))
        (ProjectiveLine.relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField))).fiberι
          point)).map
      (projectiveLineSection (source ↘ Spec (.of baseField))
        (homOfGlobalSection lineBundle (H.zeroLinearEquiv lineBundle firstClass))
        (homOfGlobalSection lineBundle (H.zeroLinearEquiv lineBundle secondClass))) ≠ 0 := by
  let parameter := ProjectiveLine.relativeLine (Spec (.of baseField))
  let structureMap := source ↘ Spec (.of baseField)
  let extensionField : Type u := parameter.residueField point
  let parameterPoint : Spec (.of extensionField) ⟶ parameter := parameter.fromSpecResidueField point
  let coefficients : CommRingCat.of baseField ⟶ CommRingCat.of extensionField :=
    Spec.preimage (parameterPoint ≫ parameter ↘ Spec (.of baseField))
  letI : Algebra baseField extensionField := coefficients.hom.toAlgebra
  let baseMap := Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))
  have baseEquation : baseMap = parameterPoint ≫ parameter ↘ Spec (.of baseField) :=
    Spec.map_preimage (parameterPoint ≫ parameter ↘ Spec (.of baseField))
  let sourceProjection := Limits.pullback.fst structureMap baseMap
  let fieldProjection := Limits.pullback.snd structureMap baseMap
  let restriction : Limits.pullback structureMap baseMap ⟶
      Limits.pullback structureMap (parameter ↘ Spec (.of baseField)) :=
    Limits.pullback.lift sourceProjection (fieldProjection ≫ parameterPoint) (by
      rw [Category.assoc, ← baseEquation]
      exact Limits.pullback.condition)
  have sourceEquation : restriction ≫ Limits.pullback.fst _ _ = sourceProjection :=
    Limits.pullback.lift_fst ..
  have parameterEquation : restriction ≫ Limits.pullback.snd _ _ =
      fieldProjection ≫ parameterPoint := Limits.pullback.lift_snd ..
  let trivialization := fieldCoordinateIso (baseField := baseField)
    (extensionField := extensionField) parameterPoint
  have nonzero := pullback_pencilSection_ne_zero_of_field_coefficients
    (baseField := baseField) (extensionField := extensionField)
    (Limits.pullback.fst structureMap (parameter ↘ Spec (.of baseField)))
    (Limits.pullback.snd structureMap (parameter ↘ Spec (.of baseField)))
    parameterPoint restriction sourceEquation parameterEquation
    lineBundle firstClass secondClass independent _ _ trivialization
    (parameterCoefficients_ne_zero (baseField := baseField)
      (extensionField := extensionField) parameterPoint trivialization)
  let fibreComparison : Limits.pullback structureMap baseMap ⟶
      (Limits.pullback.snd structureMap (parameter ↘ Spec (.of baseField))).fiber point :=
    Limits.pullback.lift restriction fieldProjection parameterEquation
  have fibreEquation : fibreComparison ≫
      (Limits.pullback.snd structureMap (parameter ↘ Spec (.of baseField))).fiberι point =
        restriction := Limits.pullback.lift_fst ..
  intro vanishing
  have pulledVanishing : (pullback fibreComparison).map
      ((pullback ((Limits.pullback.snd structureMap
        (parameter ↘ Spec (.of baseField))).fiberι point)).map
          (projectiveLineSection structureMap
            (homOfGlobalSection lineBundle (H.zeroLinearEquiv lineBundle firstClass))
            (homOfGlobalSection lineBundle (H.zeroLinearEquiv lineBundle secondClass)))) = 0 := by
    rw [vanishing, Functor.map_zero]
  have comparison := pullbackCompOfEq_conjugate fibreComparison
    ((Limits.pullback.snd structureMap (parameter ↘ Spec (.of baseField))).fiberι point)
    restriction fibreEquation
    (projectiveLineSection structureMap
      (homOfGlobalSection lineBundle (H.zeroLinearEquiv lineBundle firstClass))
      (homOfGlobalSection lineBundle (H.zeroLinearEquiv lineBundle secondClass)))
  rw [pulledVanishing, zero_comp, comp_zero] at comparison
  exact nonzero comparison.symm

/-- The same residue-fibre statement for two actual module maps from the unit. -/
theorem projectiveLineSection_residue_fibre_ne_zero_of_sections
    {baseField : Type u} [Field baseField] {source : Scheme.{u}}
    [source.Over (Spec (.of baseField))]
    [QuasiCompact (source ↘ Spec (.of baseField))]
    [QuasiSeparated (source ↘ Spec (.of baseField))]
    (lineBundle : source.Modules) [lineBundle.IsQuasicoherent]
    (firstSection secondSection : unit source ⟶ lineBundle)
    (independent : LinearIndependent baseField
      ![(H.zeroLinearEquiv lineBundle).symm (firstSection.app ⊤ (1 : Γ(source, ⊤))),
        (H.zeroLinearEquiv lineBundle).symm (secondSection.app ⊤ (1 : Γ(source, ⊤)))])
    (point : ProjectiveLine.relativeLine (Spec (.of baseField))) :
    (pullback ((Limits.pullback.snd (source ↘ Spec (.of baseField))
        (ProjectiveLine.relativeLine (Spec (.of baseField)) ↘ Spec (.of baseField))).fiberι
          point)).map
      (projectiveLineSection (source ↘ Spec (.of baseField)) firstSection secondSection) ≠ 0 := by
  have nonzero := projectiveLineSection_residue_fibre_ne_zero lineBundle _ _ independent point
  have firstEquation :
      homOfGlobalSection lineBundle (firstSection.app ⊤ (1 : Γ(source, ⊤))) = firstSection :=
    (unitHomAddEquiv lineBundle).symm_apply_apply firstSection
  have secondEquation :
      homOfGlobalSection lineBundle (secondSection.app ⊤ (1 : Γ(source, ⊤))) = secondSection :=
    (unitHomAddEquiv lineBundle).symm_apply_apply secondSection
  simpa only [LinearEquiv.apply_symm_apply, firstEquation, secondEquation] using nonzero

end AlgebraicGeometry.SectionPencil
