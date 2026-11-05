import Jacobian.FieldTheory.TensorProduct.Diagonal
import Jacobian.AlgebraicGeometry.Limits.Descent
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Finite-level descent over an algebraic field extension

The spectrum of an algebraic extension is the inverse limit of the spectra of
its finite intermediate fields, and also of its tensor diagonals. A finitely
presented scheme over the extension consequently descends to a finite level.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe fieldUniverse

open CategoryTheory Limits IntermediateField TensorProduct

namespace AlgebraicGeometry

variable (baseField extensionField : Type fieldUniverse) [Field baseField] [Field extensionField] [Algebra baseField extensionField] [Algebra.IsAlgebraic baseField extensionField]

/-- `Spec extensionField` as a cone over the schemes `Spec subextension`, `subextension` a finite subextension of `extensionField/baseField`. -/
noncomputable abbrev subextSpecCone : Cone ((subextDiagram baseField extensionField).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (subextCocone baseField extensionField).op

/-- `Spec extensionField` is the limit of the schemes `Spec subextension` over the finite subextensions `subextension` of `extensionField/baseField`. -/
noncomputable def isLimitSubextSpecCone : IsLimit (subextSpecCone baseField extensionField) :=
  isLimitOfPreserves Scheme.Spec (isColimitSubextCocone (baseField := baseField) (extensionField := extensionField)).op

/-- `Spec extensionField` as a cone over the schemes `Spec (extensionField ⊗_L extensionField)`, `subextension` a finite subextension of `extensionField/baseField`,
through the diagonal. -/
noncomputable abbrev diagonalSpecCone : Cone ((diagonalDiagram baseField extensionField).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (diagonalCocone baseField extensionField).op

/-- `Spec extensionField` is the limit of the schemes `Spec (extensionField ⊗_L extensionField)` over the finite subextensions `subextension` of
`extensionField/baseField`, through the diagonal. -/
noncomputable def isLimitDiagonalSpecCone : IsLimit (diagonalSpecCone baseField extensionField) :=
  isLimitOfPreserves Scheme.Spec (isColimitDiagonalCocone (baseField := baseField) (extensionField := extensionField)).op

variable {baseField extensionField}

/-- **Schemes of finite presentation over an algebraic extension descend to a finite
subextension**. -/
theorem exists_finiteSubext_isPullback {sourceScheme : Scheme.{fieldUniverse}} (sourceMap : sourceScheme ⟶ Spec (.of extensionField))
    [LocallyOfFinitePresentation sourceMap] [QuasiCompact sourceMap] [QuasiSeparated sourceMap] :
    ∃ (subextension : FiniteSubext baseField extensionField) (stageScheme : Scheme.{fieldUniverse}) (stageMap : stageScheme ⟶ Spec (.of subextension.1))
      (_ : LocallyOfFinitePresentation stageMap) (_ : QuasiCompact stageMap) (_ : QuasiSeparated stageMap)
      (comparison : sourceScheme ⟶ stageScheme),
      IsPullback comparison sourceMap stageMap (Spec.map (CommRingCat.ofHom (algebraMap subextension.1 extensionField))) := by
  have : ∀ {sourceIndex targetIndex : (FiniteSubext baseField extensionField)ᵒᵖ} (transition : sourceIndex ⟶ targetIndex),
      IsAffineHom (((subextDiagram baseField extensionField).op ⋙ Scheme.Spec).map transition) := fun transition ↦
    isAffineHom_of_isAffine (X := Spec _) (Y := Spec _) _
  have : ∀ sourceIndex : (FiniteSubext baseField extensionField)ᵒᵖ,
      CompactSpace (((subextDiagram baseField extensionField).op ⋙ Scheme.Spec).obj sourceIndex) := fun sourceIndex ↦
    have : IsAffine (((subextDiagram baseField extensionField).op ⋙ Scheme.Spec).obj sourceIndex) :=
      inferInstanceAs (IsAffine (Spec _))
    inferInstance
  have : ∀ sourceIndex : (FiniteSubext baseField extensionField)ᵒᵖ,
      QuasiSeparatedSpace (((subextDiagram baseField extensionField).op ⋙ Scheme.Spec).obj sourceIndex) := fun sourceIndex ↦
    have : IsAffine (((subextDiagram baseField extensionField).op ⋙ Scheme.Spec).obj sourceIndex) :=
      inferInstanceAs (IsAffine (Spec _))
    inferInstance
  obtain ⟨⟨subextension⟩, stageScheme, stageMap, h₁, h₂, h₃, comparison, hh⟩ := Scheme.exists_isPullback_of_finitePresentation
    (isLimitSubextSpecCone baseField extensionField) (sourceScheme := sourceScheme) sourceMap
  exact ⟨subextension, stageScheme, stageMap, h₁, h₂, h₃, comparison, hh⟩

section Projections

set_option linter.unusedSectionVars false

variable (subextension : FiniteSubext baseField extensionField)

/-- The first projection `Spec (extensionField ⊗_L extensionField) ⟶ Spec extensionField`. -/
noncomputable abbrev tensorSpecPr₁ : Spec (.of (extensionField ⊗[subextension.1] extensionField)) ⟶ Spec (.of extensionField) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)

/-- The second projection `Spec (extensionField ⊗_L extensionField) ⟶ Spec extensionField`. -/
noncomputable abbrev tensorSpecPr₂ : Spec (.of (extensionField ⊗[subextension.1] extensionField)) ⟶ Spec (.of extensionField) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)

/-- `Spec (extensionField ⊗_L extensionField)` is the fibre product `Spec extensionField ×_{Spec subextension} Spec extensionField`. -/
lemma isPullback_tensorSpecPr :
    IsPullback (tensorSpecPr₁ subextension) (tensorSpecPr₂ subextension)
      (Spec.map (CommRingCat.ofHom (algebraMap subextension.1 extensionField)))
      (Spec.map (CommRingCat.ofHom (algebraMap subextension.1 extensionField))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct subextension.1 extensionField extensionField)

lemma diagonalSpecCone_π_comp_tensorSpecPr₁ :
    (diagonalSpecCone baseField extensionField).π.app (.op subextension) ≫ tensorSpecPr₁ subextension = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of extensionField))
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext element
  change (Algebra.TensorProduct.lmul' subextension.1 (S := extensionField)) (element ⊗ₜ 1) = element
  simp

lemma diagonalSpecCone_π_comp_tensorSpecPr₂ :
    (diagonalSpecCone baseField extensionField).π.app (.op subextension) ≫ tensorSpecPr₂ subextension = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of extensionField))
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext element
  change (Algebra.TensorProduct.lmul' subextension.1 (S := extensionField)) (1 ⊗ₜ element) = element
  simp

variable {subextension} {largerSubextension : FiniteSubext baseField extensionField}

lemma map_comp_tensorSpecPr₁ (transition : Opposite.op largerSubextension ⟶ .op subextension) :
    ((diagonalDiagram baseField extensionField).op ⋙ Scheme.Spec).map transition ≫ tensorSpecPr₁ subextension = tensorSpecPr₁ largerSubextension := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

lemma map_comp_tensorSpecPr₂ (transition : Opposite.op largerSubextension ⟶ .op subextension) :
    ((diagonalDiagram baseField extensionField).op ⋙ Scheme.Spec).map transition ≫ tensorSpecPr₂ subextension = tensorSpecPr₂ largerSubextension := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

end Projections

end AlgebraicGeometry
