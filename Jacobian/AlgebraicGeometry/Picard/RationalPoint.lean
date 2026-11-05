import Jacobian.AlgebraicGeometry.Picard.Descent
import Jacobian.AlgebraicGeometry.Modules.StructureSheaf

/-!
# Picard classes normalized at a rational point

For a proper geometrically integral scheme over a field, a rational point
identifies normalized Picard classes with the relative Picard sheaf. The
identification is induced by inclusion of normalized classes and gives fpqc
descent and an equivalence of representability.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable {baseField : Type schemeUniverse} [Field baseField]
  {source : Scheme.{schemeUniverse}} [source.Over (Spec (.of baseField))]
  [IsProper (source ↘ Spec (.of baseField))]
  [GeometricallyIntegral (source ↘ Spec (.of baseField))]

/-- Normalized classes map isomorphically to the relative Picard sheaf. -/
theorem isIso_picardFunctorNormalized_ι_comp_toPicardFunctor_of_geometricallyIntegral
    (rationalPoint : Spec (.of baseField) ⟶ source)
    (sectionCondition : rationalPoint ≫ source ↘ Spec (.of baseField) = 𝟙 _) :
    IsIso ((picardFunctorNormalized (source ↘ Spec (.of baseField))
      rationalPoint sectionCondition).ι ≫ toPicardFunctor (source ↘ Spec (.of baseField))) :=
  isIso_picardFunctorNormalized_ι_comp_toPicardFunctor _ rationalPoint sectionCondition
    isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral

/-- Normalization at a rational point identifies the normalized presheaf with the Picard sheaf. -/
def normalizedPicardIso (rationalPoint : Spec (.of baseField) ⟶ source)
    (sectionCondition : rationalPoint ≫ source ↘ Spec (.of baseField) = 𝟙 _) :
    (picardFunctorNormalized (source ↘ Spec (.of baseField))
      rationalPoint sectionCondition).toFunctor ≅
      (picardFunctor (source ↘ Spec (.of baseField))).obj :=
  picardFunctorNormalizedIso _ rationalPoint sectionCondition
    isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral

/-- The normalization isomorphism is the inclusion of classes followed by sheafification. -/
@[simp]
theorem normalizedPicardIso_hom (rationalPoint : Spec (.of baseField) ⟶ source)
    (sectionCondition : rationalPoint ≫ source ↘ Spec (.of baseField) = 𝟙 _) :
    (normalizedPicardIso rationalPoint sectionCondition).hom =
      (picardFunctorNormalized (source ↘ Spec (.of baseField)) rationalPoint sectionCondition).ι ≫
        toPicardFunctor (source ↘ Spec (.of baseField)) :=
  rfl

/-- Representability is unchanged by normalization at a rational point. -/
theorem isRepresentable_picardFunctorNormalized_iff_of_geometricallyIntegral
    (rationalPoint : Spec (.of baseField) ⟶ source)
    (sectionCondition : rationalPoint ≫ source ↘ Spec (.of baseField) = 𝟙 _) :
    (picardFunctorNormalized (source ↘ Spec (.of baseField))
      rationalPoint sectionCondition).toFunctor.IsRepresentable ↔
        (picardFunctor (source ↘ Spec (.of baseField))).obj.IsRepresentable :=
  isRepresentable_picardFunctorNormalized_iff _ rationalPoint sectionCondition
    isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral

/-- The relative Picard sheaf of a pointed proper geometrically integral scheme is an fpqc sheaf. -/
theorem isSheaf_fpqc_picardFunctor (rationalPoint : Spec (.of baseField) ⟶ source)
    (sectionCondition : rationalPoint ≫ source ↘ Spec (.of baseField) = 𝟙 _) :
    Presheaf.IsSheaf (fpqcTopology.over (Spec (.of baseField)))
      (picardFunctor (source ↘ Spec (.of baseField))).obj :=
  (Presheaf.isSheaf_of_iso_iff (normalizedPicardIso rationalPoint sectionCondition)).mp
    (isSheaf_fpqc_picardFunctorNormalized _ rationalPoint sectionCondition
      isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral)

end AlgebraicGeometry
