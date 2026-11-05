import Jacobian.AlgebraicGeometry.Modules.Endomorphism
import Jacobian.AlgebraicGeometry.Modules.PushforwardUnit

/-!
# Rigidifying isomorphisms along a section

Trivializations of two invertible module sheaves along a section can be made
compatible with any isomorphism between them by rescaling it with a global
unit pulled back from the base. If pullback of global functions from the base
is surjective, the compatible isomorphism is unique.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {source base : Scheme.{schemeUniverse}}

/-- An isomorphism can be rescaled to respect chosen trivializations along a section. -/
theorem exists_iso_of_pullback_trivializations (projection : source ⟶ base)
    (sectionMorphism : base ⟶ source) (sectionCondition : sectionMorphism ≫ projection = 𝟙 base)
    {moduleSheaf targetSheaf : source.Modules} [moduleSheaf.IsInvertible]
    (sourceTrivialization : (pullback sectionMorphism).obj moduleSheaf ≅
      SheafOfModules.unit base.ringCatSheaf)
    (targetTrivialization : (pullback sectionMorphism).obj targetSheaf ≅
      SheafOfModules.unit base.ringCatSheaf)
    (isomorphism : moduleSheaf ≅ targetSheaf) :
    ∃ normalizedIso : moduleSheaf ≅ targetSheaf,
      (pullback sectionMorphism).map normalizedIso.hom ≫ targetTrivialization.hom =
        sourceTrivialization.hom := by
  let pulledModule := (pullback sectionMorphism).obj moduleSheaf
  let discrepancy : pulledModule ⟶ pulledModule :=
    (pullback sectionMorphism).map isomorphism.hom ≫
      targetTrivialization.hom ≫ sourceTrivialization.inv
  have : IsIso discrepancy := by dsimp only [discrepancy]; infer_instance
  obtain ⟨inverseScalar, inverseScalarEquation⟩ := exists_eq_smulHom pulledModule (inv discrepancy)
  obtain ⟨scalar, scalarEquation⟩ := exists_eq_smulHom pulledModule discrepancy
  have inverseProduct : inverseScalar * scalar = 1 := by
    refine eq_of_smulHom_eq pulledModule ?_
    rw [smulHom_mul, smulHom_one, ← inverseScalarEquation, ← scalarEquation, IsIso.hom_inv_id]
  have product : scalar * inverseScalar = 1 := by rw [mul_comm, inverseProduct]
  let liftedScalar := projection.appTop inverseScalar
  let liftedInverse := projection.appTop scalar
  have sectionEquation : sectionMorphism.appTop liftedScalar = inverseScalar := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, sectionCondition]
    rfl
  have : IsIso (moduleSheaf.smulHom liftedScalar) := ⟨moduleSheaf.smulHom liftedInverse, by
    rw [← smulHom_mul, ← map_mul, product, map_one, smulHom_one], by
    rw [← smulHom_mul, ← map_mul, inverseProduct, map_one, smulHom_one]⟩
  refine ⟨asIso (moduleSheaf.smulHom liftedScalar ≫ isomorphism.hom), ?_⟩
  change (pullback sectionMorphism).map
      (moduleSheaf.smulHom liftedScalar ≫ isomorphism.hom) ≫ targetTrivialization.hom =
    sourceTrivialization.hom
  rw [Functor.map_comp, pullback_map_smulHom, sectionEquation, ← inverseScalarEquation,
    Category.assoc]
  calc
    inv discrepancy ≫ (pullback sectionMorphism).map isomorphism.hom ≫ targetTrivialization.hom =
        inv discrepancy ≫ (discrepancy ≫ sourceTrivialization.hom) := by simp [discrepancy]
    _ = sourceTrivialization.hom := by
      rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- Surjectivity on global functions makes a section-compatible isomorphism unique. -/
theorem existsUnique_iso_of_pullback_trivializations (projection : source ⟶ base)
    (sectionMorphism : base ⟶ source) (sectionCondition : sectionMorphism ≫ projection = 𝟙 base)
    (surjective : Function.Surjective projection.appTop)
    {moduleSheaf targetSheaf : source.Modules} [moduleSheaf.IsInvertible]
    (sourceTrivialization : (pullback sectionMorphism).obj moduleSheaf ≅
      SheafOfModules.unit base.ringCatSheaf)
    (targetTrivialization : (pullback sectionMorphism).obj targetSheaf ≅
      SheafOfModules.unit base.ringCatSheaf)
    (isomorphism : moduleSheaf ≅ targetSheaf) :
    ∃! normalizedIso : moduleSheaf ≅ targetSheaf,
      (pullback sectionMorphism).map normalizedIso.hom ≫ targetTrivialization.hom =
        sourceTrivialization.hom := by
  obtain ⟨normalizedIso, normalized⟩ := exists_iso_of_pullback_trivializations projection
    sectionMorphism sectionCondition sourceTrivialization targetTrivialization isomorphism
  refine ⟨normalizedIso, normalized, fun otherIso otherNormalized ↦ Iso.ext ?_⟩
  apply eq_of_pullback_map_eq projection sectionMorphism sectionCondition surjective
  exact (cancel_mono targetTrivialization.hom).mp (otherNormalized.trans normalized.symm)

/-- Section-compatible isomorphisms satisfy the cocycle identity by rigidity. -/
theorem iso_trans_eq_of_pullback_trivializations (projection : source ⟶ base)
    (sectionMorphism : base ⟶ source) (sectionCondition : sectionMorphism ≫ projection = 𝟙 base)
    (surjective : Function.Surjective projection.appTop)
    {firstSheaf secondSheaf thirdSheaf : source.Modules} [firstSheaf.IsInvertible]
    (firstTrivialization : (pullback sectionMorphism).obj firstSheaf ≅
      SheafOfModules.unit base.ringCatSheaf)
    (secondTrivialization : (pullback sectionMorphism).obj secondSheaf ≅
      SheafOfModules.unit base.ringCatSheaf)
    (thirdTrivialization : (pullback sectionMorphism).obj thirdSheaf ≅
      SheafOfModules.unit base.ringCatSheaf)
    (firstIso : firstSheaf ≅ secondSheaf) (secondIso : secondSheaf ≅ thirdSheaf)
    (directIso : firstSheaf ≅ thirdSheaf)
    (firstNormalized : (pullback sectionMorphism).map firstIso.hom ≫
      secondTrivialization.hom = firstTrivialization.hom)
    (secondNormalized : (pullback sectionMorphism).map secondIso.hom ≫
      thirdTrivialization.hom = secondTrivialization.hom)
    (directNormalized : (pullback sectionMorphism).map directIso.hom ≫
      thirdTrivialization.hom = firstTrivialization.hom) :
    firstIso ≪≫ secondIso = directIso := by
  apply Iso.ext
  apply eq_of_pullback_map_eq projection sectionMorphism sectionCondition surjective
  apply (cancel_mono thirdTrivialization.hom).mp
  change (pullback sectionMorphism).map (firstIso.hom ≫ secondIso.hom) ≫
      thirdTrivialization.hom = (pullback sectionMorphism).map directIso.hom ≫ thirdTrivialization.hom
  rw [Functor.map_comp, Category.assoc, secondNormalized, firstNormalized, directNormalized]

/-- The pushforward structure-module isomorphism supplies rigidity of section-compatible maps. -/
theorem existsUnique_iso_of_isIso_pushforwardUnitMap (projection : source ⟶ base)
    (sectionMorphism : base ⟶ source) (sectionCondition : sectionMorphism ≫ projection = 𝟙 base)
    [IsIso (pushforwardUnitMap projection)]
    {moduleSheaf targetSheaf : source.Modules} [moduleSheaf.IsInvertible]
    (sourceTrivialization : (pullback sectionMorphism).obj moduleSheaf ≅
      SheafOfModules.unit base.ringCatSheaf)
    (targetTrivialization : (pullback sectionMorphism).obj targetSheaf ≅
      SheafOfModules.unit base.ringCatSheaf)
    (isomorphism : moduleSheaf ≅ targetSheaf) :
    ∃! normalizedIso : moduleSheaf ≅ targetSheaf,
      (pullback sectionMorphism).map normalizedIso.hom ≫ targetTrivialization.hom =
        sourceTrivialization.hom :=
  existsUnique_iso_of_pullback_trivializations projection sectionMorphism sectionCondition
    (surjective_appTop_of_isIso_pushforwardUnitMap projection)
    sourceTrivialization targetTrivialization isomorphism

end AlgebraicGeometry.Scheme.Modules
