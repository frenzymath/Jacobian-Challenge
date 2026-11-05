import Jacobian.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverDescent
import Jacobian.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverImmersion
import Jacobian.AlgebraicGeometry.ProjectiveSpace.AffineStandardOpenCover
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Spreading
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Field descent of projective immersions

If a field extension admits a projective immersion of the base-changed
scheme, the original scheme also admits one with finitely many coordinates.
-/

set_option backward.isDefEq.respectTransparency false

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section
universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {baseField extensionField : Type schemeUniverse} [Field baseField] [Field extensionField] [Algebra baseField extensionField]

theorem exists_isImmersion_projectiveSpace_of_pullback {scheme : Scheme.{schemeUniverse}} (function : scheme ⟶ Spec (.of baseField))
    {coordinateIndex : Type schemeUniverse} [Finite coordinateIndex]
    (secondIndex : pullback function (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) ⟶ ℙ(coordinateIndex; Spec (.of extensionField)))
    [IsImmersion secondIndex] (hj : secondIndex ≫ ℙ(coordinateIndex; Spec (.of extensionField)) ↘ Spec (.of extensionField) = pullback.snd _ _) :
    ∃ (newIndex : Type schemeUniverse) (_ : Finite newIndex) (index : scheme ⟶ ℙ(newIndex; Spec (.of baseField))),
      IsImmersion index ∧ index ≫ ℙ(newIndex; Spec (.of baseField)) ↘ Spec (.of baseField) = function := by
  let ringMap := Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))
  have hsurj : Surjective ringMap := surjective_specMap_algebraMap_of_field
  have hflat : Flat ringMap := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective (pullback.fst function ringMap) :=
    MorphismProperty.pullback_fst (P := @Surjective) _ _ hsurj
  have : IsAffineHom (pullback.fst function ringMap) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance

  have : IsLocallyNoetherian ℙ(coordinateIndex; Spec (.of extensionField)) :=
    LocallyOfFiniteType.isLocallyNoetherian (ℙ(coordinateIndex; Spec (.of extensionField)) ↘ Spec (.of extensionField))
  have : QuasiCompact secondIndex := by
    rw [← secondIndex.liftCoborder_ι]
    infer_instance
  have : CompactSpace ℙ(coordinateIndex; Spec (.of extensionField)) :=
    QuasiCompact.compactSpace_of_compactSpace (ℙ(coordinateIndex; Spec (.of extensionField)) ↘ Spec (.of extensionField))
  have : CompactSpace ↥(pullback function ringMap) := QuasiCompact.compactSpace_of_compactSpace secondIndex
  have : QuasiSeparatedSpace ↥(pullback function ringMap) := quasiSeparatedSpace_of_quasiSeparated secondIndex
  have : CompactSpace scheme := (pullback.fst function ringMap).surjective.compactSpace (pullback.fst function ringMap).continuous
  have : QuasiSeparatedSpace scheme := quasiSeparatedSpace_of_surjective (pullback.fst function ringMap)
  have : LocallyOfFiniteType (pullback.snd function ringMap) := by
    rw [← hj]
    infer_instance
  have : LocallyOfFiniteType function :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (IsPullback.of_hasPullback function ringMap).flip
      ⟨⟨hsurj, hflat⟩, inferInstance⟩ inferInstance

  obtain ⟨homogeneousIndex, hγ, ψ, hψo, hψ⟩ := exists_isAffineOpen_preimage_of_isImmersion secondIndex
  obtain ⟨k', _, _, _, source, projection, extensionStructure, pullbackSquare, ψ', hψ'⟩ :=
    exists_finite_isAffineOpen_preimage_standardOpen function ψ (hψo.trans hj) hψ

  obtain ⟨coverIndex, hι, coordinates, h𝒟⟩ := exists_coordinateCover_of_isPullback pullbackSquare ψ' hψ'
  exact coordinates.exists_isImmersion function h𝒟

end AlgebraicGeometry
