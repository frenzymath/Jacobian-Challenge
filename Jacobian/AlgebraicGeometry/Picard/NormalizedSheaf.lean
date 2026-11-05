import Jacobian.AlgebraicGeometry.Picard.LocalTriviality
import Jacobian.AlgebraicGeometry.Picard.Normalized
import Jacobian.AlgebraicGeometry.Picard.Sheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Sheafification of normalized Picard classes

The inclusion of classes normalized along a section is locally bijective for
the fppf topology: the pullback to the section can be trivialized on a Zariski
cover of the parameter scheme. Its sheafification is therefore the relative
Picard functor, without any hypothesis on the family beyond the section.

The map from the normalized presheaf itself is an isomorphism precisely when
that presheaf satisfies fppf descent. Under this explicit descent hypothesis,
the normalized presheaf and the Picard sheaf have the same representability.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {source base : Scheme.{schemeUniverse}}

/-- Every relative Picard class is locally normalized along the section. -/
instance isLocallySurjective_picardFunctorNormalized_ι (morphism : source ⟶ base)
    (sectionMorphism : base ⟶ source) (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) :
    Presheaf.IsLocallySurjective (fppfTopology.over base)
      (picardFunctorNormalized morphism sectionMorphism sectionCondition).ι where
  imageSieve_mem {parameter} picardClass := by
    choose cover membership trivializations using fun point : parameter.left ↦
      Pic.exists_map_iota_eq_one
        (Pic.map (sectionBaseChange morphism sectionMorphism sectionCondition parameter) picardClass)
        point
    rw [GrothendieckTopology.mem_over_iff]
    refine fppfTopology.superset_covering ?_ (Precoverage.generate_mem_toGrothendieck
      (R := Presieve.ofArrows (fun point ↦ (cover point).toScheme) (fun point ↦ (cover point).ι)) ?_)
    · rw [Sieve.generate_le_iff]
      rintro _ _ ⟨point⟩
      rw [Sieve.overEquiv_iff]
      let restriction : Over.mk ((cover point).ι ≫ parameter.hom) ⟶ parameter :=
        Over.homMk (cover point).ι
      refine ⟨⟨Pic.map (baseChangeMap morphism restriction) picardClass, ?_⟩, rfl⟩
      exact (Pic.map_comp _ _ picardClass).symm.trans
        ((congrArg (fun sectionMap ↦ Pic.map sectionMap picardClass)
          (sectionBaseChange_comp_baseChangeMap morphism sectionMorphism sectionCondition restriction)).trans
            ((Pic.map_comp _ _ picardClass).trans (trivializations point)))
    · rw [fppfPrecoverage, ofArrows_mem_precoverage_iff]
      exact ⟨fun point ↦ ⟨point, ⟨point, membership point⟩, rfl⟩,
        fun point ↦ ⟨inferInstance, inferInstance⟩⟩

/-- Normalized classes form a subpresheaf, so their inclusion is locally injective. -/
instance isLocallyInjective_picardFunctorNormalized_ι (morphism : source ⟶ base)
    (sectionMorphism : base ⟶ source) (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) :
    Presheaf.IsLocallyInjective (fppfTopology.over base)
      (picardFunctorNormalized morphism sectionMorphism sectionCondition).ι :=
  Presheaf.isLocallyInjective_of_injective _ _ fun _ ↦ Subtype.val_injective

/-- The inclusion of normalized classes becomes an isomorphism after fppf sheafification. -/
instance isIso_presheafToSheaf_map_picardFunctorNormalized_ι (morphism : source ⟶ base)
    (sectionMorphism : base ⟶ source) (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) :
    IsIso ((presheafToSheaf (fppfTopology.over base) (Type (schemeUniverse + 1))).map
      (picardFunctorNormalized morphism sectionMorphism sectionCondition).ι) :=
  ((fppfTopology.over base).W_iff _).mp
    ((fppfTopology.over base).W_of_isLocallyBijective _)

/-- The relative Picard functor is the fppf sheafification of the normalized classes. -/
def sheafifyPicardFunctorNormalizedIso (morphism : source ⟶ base)
    (sectionMorphism : base ⟶ source) (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) :
    (presheafToSheaf (fppfTopology.over base) (Type (schemeUniverse + 1))).obj
        (picardFunctorNormalized morphism sectionMorphism sectionCondition).toFunctor ≅
      picardFunctor morphism :=
  asIso ((presheafToSheaf (fppfTopology.over base) (Type (schemeUniverse + 1))).map
    (picardFunctorNormalized morphism sectionMorphism sectionCondition).ι)

/-- The comparison between sheafifications is induced by inclusion of normalized classes. -/
lemma toSheafify_comp_sheafifyPicardFunctorNormalizedIso_hom (morphism : source ⟶ base)
    (sectionMorphism : base ⟶ source) (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) :
    toSheafify (fppfTopology.over base)
        (picardFunctorNormalized morphism sectionMorphism sectionCondition).toFunctor ≫
      (sheafifyPicardFunctorNormalizedIso morphism sectionMorphism sectionCondition).hom.hom =
        (picardFunctorNormalized morphism sectionMorphism sectionCondition).ι ≫
          toPicardFunctor morphism :=
  (toSheafify_naturality _ _).symm

/-- The normalized presheaf maps isomorphically to the Picard sheaf exactly when it is a sheaf. -/
theorem isIso_picardFunctorNormalized_ι_comp_toPicardFunctor_iff (morphism : source ⟶ base)
    (sectionMorphism : base ⟶ source) (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) :
    IsIso ((picardFunctorNormalized morphism sectionMorphism sectionCondition).ι ≫
        toPicardFunctor morphism) ↔
      Presheaf.IsSheaf (fppfTopology.over base)
        (picardFunctorNormalized morphism sectionMorphism sectionCondition).toFunctor := by
  constructor
  · intro isomorphism
    letI := isomorphism
    exact (Presheaf.isSheaf_of_iso_iff (asIso
      ((picardFunctorNormalized morphism sectionMorphism sectionCondition).ι ≫
        toPicardFunctor morphism))).mpr (picardFunctor morphism).property
  · intro sheafCondition
    letI := isIso_toSheafify (fppfTopology.over base) sheafCondition
    rw [← toSheafify_comp_sheafifyPicardFunctorNormalizedIso_hom]
    infer_instance

/-- Under fppf descent, normalized classes and the Picard sheaf have the same representability. -/
theorem isRepresentable_picardFunctorNormalized_iff_of_isSheaf (morphism : source ⟶ base)
    (sectionMorphism : base ⟶ source) (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base)
    (sheafCondition : Presheaf.IsSheaf (fppfTopology.over base)
      (picardFunctorNormalized morphism sectionMorphism sectionCondition).toFunctor) :
    (picardFunctorNormalized morphism sectionMorphism sectionCondition).toFunctor.IsRepresentable ↔
      (picardFunctor morphism).obj.IsRepresentable := by
  letI := (isIso_picardFunctorNormalized_ι_comp_toPicardFunctor_iff morphism
    sectionMorphism sectionCondition).mpr sheafCondition
  let comparison := asIso ((picardFunctorNormalized morphism sectionMorphism sectionCondition).ι ≫
    toPicardFunctor morphism)
  exact ⟨fun _ ↦ isRepresentable_of_natIso _ comparison,
    fun _ ↦ isRepresentable_of_natIso _ comparison.symm⟩

end AlgebraicGeometry
