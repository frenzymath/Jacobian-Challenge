import Jacobian.AlgebraicGeometry.Picard.RationalPoint
import Jacobian.AlgebraicGeometry.Picard.BaseChange
import Jacobian.AlgebraicGeometry.Sites.Fpqc
import Jacobian.CategoryTheory.Comma.Over.DescentRepresentable
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Fpqc descent for relative Picard sheaves

The relative Picard sheaf of a proper geometrically integral scheme over a field
is an fpqc sheaf, even when the scheme has no rational point. A closed point
gives a finite field extension with a rational point. Picard base change and
transitivity of the sheaf condition descend fpqc sheafhood along the resulting
fppf cover of the ground field.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe valueUniverse schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

private theorem isSheaf_fpqc_of_fppf_of_overMap {base extension : Scheme.{schemeUniverse}}
    (baseMap : extension ⟶ base) [Flat baseMap] [Surjective baseMap]
    [LocallyOfFinitePresentation baseMap] {presheaf : (Over base)ᵒᵖ ⥤ Type valueUniverse}
    (originalSheaf : Presheaf.IsSheaf (fppfTopology.over base) presheaf)
    (restrictedSheaf : Presheaf.IsSheaf (fpqcTopology.over extension)
      ((Over.map baseMap).op ⋙ presheaf)) :
    Presheaf.IsSheaf (fpqcTopology.over base) presheaf := by
  have originalSheaf := (isSheaf_iff_isSheaf_of_type _ _).mp originalSheaf
  rw [isSheaf_iff_isSheaf_of_type]
  intro parameter sieve covering
  let projection := Functor.RepresentableBy.descentCoverπ baseMap parameter
  have : Flat projection.left := inferInstanceAs (Flat (pullback.fst _ _))
  have : Surjective projection.left := inferInstanceAs (Surjective (pullback.fst _ _))
  have : LocallyOfFinitePresentation projection.left :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst _ _))
  have projectionCovering := singleton_mem_over_fppfTopology projection
  refine Presieve.isSheafFor_trans presheaf _ sieve
    (originalSheaf _ projectionCovering) (fun test restriction _ ↦
      (originalSheaf _ (GrothendieckTopology.pullback_stable _ restriction
        projectionCovering)).isSeparatedFor) ?_
  intro test restriction membership
  obtain ⟨intermediate, factor, _, ⟨⟩, rfl⟩ := membership
  exact isSheafFor_of_isSheaf_overMap baseMap restrictedSheaf _
    (GrothendieckTopology.pullback_stable _ (factor ≫ projection) covering)
    (factor.left ≫ pullback.snd parameter.hom baseMap)
    (by rw [Category.assoc, ← Over.w factor]; rfl)

private theorem isSheaf_fpqc_picardFunctor_overMap
    {baseField extensionField : Type schemeUniverse} [Field baseField] [Field extensionField]
    {source : Scheme.{schemeUniverse}} [source.Over (Spec (.of baseField))]
    [IsProper (source ↘ Spec (.of baseField))]
    [GeometricallyIntegral (source ↘ Spec (.of baseField))]
    (baseMap : Spec (.of extensionField) ⟶ Spec (.of baseField))
    (point : Spec (.of extensionField) ⟶ source)
    (pointCondition : point ≫ source ↘ Spec (.of baseField) = baseMap) :
    Presheaf.IsSheaf (fpqcTopology.over (Spec (.of extensionField)))
      ((Over.map baseMap).op ⋙ (picardFunctor (source ↘ Spec (.of baseField))).obj) := by
  let structureMap := source ↘ Spec (.of baseField)
  let : (pullback structureMap baseMap).Over (Spec (.of extensionField)) :=
    ⟨pullback.snd structureMap baseMap⟩
  have : IsProper (pullback structureMap baseMap ↘ Spec (.of extensionField)) :=
    inferInstanceAs (IsProper (pullback.snd structureMap baseMap))
  have : GeometricallyIntegral (pullback structureMap baseMap ↘ Spec (.of extensionField)) :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd structureMap baseMap))
  let rationalPoint : Spec (.of extensionField) ⟶ pullback structureMap baseMap :=
    pullback.lift point (𝟙 _) (by rw [Category.id_comp]; exact pointCondition)
  exact (Presheaf.isSheaf_of_iso_iff
    (picardFunctorIsoOfIsPullback (IsPullback.of_hasPullback structureMap baseMap))).mpr
    (isSheaf_fpqc_picardFunctor rationalPoint (pullback.lift_snd _ _ _))

/-- The Picard fppf sheaf of a proper geometrically integral scheme over a field
satisfies descent for the fpqc topology, without a rational-point hypothesis. -/
theorem isSheaf_fpqc_picardFunctor_of_geometricallyIntegral
    {baseField : Type schemeUniverse} [Field baseField] {source : Scheme.{schemeUniverse}}
    [source.Over (Spec (.of baseField))] [IsProper (source ↘ Spec (.of baseField))]
    [GeometricallyIntegral (source ↘ Spec (.of baseField))] :
    Presheaf.IsSheaf (fpqcTopology.over (Spec (.of baseField)))
      (picardFunctor (source ↘ Spec (.of baseField))).obj := by
  let structureMap := source ↘ Spec (.of baseField)
  have : IsIntegral source := GeometricallyIntegral.isIntegral_of_subsingleton structureMap
  have : CompactSpace source := QuasiCompact.compactSpace_of_compactSpace structureMap
  obtain ⟨point, _, closedPoint⟩ := IsClosed.exists_closed_singleton
    (S := (Set.univ : Set source)) isClosed_univ Set.univ_nonempty
  have : IsClosedImmersion (source.fromSpecResidueField point) :=
    isClosed_singleton_iff_isClosedImmersion.mp closedPoint
  have : IsFinite (source.fromSpecResidueField point ≫ structureMap) := by
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  let coefficients : CommRingCat.of baseField ⟶ source.residueField point :=
    Spec.preimage (source.fromSpecResidueField point ≫ structureMap)
  let : Algebra baseField (source.residueField point) := coefficients.hom.toAlgebra
  let baseMap := Spec.map coefficients
  have baseMap_eq : baseMap = source.fromSpecResidueField point ≫ structureMap :=
    Spec.map_preimage _
  have : IsFinite baseMap := by rw [baseMap_eq]; infer_instance
  have : Flat baseMap := by
    rw [Flat.SpecMap_iff]
    change (algebraMap baseField (source.residueField point)).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective baseMap := ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have : LocallyOfFinitePresentation baseMap := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.FinitePresentation.of_finiteType.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
        (inferInstanceAs (LocallyOfFiniteType baseMap)))
  exact isSheaf_fpqc_of_fppf_of_overMap baseMap (picardFunctor structureMap).property
    (isSheaf_fpqc_picardFunctor_overMap (extensionField := source.residueField point)
      baseMap (source.fromSpecResidueField point) baseMap_eq.symm)

end AlgebraicGeometry
