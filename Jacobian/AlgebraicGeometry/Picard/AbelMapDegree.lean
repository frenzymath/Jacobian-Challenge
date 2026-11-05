import Jacobian.AlgebraicGeometry.Curve.DivisorDegree
import Jacobian.AlgebraicGeometry.IdealSheaf.FiniteFlat
import Jacobian.AlgebraicGeometry.Picard.AbelMap
import Jacobian.AlgebraicGeometry.Picard.DegreeBaseChange

/-!
# The degree of the Abel map

A finite flat divisor of rank `d` on a smooth proper geometrically
irreducible curve defines a line bundle of fibrewise degree `d`. Thus the
Abel map takes values in the degree-`d` part of the Picard functor.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
  (structureMap : source ⟶ Spec (.of baseField))
  [IsProper structureMap] [SmoothOfRelativeDimension 1 structureMap]
  [GeometricallyIrreducible structureMap]

/-- The Abel class of a finite flat divisor of rank `degree` has that
constant fibrewise degree. -/
theorem abelClass_mem {degree : ℕ} {parameter : Over (Spec (.of baseField))}
    (divisor : (hilbertPresheaf structureMap degree).obj (.op parameter)) :
    abelClass structureMap divisor ∈
      (picardSubfunctorDegree structureMap degree).obj (.op parameter) := by
  have : Smooth structureMap := SmoothOfRelativeDimension.smooth 1 structureMap
  have := smoothOfRelativeDimension_isStableUnderBaseChange 1
  refine (mem_picardSubfunctorDegree_iff structureMap _ degree).mpr fun point ↦ ?_
  let projection := pullback.snd structureMap parameter.hom
  let field := parameter.left.residueField point
  letI := projection.fiberOverSpecResidueField point
  have : SmoothOfRelativeDimension 1 projection :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ ‹_›
  have : IsProper projection := MorphismProperty.pullback_snd (P := @IsProper) _ _ ‹_›
  have : GeometricallyIrreducible projection :=
    MorphismProperty.pullback_snd (P := @GeometricallyIrreducible) _ _ ‹_›
  have : SmoothOfRelativeDimension 1 (projection.fiber point ↘ Spec field) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ ‹_›
  have : IsProper (projection.fiber point ↘ Spec field) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ ‹_›
  have : GeometricallyIrreducible (projection.fiber point ↘ Spec field) :=
    MorphismProperty.pullback_snd (P := @GeometricallyIrreducible) _ _ ‹_›
  obtain ⟨finite, flat, _, rank⟩ := divisor.2
  have regular := divisor.2.isInvertible
  have pulledRegular : (divisor.1.comap (projection.fiberι point)).IsInvertible :=
    (IdealSheafData.IsRelativeEffectiveCartier.isRelativeEffectiveCartier_comap_of_isPullback
      ⟨regular, flat⟩
      (IsPullback.of_hasPullback projection (parameter.left.fromSpecResidueField point))).1
  obtain ⟨comparison⟩ := regular.nonempty_pullback_dual_toModules_iso
    (projection.fiberι point) pulledRegular
  have : IsFinite ((divisor.1.comap (projection.fiberι point)).subschemeι ≫
      (projection.fiber point ↘ Spec field)) :=
    MorphismProperty.of_isPullback (P := @IsFinite)
      ((divisor.1.isPullback_comap (projection.fiberι point)).flip.paste_vert
        (.of_hasPullback projection _)) finite
  rw [picardPresheafDegree_eq_degree, Modules.degree_congr field
    ((Modules.pullback _).mapIso (abelClassIso structureMap divisor) ≪≫ comparison),
    pulledRegular.degree_dual_toModules]
  exact_mod_cast ((Scheme.IdealSheafData.finrank_subschemeι_comp_eq_finrankΓ
    projection divisor.1 point).symm.trans (rank point))

/-- The Abel map with values in the degree-`degree` Picard presheaf. -/
def abelMapPresheaf (degree : ℕ) :
    hilbertPresheaf structureMap degree ⋙ uliftFunctor.{u + 1, u} ⟶
      (picardSubfunctorDegree structureMap degree).toFunctor where
  app parameter := TypeCat.ofHom fun divisor ↦
    ⟨abelClass structureMap divisor.down, abelClass_mem structureMap divisor.down⟩
  naturality {parameter parameter'} restriction := by
    ext divisor
    exact Subtype.ext (pic_map_abelClass structureMap restriction.unop divisor.down).symm

/-- The Abel map to the degree-`degree` part of the fppf Picard sheaf. -/
def abelMapDegree (degree : ℕ) :
    hilbertPresheaf structureMap degree ⋙ uliftFunctor.{u + 1, u} ⟶
      (picardFunctorDegree structureMap degree).obj :=
  abelMapPresheaf structureMap degree ≫
    toSheafify (fppfTopology.over (Spec (.of baseField)))
      (picardSubfunctorDegree structureMap degree).toFunctor

/-- Forgetting the degree part recovers the usual Abel map. -/
theorem abelMapDegree_comp_ι (degree : ℕ) :
    abelMapDegree structureMap degree ≫ (picardFunctorDegreeι structureMap degree).hom =
      hilbertToPicard structureMap degree := by
  ext parameter divisor
  exact picardFunctorDegreeι_app_toSheafify structureMap degree
    ⟨abelClass structureMap divisor.down, abelClass_mem structureMap divisor.down⟩

end AlgebraicGeometry
