import Jacobian.AlgebraicGeometry.Hilbert.CurveGeometry
import Jacobian.AlgebraicGeometry.Picard.AbelMapDegree
import Jacobian.AlgebraicGeometry.Picard.EffectiveDivisors
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# A proper Hilbert cover of the degree-genus Picard scheme

For a smooth proper geometrically irreducible curve of genus `g`, the Abel
map from the degree-`g` Hilbert scheme to any representative of the degree-`g`
Picard sheaf is surjective. Every point lifts after passing to an algebraic
closure of its residue field. The representative is therefore universally
closed and geometrically irreducible, without any closedness hypothesis on
the ground field.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
  [source.Over (Spec (.of baseField))]
  [IsProper (source ↘ Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
  [GeometricallyIrreducible (source ↘ Spec (.of baseField))]

/-- The degree-genus Hilbert scheme is a proper geometrically integral cover
of any scheme representing the degree-genus Picard sheaf. -/
theorem exists_surjective_of_representableBy_picardFunctorDegree_genus
    (representative : Over (Spec (.of baseField)))
    (representation : (picardFunctorDegree (source ↘ Spec (.of baseField))
      (source.arithmeticGenus baseField)).obj.RepresentableBy representative) :
    ∃ (cover : Over (Spec (.of baseField))) (coverMap : cover ⟶ representative),
      IsProper cover.hom ∧ GeometricallyIntegral cover.hom ∧ Surjective coverMap.left := by
  let structureMap := source ↘ Spec (.of baseField)
  have : Smooth structureMap := SmoothOfRelativeDimension.smooth 1 structureMap
  have : GeometricallyIntegral structureMap := inferInstance
  obtain ⟨hilbertScheme, projection, _, properCover, integralCover, ⟨hilbertRepresentation⟩⟩ :=
    hilbertPresheaf_curve_representable structureMap (source.arithmeticGenus baseField)
  let topology := fppfTopology.over (Spec (.of baseField))
  let degreePart := picardSubfunctorDegree structureMap (source.arithmeticGenus baseField)
  let presheafMap := abelMapPresheaf structureMap (source.arithmeticGenus baseField)
  let universalClass : (picardFunctorDegree structureMap
      (source.arithmeticGenus baseField)).obj.obj (.op (Over.mk projection)) :=
    (toSheafify topology degreePart.toFunctor).app _
      (presheafMap.app _ (ULift.up (hilbertRepresentation.homEquiv (𝟙 _))))
  let abelMorphism : Over.mk projection ⟶ representative :=
    representation.homEquiv.symm universalClass
  have classifies {parameter : Over (Spec (.of baseField))}
      (parameterMap : parameter ⟶ Over.mk projection) :
      representation.homEquiv (parameterMap ≫ abelMorphism) =
        (toSheafify topology degreePart.toFunctor).app _
          (presheafMap.app _ (ULift.up (hilbertRepresentation.homEquiv parameterMap))) := by
    rw [representation.homEquiv_comp, representation.homEquiv.apply_symm_apply]
    have universalPullback : hilbertRepresentation.homEquiv parameterMap =
        (hilbertPresheaf _ _).map parameterMap.op
          (hilbertRepresentation.homEquiv (𝟙 _)) := by
      simpa using hilbertRepresentation.homEquiv_comp parameterMap (𝟙 _)
    rw [universalPullback]
    refine (NatTrans.naturality_apply (toSheafify topology degreePart.toFunctor)
      parameterMap.op _).symm.trans ?_
    exact congrArg _ (NatTrans.naturality_apply presheafMap parameterMap.op _).symm
  refine ⟨Over.mk projection, abelMorphism, properCover, integralCover, ⟨fun point ↦ ?_⟩⟩
  let residue := representative.left.residueField point
  let residueMap : CommRingCat.of baseField ⟶ residue :=
    Spec.preimage (representative.left.fromSpecResidueField point ≫ representative.hom)
  let closure := AlgebraicClosure residue
  letI : Algebra baseField closure :=
    ((algebraMap residue closure).comp residueMap.hom).toAlgebra
  have structure_eq : Spec.map (CommRingCat.ofHom (algebraMap baseField closure)) =
      Spec.map (CommRingCat.ofHom (algebraMap residue closure)) ≫
        representative.left.fromSpecResidueField point ≫ representative.hom := by
    rw [← Spec.map_preimage
      (representative.left.fromSpecResidueField point ≫ representative.hom), ← Spec.map_comp]
    rfl
  let geometricPoint : Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap baseField closure))) ⟶ representative :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap residue closure)) ≫
      representative.left.fromSpecResidueField point)
      (by rw [Category.assoc]; exact structure_eq.symm)
  obtain ⟨lineClass, lineClass_eq⟩ := surjective_toSheafify_app_of_isAlgClosed
    degreePart.toFunctor (representation.homEquiv geometricPoint)
  obtain ⟨divisor, divisor_eq⟩ := exists_abelClass_eq closure lineClass
  let divisorPoint : Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap baseField closure))) ⟶ Over.mk projection :=
    hilbertRepresentation.homEquiv.symm divisor
  have divisorPoint_comp : divisorPoint ≫ abelMorphism = geometricPoint := by
    refine representation.homEquiv.injective ?_
    rw [classifies, ← lineClass_eq]
    refine congrArg _ (Subtype.ext ?_)
    change abelClass structureMap (hilbertRepresentation.homEquiv divisorPoint) = lineClass.1
    simpa [divisorPoint] using divisor_eq
  obtain ⟨closurePoint⟩ : Nonempty (Spec (.of closure)) := inferInstance
  refine ⟨divisorPoint.left closurePoint, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, divisorPoint_comp]
  change (representative.left.fromSpecResidueField point) _ = point
  exact Scheme.fromSpecResidueField_apply _ _

/-- A representative of the degree-genus Picard sheaf is universally closed
over the structural field. -/
theorem universallyClosed_of_representableBy_picardFunctorDegree_genus
    (representative : Over (Spec (.of baseField)))
    (representation : (picardFunctorDegree (source ↘ Spec (.of baseField))
      (source.arithmeticGenus baseField)).obj.RepresentableBy representative) :
    UniversallyClosed representative.hom := by
  obtain ⟨cover, coverMap, _, _, _⟩ :=
    exists_surjective_of_representableBy_picardFunctorDegree_genus representative representation
  have : UniversallyClosed (coverMap.left ≫ representative.hom) := by
    rw [Over.w coverMap]
    infer_instance
  exact UniversallyClosed.of_comp_surjective coverMap.left representative.hom

/-- A representative of the degree-genus Picard sheaf is geometrically
irreducible over the structural field. -/
theorem geometricallyIrreducible_of_representableBy_picardFunctorDegree_genus
    (representative : Over (Spec (.of baseField)))
    (representation : (picardFunctorDegree (source ↘ Spec (.of baseField))
      (source.arithmeticGenus baseField)).obj.RepresentableBy representative) :
    GeometricallyIrreducible representative.hom := by
  obtain ⟨cover, coverMap, _, _, _⟩ :=
    exists_surjective_of_representableBy_picardFunctorDegree_genus representative representation
  have : GeometricallyIrreducible (coverMap.left ≫ representative.hom) := by
    rw [Over.w coverMap]
    infer_instance
  exact GeometricallyIrreducible.of_surjective coverMap.left representative.hom

end AlgebraicGeometry
