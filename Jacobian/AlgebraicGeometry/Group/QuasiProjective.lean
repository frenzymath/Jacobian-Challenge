import Jacobian.AlgebraicGeometry.Group.AmpleFamily
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Embedding
import Jacobian.AlgebraicGeometry.ProjectiveSpace.FieldDescent
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Projective immersions of smooth geometrically integral groups

Over an algebraically closed field the group has an ample family. Its resulting
projective immersion descends through the extension of the ground field.
-/

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

private theorem exists_projective_immersion_of_algebraically_closed
    {baseField : Type schemeUniverse} [Field baseField] [IsAlgClosed baseField]
    (group : Over (Spec (.of baseField))) [GrpObj group]
    [Smooth group.hom] [QuasiCompact group.hom] [IrreducibleSpace group.left]
    [IsSeparated group.hom] :
    ∃ (coordinateIndex : Type schemeUniverse) (_ : Finite coordinateIndex)
      (immersion : group.left ⟶ ℙ(coordinateIndex; Spec (.of baseField))),
      IsImmersion immersion ∧ immersion ≫ ℙ(coordinateIndex; Spec (.of baseField)) ↘
        Spec (.of baseField) = group.hom := by
  obtain ⟨lineBundle, invertible, indexType, finite, sections, affine, cover⟩ :=
    GrpObj.hasAmpleFamily_of_smooth_of_irreducibleSpace group
  letI := invertible
  letI := finite
  exact exists_isImmersion_projectiveSpace_of_isAffineOpen group.hom lineBundle sections affine cover

/-- A smooth geometrically integral quasi-compact separated group over a field
admits an immersion into a projective space with finitely many coordinates. -/
theorem GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral
    {baseField : Type schemeUniverse} [Field baseField]
    (group : Over (Spec (.of baseField))) [GrpObj group]
    [Smooth group.hom] [GeometricallyIntegral group.hom]
    [QuasiCompact group.hom] [IsSeparated group.hom] :
    ∃ (coordinateIndex : Type schemeUniverse) (_ : Finite coordinateIndex)
      (immersion : group.left ⟶ ℙ(coordinateIndex; Spec (.of baseField))),
      IsImmersion immersion ∧ immersion ≫ ℙ(coordinateIndex; Spec (.of baseField)) ↘
        Spec (.of baseField) = group.hom := by
  let extensionMap : Spec (.of (AlgebraicClosure baseField)) ⟶ Spec (.of baseField) :=
    Spec.map (CommRingCat.ofHom (algebraMap baseField (AlgebraicClosure baseField)))
  letI : GrpObj (Over.mk group.hom) := inferInstanceAs (GrpObj group)
  letI : GrpObj (Over.mk (pullback.snd group.hom extensionMap)) := Over.grpObjMkPullbackSnd
  have : Smooth (Over.mk (pullback.snd group.hom extensionMap)).hom :=
    inferInstanceAs (Smooth (pullback.snd group.hom extensionMap))
  have : QuasiCompact (Over.mk (pullback.snd group.hom extensionMap)).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd group.hom extensionMap))
  have : IrreducibleSpace (Over.mk (pullback.snd group.hom extensionMap)).left :=
    inferInstanceAs (IrreducibleSpace ↥(Limits.pullback group.hom extensionMap))
  obtain ⟨coordinateIndex, finite, immersion, isImmersion, over⟩ :=
    exists_projective_immersion_of_algebraically_closed
      (Over.mk (pullback.snd group.hom extensionMap))
  letI := finite
  letI := isImmersion
  exact exists_isImmersion_projectiveSpace_of_pullback group.hom immersion over

end AlgebraicGeometry
