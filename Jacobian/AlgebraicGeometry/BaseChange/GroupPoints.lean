import Jacobian.AlgebraicGeometry.BaseChange.Field
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-!
# Group-valued points and field extension

The restriction-pullback adjunction identifies the group of points of a
base-changed commutative group scheme with its group of points on the
restricted parameter scheme. Multiplication is checked using the actual
pullback tensorator, not by assuming restriction preserves terminal objects.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {baseField extensionField : Type u} [Field baseField] [Field extensionField]
  [Algebra baseField extensionField]

private abbrev fieldMap : Spec (.of extensionField) ⟶ Spec (.of baseField) :=
  Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))

private abbrev restrictedPoint {parameter : Over (Spec (.of extensionField))}
    {scheme : Over (Spec (.of baseField))}
    (point : parameter ⟶ (baseChange baseField extensionField).obj scheme) :
    (Over.map (fieldMap (baseField := baseField) (extensionField := extensionField))).obj
      parameter ⟶ scheme :=
  ((Over.mapPullbackAdj fieldMap).homEquiv _ _).symm point

@[simp]
private theorem restrictedPoint_left {parameter : Over (Spec (.of extensionField))}
    {scheme : Over (Spec (.of baseField))}
    (point : parameter ⟶ (baseChange baseField extensionField).obj scheme) :
    (restrictedPoint point).left = point.left ≫ pullback.fst scheme.hom fieldMap :=
  rfl

private theorem restrictedPoint_pair
    (group : CommGrp (Over (Spec (.of baseField))))
    (parameter : Over (Spec (.of extensionField)))
    (firstPoint secondPoint : parameter ⟶ (baseChange baseField extensionField).obj group.X) :
    (lift firstPoint secondPoint).left ≫
        (Functor.LaxMonoidal.μ (baseChange baseField extensionField) group.X group.X).left ≫
        pullback.fst (group.X ⊗ group.X).hom fieldMap =
      (lift (restrictedPoint firstPoint) (restrictedPoint secondPoint)).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.μ_pullback_left_fst_fst,
      Over.lift_left, pullback.lift_fst_assoc, pullback.lift_fst,
      restrictedPoint_left]
  · simp only [Category.assoc, Over.μ_pullback_left_fst_snd,
      Over.lift_left, pullback.lift_snd_assoc, pullback.lift_snd,
      restrictedPoint_left]

/-- The actual restriction-pullback correspondence is multiplicative on group-scheme points. -/
def baseChangeHomMulEquiv
    (group : CommGrp (Over (Spec (.of baseField))))
    (parameter : Over (Spec (.of extensionField))) :
    (parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj group).X) ≃*
      ((Over.map (Spec.map (CommRingCat.ofHom
        (algebraMap baseField extensionField)))).obj parameter ⟶ group.X) :=
  { ((Over.mapPullbackAdj fieldMap).homEquiv parameter group.X).symm with
    map_mul' := fun firstPoint secondPoint ↦ by
      ext
      change ((lift firstPoint secondPoint ≫
        (Functor.LaxMonoidal.μ (baseChange baseField extensionField) group.X group.X ≫
          (baseChange baseField extensionField).map μ[group.X])).left ≫
          pullback.fst group.X.hom fieldMap) =
        (lift (restrictedPoint firstPoint) (restrictedPoint secondPoint) ≫ μ[group.X]).left
      simp only [Over.comp_left, Category.assoc, Over.pullback_map_left,
        pullback.lift_fst, pullback.lift_fst_assoc]
      simpa only [Category.assoc] using congrArg
        (fun morphism ↦ morphism ≫ (μ[group.X]).left)
        (restrictedPoint_pair group parameter firstPoint secondPoint) }

/-- The adjoint point is the original point followed by the first pullback projection. -/
@[simp]
theorem baseChangeHomMulEquiv_apply_left
    (group : CommGrp (Over (Spec (.of baseField))))
    (parameter : Over (Spec (.of extensionField)))
    (point : parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj group).X) :
    (baseChangeHomMulEquiv group parameter point).left =
      point.left ≫ pullback.fst group.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) :=
  rfl

/-- Restricting a test scheme commutes with the multiplicative adjunction. -/
theorem baseChangeHomMulEquiv_naturality_left
    (group : CommGrp (Over (Spec (.of baseField))))
    {parameter cover : Over (Spec (.of extensionField))} (restriction : cover ⟶ parameter)
    (point : parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj group).X) :
    baseChangeHomMulEquiv group cover (restriction ≫ point) =
      (Over.map (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))).map
          restriction ≫ baseChangeHomMulEquiv group parameter point :=
  (Over.mapPullbackAdj fieldMap).homEquiv_naturality_left_symm restriction point

/-- The multiplicative adjunction is natural in the supplied commutative group. -/
theorem baseChangeHomMulEquiv_postcomp
    {sourceGroup targetGroup : CommGrp (Over (Spec (.of baseField)))}
    (groupMap : sourceGroup ⟶ targetGroup)
    (parameter : Over (Spec (.of extensionField)))
    (point : parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj sourceGroup).X) :
    baseChangeHomMulEquiv targetGroup parameter
        (point ≫ ((baseChange baseField extensionField).mapCommGrp.map groupMap).hom.hom.hom) =
      baseChangeHomMulEquiv sourceGroup parameter point ≫ groupMap.hom.hom.hom :=
  (Over.mapPullbackAdj fieldMap).homEquiv_naturality_right_symm point groupMap.hom.hom.hom

/-- The multiplicative adjunction agrees with the prescribed identity comparison. -/
theorem baseChangeHomMulEquiv_id
    {baseField : Type u} [Field baseField]
    (group : CommGrp (Over (Spec (.of baseField))))
    (parameter : Over (Spec (.of baseField)))
    (point : parameter ⟶ ((baseChange baseField baseField).mapCommGrp.obj group).X) :
    point ≫ ((baseChange.idIso baseField).app group.X).hom =
      baseChange.restrictionId baseField parameter ≫
        baseChangeHomMulEquiv group parameter point := by
  ext
  change point.left ≫ (((baseChange.idIso baseField).app group.X).hom).left =
    𝟙 parameter.left ≫ (point.left ≫ pullback.fst group.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap baseField baseField))))
  exact (congrArg (fun morphism ↦ point.left ≫ morphism)
    (baseChange.idIso_hom_app_left baseField group.X)).trans (Category.id_comp _).symm

/-- The multiplicative adjunction respects the prescribed scalar-tower comparison. -/
theorem baseChangeHomMulEquiv_comp
    (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField] [IsScalarTower baseField middleField extensionField]
    (group : CommGrp (Over (Spec (.of baseField))))
    (parameter : Over (Spec (.of extensionField)))
    (point : parameter ⟶ ((baseChange baseField extensionField).mapCommGrp.obj group).X) :
    baseChangeHomMulEquiv (extensionField := middleField) group
        ((Over.map (Spec.map (CommRingCat.ofHom
          (algebraMap middleField extensionField)))).obj parameter)
        (baseChangeHomMulEquiv (extensionField := extensionField)
          ((baseChange baseField middleField).mapCommGrp.obj group) parameter
          (point ≫ ((baseChange.compIso baseField middleField extensionField).app group.X).hom)) =
      baseChange.restrictionComp baseField middleField extensionField parameter ≫
        baseChangeHomMulEquiv group parameter point := by
  ext
  change ((point.left ≫
    (((baseChange.compIso baseField middleField extensionField).app group.X).hom).left) ≫
      pullback.fst (pullback.snd group.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap baseField middleField))))
        (Spec.map (CommRingCat.ofHom (algebraMap middleField extensionField)))) ≫
      pullback.fst group.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap baseField middleField))) =
    𝟙 parameter.left ≫ (point.left ≫ pullback.fst group.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))
  simp only [Category.assoc, baseChange.compIso_hom_app_left_fst_fst, Category.id_comp]

end AlgebraicGeometry
