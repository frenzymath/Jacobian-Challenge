import Jacobian.AlgebraicGeometry.Curve.PullbackDegree
import Jacobian.AlgebraicGeometry.Picard.DegreeBaseChange
import Jacobian.AlgebraicGeometry.Picard.Functorial

/-!
# Fibrewise degree-zero pullback on curves

A residue-field fibre of a constant smooth proper geometrically irreducible
curve family is again such a curve. A morphism of curves induces a morphism
between these literal fibres, and restriction of module sheaves commutes with
its pullback. Pointwise degree-zero preservation therefore applies over every
parameter scheme and preserves the degree-zero Picard subfunctor.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Curve

variable {baseField : Type u} [Field baseField]

/-- The literal residue-field fibre of a curve family is a base change of the curve. -/
theorem residueFiber_isPullback (curve : Curve baseField)
    (parameter : Over (Spec (.of baseField))) (point : parameter.left) :
    IsPullback
      ((pullback.snd curve.carrier.hom parameter.hom).fiberι point ≫
        pullback.fst curve.carrier.hom parameter.hom)
      ((pullback.snd curve.carrier.hom parameter.hom).fiberToSpecResidueField point)
      curve.carrier.hom (parameter.left.fromSpecResidueField point ≫ parameter.hom) :=
  (IsPullback.of_hasPullback _ _).paste_horiz
    (IsPullback.of_hasPullback curve.carrier.hom parameter.hom)

/-- A residue-field fibre of a curve family, with its inherited curve geometry. -/
def residueFiber (curve : Curve baseField) (parameter : Over (Spec (.of baseField)))
    (point : parameter.left) : Curve (parameter.left.residueField point) where
  carrier := Over.mk
    ((pullback.snd curve.carrier.hom parameter.hom).fiberToSpecResidueField point)
  isProper := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsProper) (residueFiber_isPullback curve parameter point) inferInstance
  smoothOfRelativeDimension := by
    letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @SmoothOfRelativeDimension 1)
      (residueFiber_isPullback curve parameter point) inferInstance
  geometricallyIrreducible := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @GeometricallyIrreducible) (residueFiber_isPullback curve parameter point)
    inferInstance

variable (source target : Curve baseField) (morphism : source ⟶ target)

/-- The morphism induced on the literal residue-field fibres of two curve families. -/
def mapResidueFiber (parameter : Over (Spec (.of baseField))) (point : parameter.left) :
    residueFiber source parameter point ⟶ residueFiber target parameter point :=
  Over.homMk (pullback.lift
    ((pullback.snd source.carrier.hom parameter.hom).fiberι point ≫
      picardFamilyMap morphism parameter)
    ((pullback.snd source.carrier.hom parameter.hom).fiberToSpecResidueField point) (by
      simp only [picardFamilyMap, Category.assoc, pullback.lift_snd]
      exact pullback.condition)) (by
        exact pullback.lift_snd _ _ _)

/-- The induced fibre morphism commutes with the inclusions into the curve families. -/
@[reassoc (attr := simp)]
theorem mapResidueFiber_ι (parameter : Over (Spec (.of baseField)))
    (point : parameter.left) :
    (mapResidueFiber source target morphism parameter point).left ≫
        (pullback.snd target.carrier.hom parameter.hom).fiberι point =
      (pullback.snd source.carrier.hom parameter.hom).fiberι point ≫
        picardFamilyMap morphism parameter := by
  exact pullback.lift_fst _ _ _

/-- Restricting a pulled-back module to a fibre agrees with pullback on that fibre. -/
def mapResidueFiberModuleIso (parameter : Over (Spec (.of baseField)))
    (point : parameter.left)
    (moduleSheaf : (pullback target.carrier.hom parameter.hom).Modules) :
    (Scheme.Modules.pullback
        ((pullback.snd source.carrier.hom parameter.hom).fiberι point)).obj
      ((Scheme.Modules.pullback (picardFamilyMap morphism parameter)).obj moduleSheaf) ≅
    (Scheme.Modules.pullback
        (mapResidueFiber source target morphism parameter point).left).obj
      ((Scheme.Modules.pullback
        ((pullback.snd target.carrier.hom parameter.hom).fiberι point)).obj moduleSheaf) :=
  (Scheme.Modules.pullbackComp _ _).app moduleSheaf ≪≫
    (Scheme.Modules.pullbackCongr
      (mapResidueFiber_ι source target morphism parameter point).symm).app moduleSheaf ≪≫
    ((Scheme.Modules.pullbackComp _ _).app moduleSheaf).symm

/-- Pullback preserves degree zero on every residue-field fibre of a curve family. -/
theorem degree_pullback_fiber_eq_zero (parameter : Over (Spec (.of baseField)))
    (point : parameter.left)
    (lineBundle : (pullback target.carrier.hom parameter.hom).Modules)
    [lineBundle.IsInvertible]
    (zeroDegree :
      letI := (pullback.snd target.carrier.hom parameter.hom).fiberOverSpecResidueField point
      ((Scheme.Modules.pullback
        ((pullback.snd target.carrier.hom parameter.hom).fiberι point)).obj lineBundle).degree
        (parameter.left.residueField point) = 0) :
    letI := (pullback.snd source.carrier.hom parameter.hom).fiberOverSpecResidueField point
    ((Scheme.Modules.pullback
      ((pullback.snd source.carrier.hom parameter.hom).fiberι point)).obj
        ((Scheme.Modules.pullback (picardFamilyMap morphism parameter)).obj lineBundle)).degree
      (parameter.left.residueField point) = 0 := by
  letI := (pullback.snd source.carrier.hom parameter.hom).fiberOverSpecResidueField point
  letI := (pullback.snd target.carrier.hom parameter.hom).fiberOverSpecResidueField point
  exact (Scheme.Modules.degree_congr _
    (mapResidueFiberModuleIso source target morphism parameter point lineBundle)).trans
      (degree_pullback_eq_zero (residueFiber source parameter point)
        (residueFiber target parameter point)
        (mapResidueFiber source target morphism parameter point) _ zeroDegree)

private theorem picardPresheafDegree_mk_eq_fiber_degree (curve : Curve baseField)
    (parameter : Over (Spec (.of baseField)))
    (lineBundle : (pullback curve.carrier.hom parameter.hom).Modules)
    [lineBundle.IsInvertible] (point : parameter.left) :
    letI := (pullback.snd curve.carrier.hom parameter.hom).fiberOverSpecResidueField point
    picardPresheafDegree curve.carrier.hom (Scheme.Pic.mk lineBundle) point =
      ((Scheme.Modules.pullback
        ((pullback.snd curve.carrier.hom parameter.hom).fiberι point)).obj lineBundle).degree
        (parameter.left.residueField point) := by
  letI := (pullback.snd curve.carrier.hom parameter.hom).fiberOverSpecResidueField point
  exact (picardPresheafDegree_eq_degree curve.carrier.hom
    (Scheme.Pic.mk lineBundle) point).trans
      (Scheme.Modules.degree_congr _
        ((Scheme.Modules.pullback _).mapIso (Scheme.Pic.mkIso lineBundle)))

/-- Pullback preserves degree zero of a relative Picard class at any parameter point. -/
theorem picardPresheafDegree_pullback_eq_zero
    (parameter : Over (Spec (.of baseField)))
    (picardClass : (picardPresheaf target.carrier.hom).obj (.op parameter))
    (point : parameter.left)
    (zeroDegree : picardPresheafDegree target.carrier.hom picardClass point = 0) :
    picardPresheafDegree source.carrier.hom
      (Scheme.Pic.map (picardFamilyMap morphism parameter) picardClass) point = 0 := by
  obtain ⟨lineBundle, invertible, rfl⟩ := Scheme.Pic.exists_mk_eq picardClass
  letI := invertible
  rw [Scheme.Pic.map_mk, picardPresheafDegree_mk_eq_fiber_degree]
  rw [picardPresheafDegree_mk_eq_fiber_degree] at zeroDegree
  exact degree_pullback_fiber_eq_zero source target morphism parameter point lineBundle zeroDegree

/-- Every field-valued test of the pulled-back class has degree zero whenever the
same test of the original class does. -/
theorem picardFibreDegree_pullback_eq_zero
    (parameter : Over (Spec (.of baseField)))
    (picardClass : (picardPresheaf target.carrier.hom).obj (.op parameter))
    {extensionField : Type u} [Field extensionField] [Algebra baseField extensionField]
    (point : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) ⟶
      parameter)
    (zeroDegree : picardFibreDegree target.carrier.hom picardClass point = 0) :
    picardFibreDegree source.carrier.hom
      (Scheme.Pic.map (picardFamilyMap morphism parameter) picardClass) point = 0 := by
  rw [picardFibreDegree_eq_picardPresheafDegree source.carrier.hom _ point
    (IsLocalRing.closedPoint extensionField)]
  apply picardPresheafDegree_pullback_eq_zero source target morphism parameter picardClass
  rwa [← picardFibreDegree_eq_picardPresheafDegree target.carrier.hom picardClass point
    (IsLocalRing.closedPoint extensionField)]

/-- Pullback by any morphism of curves preserves the native degree-zero Picard subfunctor. -/
theorem mem_picardSubfunctorDegree_zero_pullback
    (parameter : Over (Spec (.of baseField)))
    (picardClass : (picardPresheaf target.carrier.hom).obj (.op parameter))
    (degreeZero : picardClass ∈
      (picardSubfunctorDegree target.carrier.hom 0).obj (.op parameter)) :
    Scheme.Pic.map (picardFamilyMap morphism parameter) picardClass ∈
      (picardSubfunctorDegree source.carrier.hom 0).obj (.op parameter) := by
  rw [mem_picardSubfunctorDegree_iff] at degreeZero ⊢
  intro point
  exact picardPresheafDegree_pullback_eq_zero source target morphism parameter picardClass point
    (degreeZero point)

end AlgebraicGeometry.Curve
