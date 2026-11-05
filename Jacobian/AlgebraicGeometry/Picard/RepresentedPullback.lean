import Jacobian.AlgebraicGeometry.Picard.DegreeZeroPullback
import Jacobian.AlgebraicGeometry.Picard.TensorCompatible

/-!
# Pullback between tensor-compatible Picard representations

Pullback of degree-zero Picard classes induces a morphism between any supplied
representing commutative groups whose identity and multiplication classify the
trivial bundle and tensor products. The underlying scheme morphism is the
representing morphism of the Picard sheaf transformation. Its group compatibility
follows from fppf local line-bundle representatives, rather than a choice of group
structure on the representing schemes.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry.PicardTensorCompatible

variable {baseField : Type u} [Field baseField]
  {source target thirdCurve : Curve baseField}
  {sourceGroup targetGroup thirdGroup : CommGrp (Over (Spec (.of baseField)))}
  {sourceRepresentation :
    (picardFunctorDegree source.carrier.hom 0).obj.RepresentableBy sourceGroup.X}
  {targetRepresentation :
    (picardFunctorDegree target.carrier.hom 0).obj.RepresentableBy targetGroup.X}
  {thirdRepresentation :
    (picardFunctorDegree thirdCurve.carrier.hom 0).obj.RepresentableBy thirdGroup.X}

/-- A curve morphism induces a group morphism between any tensor-compatible
representations of the degree-zero Picard sheaves. -/
def representedPullback
    (sourceCompatibility : PicardTensorCompatible source.carrier.hom sourceGroup
      sourceRepresentation)
    (targetCompatibility : PicardTensorCompatible target.carrier.hom targetGroup
      targetRepresentation)
    (morphism : source ⟶ target) : targetGroup ⟶ sourceGroup := by
  let arrow : targetGroup.X ⟶ sourceGroup.X :=
    (picardDegreeZeroRepresentedPullback morphism sourceRepresentation
      targetRepresentation).hom.hom.hom
  have preservesProducts {parameter : Over (Spec (.of baseField))}
      (firstPoint secondPoint : parameter ⟶ targetGroup.X) :
      (firstPoint * secondPoint) ≫ arrow =
        (firstPoint ≫ arrow) * (secondPoint ≫ arrow) := by
    let sourceEquiv : (parameter ⟶ sourceGroup.X) ≃*
        (picardDegreeZeroFunctorGrp source.carrier.hom).obj (.op parameter) :=
      sourceCompatibility.homMulEquiv parameter
    let targetEquiv : (parameter ⟶ targetGroup.X) ≃*
        (picardDegreeZeroFunctorGrp target.carrier.hom).obj (.op parameter) :=
      targetCompatibility.homMulEquiv parameter
    let pullbackHom :
        (picardDegreeZeroFunctorGrp target.carrier.hom).obj (.op parameter) →*
          (picardDegreeZeroFunctorGrp source.carrier.hom).obj (.op parameter) :=
      ((picardDegreeZeroFunctorPullbackGrp morphism).app (.op parameter)).hom
    have application (point : parameter ⟶ targetGroup.X) :
        sourceEquiv (point ≫ arrow) = pullbackHom (targetEquiv point) :=
      picardDegreeZeroRepresentedPullback_app morphism sourceRepresentation
        targetRepresentation parameter point
    apply sourceEquiv.injective
    calc
      sourceEquiv ((firstPoint * secondPoint) ≫ arrow) =
          pullbackHom (targetEquiv (firstPoint * secondPoint)) :=
        application (firstPoint * secondPoint)
      _ = pullbackHom (targetEquiv firstPoint * targetEquiv secondPoint) :=
        congrArg pullbackHom (targetEquiv.map_mul firstPoint secondPoint)
      _ = pullbackHom (targetEquiv firstPoint) * pullbackHom (targetEquiv secondPoint) :=
        pullbackHom.map_mul _ _
      _ = sourceEquiv (firstPoint ≫ arrow) * sourceEquiv (secondPoint ≫ arrow) :=
        congrArg₂ (· * ·) (application firstPoint).symm (application secondPoint).symm
      _ = sourceEquiv ((firstPoint ≫ arrow) * (secondPoint ≫ arrow)) :=
        (sourceEquiv.map_mul _ _).symm
  let pointHom (parameter : Over (Spec (.of baseField))) :
      (parameter ⟶ targetGroup.X) →* (parameter ⟶ sourceGroup.X) :=
    MonoidHom.mk' (fun point ↦ point ≫ arrow) (fun firstPoint secondPoint ↦
      preservesProducts firstPoint secondPoint)
  refine ⟨Grp.homMk'
    { hom := arrow
      isMonHom_hom.one_hom := ?_
      isMonHom_hom.mul_hom := ?_ }⟩
  · rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact (pointHom (𝟙_ (Over (Spec (.of baseField))))).map_one
  · calc
      μ[targetGroup.X] ≫ arrow =
          (fst targetGroup.X targetGroup.X * snd targetGroup.X targetGroup.X) ≫ arrow := by
        rw [CategoryTheory.Hom.mul_def, lift_fst_snd, Category.id_comp]
      _ = (fst targetGroup.X targetGroup.X ≫ arrow) *
          (snd targetGroup.X targetGroup.X ≫ arrow) := preservesProducts _ _
      _ = (arrow ⊗ₘ arrow) ≫ μ[sourceGroup.X] := by
        rw [CategoryTheory.Hom.mul_def]
        congr 1

/-- The group morphism realizes the actual pullback of degree-zero Picard
sections on every test scheme. -/
theorem representedPullback_app
    (sourceCompatibility : PicardTensorCompatible source.carrier.hom sourceGroup
      sourceRepresentation)
    (targetCompatibility : PicardTensorCompatible target.carrier.hom targetGroup
      targetRepresentation)
    (morphism : source ⟶ target) (parameter : Over (Spec (.of baseField)))
    (point : parameter ⟶ targetGroup.X) :
    sourceRepresentation.homEquiv (point ≫
        (representedPullback sourceCompatibility targetCompatibility morphism).hom.hom.hom) =
      (picardDegreeZeroFunctorPullbackGrp morphism).app (.op parameter)
        (targetRepresentation.homEquiv point) :=
  picardDegreeZeroRepresentedPullback_app morphism sourceRepresentation targetRepresentation
    parameter point

/-- A represented point classifying a line bundle is sent to the point
classifying its pullback on the Cartesian family. -/
theorem representedPullback_class
    (sourceCompatibility : PicardTensorCompatible source.carrier.hom sourceGroup
      sourceRepresentation)
    (targetCompatibility : PicardTensorCompatible target.carrier.hom targetGroup
      targetRepresentation)
    (morphism : source ⟶ target) (parameter : Over (Spec (.of baseField)))
    (point : parameter ⟶ targetGroup.X)
    (lineBundle : (pullback target.carrier.hom parameter.hom).Modules)
    [lineBundle.IsInvertible]
    (classifies : (picardFunctorDegreeι target.carrier.hom 0).hom.app (.op parameter)
        (targetRepresentation.homEquiv point) =
      (toPicardFunctor target.carrier.hom).app (.op parameter) (Scheme.Pic.mk lineBundle)) :
    (picardFunctorDegreeι source.carrier.hom 0).hom.app (.op parameter)
        (sourceRepresentation.homEquiv (point ≫
          (representedPullback sourceCompatibility targetCompatibility morphism).hom.hom.hom)) =
      (toPicardFunctor source.carrier.hom).app (.op parameter)
        (Scheme.Pic.mk ((Scheme.Modules.pullback
          (picardFamilyMap morphism parameter)).obj lineBundle)) := by
  rw [representedPullback_app]
  have inclusionSquare := congr_app
    (congrArg (fun transformation : picardFunctorDegree target.carrier.hom 0 ⟶
      picardFunctor source.carrier.hom ↦ transformation.hom)
        (picardDegreeZeroFunctorPullback_inclusion morphism)) (.op parameter)
  have evaluatedSquare := ConcreteCategory.congr_hom inclusionSquare
    (targetRepresentation.homEquiv point)
  change (picardFunctorDegreeι source.carrier.hom 0).hom.app (.op parameter)
      ((picardDegreeZeroFunctorPullback morphism).hom.app (.op parameter)
        (targetRepresentation.homEquiv point)) =
    (picardFunctorPullback morphism).hom.app (.op parameter)
      ((picardFunctorDegreeι target.carrier.hom 0).hom.app (.op parameter)
        (targetRepresentation.homEquiv point)) at evaluatedSquare
  change (picardFunctorDegreeι source.carrier.hom 0).hom.app (.op parameter)
      ((picardDegreeZeroFunctorPullback morphism).hom.app (.op parameter)
        (targetRepresentation.homEquiv point)) = _
  rw [evaluatedSquare, classifies, picardFunctorPullback_toPicardFunctor,
    Scheme.Pic.map_mk]

/-- Classification of pulled-back line bundles determines the group morphism.
Local representatives suffice; no global bundle representative is assumed. -/
theorem representedPullback_unique
    (sourceCompatibility : PicardTensorCompatible source.carrier.hom sourceGroup
      sourceRepresentation)
    (targetCompatibility : PicardTensorCompatible target.carrier.hom targetGroup
      targetRepresentation)
    (morphism : source ⟶ target) (candidate : targetGroup ⟶ sourceGroup)
    (action : ∀ (parameter : Over (Spec (.of baseField))) (point : parameter ⟶ targetGroup.X)
      (lineBundle : (pullback target.carrier.hom parameter.hom).Modules)
      [lineBundle.IsInvertible],
      (picardFunctorDegreeι target.carrier.hom 0).hom.app (.op parameter)
          (targetRepresentation.homEquiv point) =
        (toPicardFunctor target.carrier.hom).app (.op parameter) (Scheme.Pic.mk lineBundle) →
      (picardFunctorDegreeι source.carrier.hom 0).hom.app (.op parameter)
          (sourceRepresentation.homEquiv (point ≫ candidate.hom.hom.hom)) =
        (toPicardFunctor source.carrier.hom).app (.op parameter)
          (Scheme.Pic.mk ((Scheme.Modules.pullback
            (picardFamilyMap morphism parameter)).obj lineBundle))) :
    candidate = representedPullback sourceCompatibility targetCompatibility morphism := by
  apply CommGrp.hom_ext
  apply sourceRepresentation.homEquiv.injective
  let topology := Scheme.fppfTopology.over (Spec (.of baseField))
  let presentation := toSheafify topology
    (picardSubfunctorDegree target.carrier.hom 0).toFunctor
  let coveringSieve := Presheaf.imageSieve presentation
    (targetRepresentation.homEquiv (𝟙 targetGroup.X))
  have covering : coveringSieve ∈ topology targetGroup.X :=
    Presheaf.imageSieve_mem topology presentation (U := .op targetGroup.X)
      (targetRepresentation.homEquiv (𝟙 targetGroup.X))
  apply (((isSheaf_iff_isSheaf_of_type topology _).1
    (picardFunctorDegree source.carrier.hom 0).property).isSeparated
      coveringSieve covering).ext
  rintro cover restriction ⟨localLift, localEquality⟩
  let localClass : picardDegreeZeroSubgroup target.carrier.hom cover := localLift
  obtain ⟨lineBundle, invertible, representative⟩ := Scheme.Pic.exists_mk_eq localClass.val
  letI := invertible
  have localClassifies :
      (picardFunctorDegreeι target.carrier.hom 0).hom.app (.op cover)
          (targetRepresentation.homEquiv restriction) =
        (toPicardFunctor target.carrier.hom).app (.op cover) (Scheme.Pic.mk lineBundle) := by
    have naturality := targetRepresentation.homEquiv_comp restriction (𝟙 targetGroup.X)
    rw [Category.comp_id] at naturality
    have restrictedClass : targetRepresentation.homEquiv restriction =
        presentation.app (.op cover) localLift :=
      naturality.trans localEquality.symm
    calc
      (picardFunctorDegreeι target.carrier.hom 0).hom.app (.op cover)
          (targetRepresentation.homEquiv restriction) =
        (picardFunctorDegreeι target.carrier.hom 0).hom.app (.op cover)
          (presentation.app (.op cover) localLift) :=
        congrArg ((picardFunctorDegreeι target.carrier.hom 0).hom.app (.op cover))
          restrictedClass
      _ = (toPicardFunctor target.carrier.hom).app (.op cover) localClass.val :=
        picardFunctorDegreeι_app_toSheafify target.carrier.hom 0 localClass
      _ = (toPicardFunctor target.carrier.hom).app (.op cover) (Scheme.Pic.mk lineBundle) :=
        congrArg (fun picardClass : (pullback target.carrier.hom cover.hom).Pic ↦
          (toPicardFunctor target.carrier.hom).app (.op cover) picardClass) representative.symm
  rw [← sourceRepresentation.homEquiv_comp, ← sourceRepresentation.homEquiv_comp]
  apply injective_picardFunctorDegreeι_app source.carrier.hom 0 cover
  exact (action cover restriction lineBundle localClassifies).trans
    (representedPullback_class sourceCompatibility targetCompatibility morphism cover
      restriction lineBundle localClassifies).symm

/-- Pullback by the identity curve map is the identity for the supplied group
structure, not only for a canonically induced structure. -/
@[simp]
theorem representedPullback_id
    (compatibility : PicardTensorCompatible source.carrier.hom sourceGroup sourceRepresentation) :
    representedPullback compatibility compatibility (𝟙 source) = 𝟙 sourceGroup := by
  apply CommGrp.hom_ext
  simp only [CommGrp.id_hom, Grp.id_hom_hom]
  change (picardDegreeZeroRepresentedPullback (𝟙 source) sourceRepresentation
      sourceRepresentation).hom.hom.hom = 𝟙 sourceGroup.X
  rw [picardDegreeZeroRepresentedPullback_id]
  simp only [CommGrp.id_hom, Grp.id_hom_hom]

/-- Pullback is contravariantly functorial for supplied tensor-compatible group
structures on all three representing schemes. -/
theorem representedPullback_comp
    (sourceCompatibility : PicardTensorCompatible source.carrier.hom sourceGroup
      sourceRepresentation)
    (targetCompatibility : PicardTensorCompatible target.carrier.hom targetGroup
      targetRepresentation)
    (thirdCompatibility : PicardTensorCompatible thirdCurve.carrier.hom thirdGroup
      thirdRepresentation)
    (firstMap : source ⟶ target) (secondMap : target ⟶ thirdCurve) :
    representedPullback sourceCompatibility thirdCompatibility (firstMap ≫ secondMap) =
      representedPullback targetCompatibility thirdCompatibility secondMap ≫
        representedPullback sourceCompatibility targetCompatibility firstMap := by
  apply CommGrp.hom_ext
  change (picardDegreeZeroRepresentedPullback (firstMap ≫ secondMap)
      sourceRepresentation thirdRepresentation).hom.hom.hom =
    (picardDegreeZeroRepresentedPullback secondMap targetRepresentation
        thirdRepresentation).hom.hom.hom ≫
      (picardDegreeZeroRepresentedPullback firstMap sourceRepresentation
        targetRepresentation).hom.hom.hom
  rw [picardDegreeZeroRepresentedPullback_comp]
  rfl

end AlgebraicGeometry.PicardTensorCompatible
