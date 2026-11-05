import Jacobian.AlgebraicGeometry.Cohomology.FieldExtension
import Jacobian.AlgebraicGeometry.Curve.LineBundleDegree
import Jacobian.AlgebraicGeometry.Picard.DegreeSheaf
import Mathlib.CategoryTheory.Yoneda

/-!
# Tensor translation between Picard degree parts

A line bundle of degree `e` on a smooth proper geometrically irreducible curve
induces an isomorphism from its degree-`d` Picard presheaf to its degree-`d + e`
Picard presheaf. The inverse tensors with the dual line bundle. Sheafification
gives the corresponding isomorphism of fppf sheaves, and hence an isomorphism
between any supplied schemes representing the two degree parts.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {baseField : Type schemeUniverse} [Field baseField]
  {curve : Scheme.{schemeUniverse}} [curve.Over (Spec (.of baseField))]

/-- Restricting the parameter scheme commutes with tensoring by a class from the curve. -/
lemma pic_map_baseChangeMap_mul_map_fst
    {parameter otherParameter : Over (Spec (.of baseField))}
    (restriction : otherParameter ⟶ parameter)
    (coefficient : (pullback (curve ↘ Spec (.of baseField)) parameter.hom).Pic)
    (twistClass : curve.Pic) :
    Pic.map (baseChangeMap (curve ↘ Spec (.of baseField)) restriction)
        (coefficient * Pic.map (pullback.fst (curve ↘ Spec (.of baseField)) parameter.hom)
          twistClass) =
      Pic.map (baseChangeMap (curve ↘ Spec (.of baseField)) restriction) coefficient *
        Pic.map (pullback.fst (curve ↘ Spec (.of baseField)) otherParameter.hom) twistClass := by
  have projection :
      baseChangeMap (curve ↘ Spec (.of baseField)) restriction ≫
          pullback.fst (curve ↘ Spec (.of baseField)) parameter.hom =
        pullback.fst (curve ↘ Spec (.of baseField)) otherParameter.hom :=
    pullback.lift_fst _ _ _
  rw [Pic.map_mul, ← Pic.map_comp, projection]

/-- A class pulled back from the curve has its original degree on every field-valued fibre. -/
theorem picardFibreDegree_map_fst [IsProper (curve ↘ Spec (.of baseField))]
    {parameter : Over (Spec (.of baseField))} (coefficient : curve.Pic)
    {extensionField : Type schemeUniverse} [Field extensionField] [Algebra baseField extensionField]
    (point : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) ⟶
      parameter) :
    picardFibreDegree (curve ↘ Spec (.of baseField))
        (Pic.map (pullback.fst (curve ↘ Spec (.of baseField)) parameter.hom) coefficient) point =
      Pic.degree baseField coefficient := by
  have projection :
      baseChangeMap (curve ↘ Spec (.of baseField)) point ≫
          pullback.fst (curve ↘ Spec (.of baseField)) parameter.hom =
        pullback.fst (curve ↘ Spec (.of baseField))
          (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) :=
    pullback.lift_fst _ _ _
  letI fieldFibreStructure : (pullback (curve ↘ Spec (.of baseField))
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))).Over
        (Spec (.of extensionField)) := ⟨pullback.snd _ _⟩
  letI : (pullback (curve ↘ Spec (.of baseField))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))).hom).Over
        (Spec (.of extensionField)) := fieldFibreStructure
  change Modules.degree extensionField ((fromSkeleton _).obj
    (Pic.map (baseChangeMap _ point) (Pic.map (pullback.fst _ parameter.hom) coefficient)).val) = _
  rw [← Pic.map_comp, projection]
  exact (Modules.degree_congr extensionField (fromSkeletonToSkeletonIso _)).trans
    (Modules.degree_pullback extensionField ((fromSkeleton curve.Modules).obj coefficient.val))

variable [IsProper (curve ↘ Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (curve ↘ Spec (.of baseField))]
  [GeometricallyIrreducible (curve ↘ Spec (.of baseField))]

/-- Tensor product adds the degree on every field-valued fibre. -/
theorem picardFibreDegree_mul {parameter : Over (Spec (.of baseField))}
    (firstClass secondClass : (pullback (curve ↘ Spec (.of baseField)) parameter.hom).Pic)
    {extensionField : Type schemeUniverse} [Field extensionField] [Algebra baseField extensionField]
    (point : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) ⟶
      parameter) :
    picardFibreDegree (curve ↘ Spec (.of baseField)) (firstClass * secondClass) point =
      picardFibreDegree (curve ↘ Spec (.of baseField)) firstClass point +
        picardFibreDegree (curve ↘ Spec (.of baseField)) secondClass point := by
  let fieldParameter := Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))
  letI : (pullback (curve ↘ Spec (.of baseField)) fieldParameter.hom).Over
      (Spec (.of extensionField)) := ⟨pullback.snd _ _⟩
  letI : IsProper
      (pullback (curve ↘ Spec (.of baseField)) fieldParameter.hom ↘ Spec (.of extensionField)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  letI : GeometricallyIrreducible
      (pullback (curve ↘ Spec (.of baseField)) fieldParameter.hom ↘ Spec (.of extensionField)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  letI : SmoothOfRelativeDimension 1
      (pullback (curve ↘ Spec (.of baseField)) fieldParameter.hom ↘ Spec (.of extensionField)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  change Pic.degree extensionField (Pic.map (baseChangeMap _ point) (firstClass * secondClass)) =
    Pic.degree extensionField (Pic.map (baseChangeMap _ point) firstClass) +
      Pic.degree extensionField (Pic.map (baseChangeMap _ point) secondClass)
  rw [Pic.map_mul, Pic.degree_mul]

/-- Tensoring by a class from the curve shifts a constant fibre degree by that class's degree. -/
lemma mul_map_fst_mem_picardSubfunctorDegree
    {parameter : Over (Spec (.of baseField))} {degree shift : ℤ} (twistClass : curve.Pic)
    (twistDegree : Pic.degreeHom (k := baseField) twistClass = Multiplicative.ofAdd shift)
    {coefficient : (pullback (curve ↘ Spec (.of baseField)) parameter.hom).Pic}
    (constantDegree : coefficient ∈
      (picardSubfunctorDegree (curve ↘ Spec (.of baseField)) degree).obj (.op parameter)) :
    coefficient * Pic.map (pullback.fst (curve ↘ Spec (.of baseField)) parameter.hom) twistClass ∈
      (picardSubfunctorDegree (curve ↘ Spec (.of baseField)) (degree + shift)).obj (.op parameter) := by
  have twistDegree' : Pic.degree baseField twistClass = shift :=
    Multiplicative.ofAdd.injective twistDegree
  intro extensionField _ _ point
  rw [picardFibreDegree_mul, constantDegree extensionField point,
    picardFibreDegree_map_fst, twistDegree']

/-- Tensoring by the pullback of a fixed class gives a morphism between Picard degree parts. -/
def picardSubfunctorDegreeTensorHom {degree targetDegree shift : ℤ} (twistClass : curve.Pic)
    (twistDegree : Pic.degreeHom (k := baseField) twistClass = Multiplicative.ofAdd shift)
    (targetDegree_eq : targetDegree = degree + shift) :
    (picardSubfunctorDegree (curve ↘ Spec (.of baseField)) degree).toFunctor ⟶
      (picardSubfunctorDegree (curve ↘ Spec (.of baseField)) targetDegree).toFunctor where
  app parameter := TypeCat.ofHom fun coefficient ↦
    ⟨(show (pullback (curve ↘ Spec (.of baseField)) parameter.unop.hom).Pic from coefficient.val) *
        Pic.map (pullback.fst (curve ↘ Spec (.of baseField)) parameter.unop.hom) twistClass, by
      rw [targetDegree_eq]
      exact mul_map_fst_mem_picardSubfunctorDegree twistClass twistDegree coefficient.property⟩
  naturality {parameter otherParameter} restriction := by
    ext coefficient
    exact Subtype.ext
      (pic_map_baseChangeMap_mul_map_fst restriction.unop coefficient.val twistClass).symm

/-- On classes, the degree translation is tensor product with the pulled-back fixed class. -/
theorem picardSubfunctorDegreeTensorHom_app_val {degree targetDegree shift : ℤ}
    (twistClass : curve.Pic)
    (twistDegree : Pic.degreeHom (k := baseField) twistClass = Multiplicative.ofAdd shift)
    (targetDegree_eq : targetDegree = degree + shift)
    (parameter : (Over (Spec (.of baseField)))ᵒᵖ)
    (coefficient : (picardSubfunctorDegree (curve ↘ Spec (.of baseField)) degree).toFunctor.obj
      parameter) :
    ((picardSubfunctorDegreeTensorHom twistClass twistDegree targetDegree_eq).app
      parameter coefficient).val =
        (show (pullback (curve ↘ Spec (.of baseField)) parameter.unop.hom).Pic from coefficient.val) *
          Pic.map (pullback.fst (curve ↘ Spec (.of baseField)) parameter.unop.hom) twistClass :=
  rfl

/-- Tensor translation is an isomorphism, with inverse given by the dual class. -/
def picardSubfunctorDegreeTensorIso {degree targetDegree shift : ℤ} (twistClass : curve.Pic)
    (twistDegree : Pic.degreeHom (k := baseField) twistClass = Multiplicative.ofAdd shift)
    (targetDegree_eq : targetDegree = degree + shift) :
    (picardSubfunctorDegree (curve ↘ Spec (.of baseField)) degree).toFunctor ≅
      (picardSubfunctorDegree (curve ↘ Spec (.of baseField)) targetDegree).toFunctor where
  hom := picardSubfunctorDegreeTensorHom twistClass twistDegree targetDegree_eq
  inv := picardSubfunctorDegreeTensorHom twistClass⁻¹
    (by rw [map_inv, twistDegree]; rfl) (shift := -shift) (by omega)
  hom_inv_id := by
    ext parameter coefficient
    refine Subtype.ext ?_
    let coefficientClass : (pullback (curve ↘ Spec (.of baseField)) parameter.unop.hom).Pic :=
      coefficient.val
    let baseProjection := pullback.fst (curve ↘ Spec (.of baseField)) parameter.unop.hom
    change (coefficientClass * Pic.map baseProjection twistClass) *
      Pic.map baseProjection twistClass⁻¹ = coefficientClass
    rw [show Pic.map baseProjection twistClass⁻¹ = (Pic.map baseProjection twistClass)⁻¹ from
      map_inv (Pic.mapHom baseProjection) twistClass]
    exact mul_inv_cancel_right _ _
  inv_hom_id := by
    ext parameter coefficient
    refine Subtype.ext ?_
    let coefficientClass : (pullback (curve ↘ Spec (.of baseField)) parameter.unop.hom).Pic :=
      coefficient.val
    let baseProjection := pullback.fst (curve ↘ Spec (.of baseField)) parameter.unop.hom
    change (coefficientClass * Pic.map baseProjection twistClass⁻¹) *
      Pic.map baseProjection twistClass = coefficientClass
    rw [show Pic.map baseProjection twistClass⁻¹ = (Pic.map baseProjection twistClass)⁻¹ from
      map_inv (Pic.mapHom baseProjection) twistClass]
    exact inv_mul_cancel_right _ _

/-- Tensor translation identifies the fppf sheaves of the two Picard degree parts. -/
def picardFunctorDegreeTensorIso {degree targetDegree shift : ℤ} (twistClass : curve.Pic)
    (twistDegree : Pic.degreeHom (k := baseField) twistClass = Multiplicative.ofAdd shift)
    (targetDegree_eq : targetDegree = degree + shift) :
    picardFunctorDegree (curve ↘ Spec (.of baseField)) degree ≅
      picardFunctorDegree (curve ↘ Spec (.of baseField)) targetDegree :=
  (presheafToSheaf (fppfTopology.over (Spec (.of baseField))) (Type (schemeUniverse + 1))).mapIso
    (picardSubfunctorDegreeTensorIso twistClass twistDegree targetDegree_eq)

/-- The sheaf isomorphism sends each generating class to its tensor translate. -/
theorem picardFunctorDegreeTensorIso_hom_app_toSheafify {degree targetDegree shift : ℤ}
    (twistClass : curve.Pic)
    (twistDegree : Pic.degreeHom (k := baseField) twistClass = Multiplicative.ofAdd shift)
    (targetDegree_eq : targetDegree = degree + shift) (parameter : Over (Spec (.of baseField)))
    (coefficient : (picardSubfunctorDegree (curve ↘ Spec (.of baseField)) degree).toFunctor.obj
      (.op parameter)) :
    (picardFunctorDegreeTensorIso twistClass twistDegree targetDegree_eq).hom.hom.app (.op parameter)
        ((toSheafify (fppfTopology.over (Spec (.of baseField)))
          (picardSubfunctorDegree (curve ↘ Spec (.of baseField)) degree).toFunctor).app _
            coefficient) =
      (toSheafify (fppfTopology.over (Spec (.of baseField)))
        (picardSubfunctorDegree (curve ↘ Spec (.of baseField)) targetDegree).toFunctor).app _
          ((picardSubfunctorDegreeTensorHom twistClass twistDegree targetDegree_eq).app _
            coefficient) := by
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (fppfTopology.over (Spec (.of baseField)))
      (picardSubfunctorDegreeTensorHom twistClass twistDegree targetDegree_eq))
        (.op parameter)) coefficient).symm

/-- Schemes representing degree parts related by an actual tensor translation are isomorphic. -/
def picardDegreeRepresenterTensorIso {degree targetDegree shift : ℤ} (twistClass : curve.Pic)
    (twistDegree : Pic.degreeHom (k := baseField) twistClass = Multiplicative.ofAdd shift)
    (targetDegree_eq : targetDegree = degree + shift)
    {sourceRepresenter targetRepresenter : Over (Spec (.of baseField))}
    (sourceRepresentation :
      (picardFunctorDegree (curve ↘ Spec (.of baseField)) degree).obj.RepresentableBy
        sourceRepresenter)
    (targetRepresentation :
      (picardFunctorDegree (curve ↘ Spec (.of baseField)) targetDegree).obj.RepresentableBy
        targetRepresenter) :
    sourceRepresenter ≅ targetRepresenter :=
  (sourceRepresentation.ofIso ((sheafToPresheaf _ _).mapIso
    (picardFunctorDegreeTensorIso twistClass twistDegree targetDegree_eq))).uniqueUpToIso
      targetRepresentation

end AlgebraicGeometry
