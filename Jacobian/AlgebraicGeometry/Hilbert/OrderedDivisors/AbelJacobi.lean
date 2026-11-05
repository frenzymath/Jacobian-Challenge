import Jacobian.AlgebraicGeometry.Curve.AbelJacobiClass
import Jacobian.AlgebraicGeometry.Hilbert.TranslatedAbelMap
import Jacobian.AlgebraicGeometry.Hilbert.OrderedDivisors.AbelianSum
import Jacobian.AlgebraicGeometry.Picard.TensorRepresentation

/-!
# Ordered divisors and the Abel–Jacobi morphism

The divisor of an ordered tuple, translated by the negative marked-point
divisor, classifies the sum of the tuple's Abel–Jacobi images. The comparison
uses the actual Picard sheaf on every parameter scheme; neither reducedness
nor distinctness of the points is required.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped BigOperators CategoryTheory.MonObj

namespace AlgebraicGeometry.Hilbert.OrderedDivisors

open Scheme

variable {baseField : Type u} [Field baseField] (curve : PointedCurve baseField)

local instance curveOver : curve.curve.carrier.left.Over (Spec (.of baseField)) :=
  ⟨curve.curve.carrier.hom⟩

local instance curveProper : IsProper (curve.curve.carrier.left ↘ Spec (.of baseField)) :=
  curve.curve.isProper

local instance curveSmooth : SmoothOfRelativeDimension 1
    (curve.curve.carrier.left ↘ Spec (.of baseField)) := curve.curve.smoothOfRelativeDimension

local instance curveGeometricallyIrreducible : GeometricallyIrreducible
    (curve.curve.carrier.left ↘ Spec (.of baseField)) := curve.curve.geometricallyIrreducible

local instance picardSectionsCommMonoid (parameter : Over (Spec (.of baseField))) :
    CommMonoid ((picardFunctorGrp curve.curve.carrier.hom).obj (op parameter)) :=
  { (inferInstance : Monoid ((picardFunctorGrp curve.curve.carrier.hom).obj (op parameter))) with
    mul_comm := sheafify_mul_comm (Scheme.fppfTopology.over (Spec (.of baseField)))
      (picardPresheafGrp curve.curve.carrier.hom)
      (fun test (firstClass secondClass :
        (pullback curve.curve.carrier.hom test.unop.hom).Pic) ↦ mul_comm firstClass secondClass) }

local instance picardSheafSectionsCommMonoid (parameter : Over (Spec (.of baseField))) :
    CommMonoid ((picardFunctor curve.curve.carrier.hom).obj.obj (op parameter)) :=
  picardSectionsCommMonoid curve parameter

variable {representingGroup : CommGrp (Over (Spec (.of baseField)))}
  (representation : (picardFunctorDegree curve.curve.carrier.hom 0).obj.RepresentableBy
    representingGroup.X)
  (compatibility : PicardTensorCompatible curve.curve.carrier.hom representingGroup representation)

private def representedClassHom (parameter : Over (Spec (.of baseField))) :
    (parameter ⟶ representingGroup.X) →*
      (picardFunctorGrp curve.curve.carrier.hom).obj (op parameter) :=
  ((picardDegreeZeroFunctorιGrp curve.curve.carrier.hom).app (op parameter)).hom.comp
    (compatibility.homMulEquiv parameter).toMonoidHom

private theorem representedClassHom_apply (parameter : Over (Spec (.of baseField)))
    (point : parameter ⟶ representingGroup.X) :
    representedClassHom curve representation compatibility parameter point =
      (picardFunctorDegreeι curve.curve.carrier.hom 0).hom.app (op parameter)
        (representation.homEquiv point) :=
  ConcreteCategory.congr_hom
    (congr_app (picardDegreeZeroFunctorιGrp_whiskerRight curve.curve.carrier.hom) (op parameter))
    (representation.homEquiv point)

include compatibility in
/-- Products of represented points classify products in the full Picard sheaf. -/
theorem representedClass_prod {degree : ℕ} {parameter : Over (Spec (.of baseField))}
    (points : Fin degree → (parameter ⟶ representingGroup.X)) :
    (picardFunctorDegreeι curve.curve.carrier.hom 0).hom.app (op parameter)
        (representation.homEquiv (∏ index, points index)) =
      ∏ index, (picardFunctorDegreeι curve.curve.carrier.hom 0).hom.app (op parameter)
        (representation.homEquiv (points index)) := by
  refine Eq.trans
    (b := representedClassHom curve representation compatibility parameter (∏ index, points index))
    (representedClassHom_apply curve representation compatibility parameter _).symm ?_
  refine Eq.trans
    (b := ∏ index, representedClassHom curve representation compatibility parameter (points index))
    (map_prod (representedClassHom curve representation compatibility parameter) _ _) ?_
  exact Finset.prod_congr rfl fun index _ ↦
    representedClassHom_apply curve representation compatibility parameter (points index)

include compatibility in
/-- The sum of any tuple has the divisor class of its graph ideals minus the marked points. -/
theorem abelianSum_classifies {degree : ℕ} {parameter : Over (Spec (.of baseField))}
    (points : Fin degree → (parameter ⟶ curve.curve.carrier)) :
    (picardFunctorDegreeι curve.curve.carrier.hom 0).hom.app (op parameter)
        (representation.homEquiv (∏ index, points index ≫
          Curve.abelJacobiMap curve.curve curve.point.left
            (by simpa using Over.w curve.point) representation)) =
      (toPicardFunctor curve.curve.carrier.hom).app (op parameter)
        (abelClass curve.curve.carrier.hom (element curve.curve.carrier.hom points) *
          Pic.map (pullback.fst curve.curve.carrier.hom parameter.hom)
            (curve.pointIdealClass ^ degree)) := by
  let classMap : (pullback curve.curve.carrier.hom parameter.hom).Pic →*
      (picardFunctor curve.curve.carrier.hom).obj.obj (op parameter) :=
    toPicardFunctorHom curve.curve.carrier.hom parameter
  have power_eq : Pic.map (pullback.fst curve.curve.carrier.hom parameter.hom)
      (curve.pointIdealClass ^ degree) =
        (Pic.map (pullback.fst curve.curve.carrier.hom parameter.hom) curve.pointIdealClass) ^
          degree :=
    map_pow (Pic.mapHom (pullback.fst curve.curve.carrier.hom parameter.hom))
      curve.pointIdealClass degree
  refine (representedClass_prod curve representation compatibility _).trans ?_
  refine Eq.trans (b := ∏ index, classMap
        (abelClass curve.curve.carrier.hom
            (element curve.curve.carrier.hom (fun _ : Fin 1 ↦ points index)) *
          Pic.map (pullback.fst curve.curve.carrier.hom parameter.hom)
            curve.pointIdealClass)) ?_ ?_
  · apply Finset.prod_congr rfl
    intro index membership
    exact curve.abelJacobiMap_classifies_graph representation (points index)
  refine (map_prod classMap _ _).symm.trans ?_
  apply congrArg classMap
  rw [Finset.prod_mul_distrib, ← abelClass_ordered_prod,
    Fin.prod_const, power_eq]

include compatibility in
/-- The actual translated Hilbert Abel map on an ordered divisor is the Abel–Jacobi sum. -/
theorem map_translatedAbelMap_eq_abelianSum (degree : ℕ)
    {hilbertScheme : Over (Spec (.of baseField))}
    (hilbertRepresentation : (hilbertPresheaf curve.curve.carrier.hom degree).RepresentableBy
      hilbertScheme) :
    map curve.curve.carrier.hom hilbertRepresentation ≫
        Hilbert.translatedAbelMap curve.curve degree (curve.pointIdealClass ^ degree)
          (curve.degreeHom_pointIdealClass_pow degree) hilbertRepresentation representation =
      abelianSum curve.curve representingGroup
        (Curve.abelJacobiMap curve.curve curve.point.left
          (by simpa using Over.w curve.point) representation) degree := by
  have divisor : hilbertRepresentation.homEquiv
      (map curve.curve.carrier.hom hilbertRepresentation) =
        element curve.curve.carrier.hom
          (Pi.π (fun _ : Fin degree ↦ curve.curve.carrier)) := by
    apply Subtype.ext
    change (hilbertRepresentation.homEquiv
      (map curve.curve.carrier.hom hilbertRepresentation)).val =
        ideal curve.curve.carrier.hom (Pi.π (fun _ : Fin degree ↦ curve.curve.carrier))
    calc
      _ = ideal curve.curve.carrier.hom
          (fun index : Fin degree ↦
            Pi.π (fun _ : Fin degree ↦ Over.mk curve.curve.carrier.hom) index) := by
        simpa only [Category.id_comp] using
          map_val curve.curve.carrier.hom hilbertRepresentation (𝟙 _)
      _ = _ := by
        apply congrArg (ideal curve.curve.carrier.hom)
        funext index
        rfl
  apply representation.homEquiv.injective
  apply injective_picardFunctorDegreeι_app curve.curve.carrier.hom 0 _
  rw [Hilbert.translatedAbelMap_classifies, divisor]
  exact (abelianSum_classifies curve representation compatibility
    (Pi.π (fun _ : Fin degree ↦ curve.curve.carrier))).symm

include compatibility in
/-- The comparison evaluated on a tuple over an arbitrary parameter scheme. -/
theorem map_lift_translatedAbelMap (degree : ℕ)
    {hilbertScheme parameter : Over (Spec (.of baseField))}
    (hilbertRepresentation : (hilbertPresheaf curve.curve.carrier.hom degree).RepresentableBy
      hilbertScheme) (points : Fin degree → (parameter ⟶ curve.curve.carrier)) :
    (Pi.lift points ≫ map curve.curve.carrier.hom hilbertRepresentation) ≫
        Hilbert.translatedAbelMap curve.curve degree (curve.pointIdealClass ^ degree)
          (curve.degreeHom_pointIdealClass_pow degree) hilbertRepresentation representation =
      ∏ index, points index ≫ Curve.abelJacobiMap curve.curve curve.point.left
        (by simpa using Over.w curve.point) representation := by
  rw [Category.assoc, map_translatedAbelMap_eq_abelianSum curve representation compatibility,
    abelianSum_lift]

/-- Insert one variable point followed by copies of the marked point. -/
def markedTuple (degree : ℕ) :
    curve.curve.carrier ⟶ ∏ᶜ fun _ : Fin (degree + 1) ↦ curve.curve.carrier :=
  Pi.lift (Fin.cases (𝟙 curve.curve.carrier)
    (fun _ ↦ CartesianMonoidalCategory.toUnit curve.curve.carrier ≫ curve.point))

/-- A pointed morphism sums the marked tuple to its single variable value. -/
theorem markedTuple_abelianSum (group : CommGrp (Over (Spec (.of baseField))))
    (morphism : curve.curve.carrier ⟶ group.X) (point_eq : curve.point ≫ morphism = 1)
    (degree : ℕ) :
    markedTuple curve degree ≫ abelianSum curve.curve group morphism (degree + 1) = morphism := by
  have constant_eq : (CartesianMonoidalCategory.toUnit curve.curve.carrier ≫ curve.point) ≫
      morphism = (1 : curve.curve.carrier ⟶ group.X) := by
    rw [Category.assoc, point_eq]
    exact MonObj.comp_one _
  rw [markedTuple, abelianSum_lift, Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, Category.id_comp, constant_eq,
    Finset.prod_const_one]
  exact mul_one morphism

include compatibility in
/-- Restricting the translated ordered-divisor map to the marked tuple recovers Abel–Jacobi. -/
theorem markedTuple_map_translatedAbelMap (degree : ℕ)
    {hilbertScheme : Over (Spec (.of baseField))}
    (hilbertRepresentation : (hilbertPresheaf curve.curve.carrier.hom (degree + 1)).RepresentableBy
      hilbertScheme) :
    markedTuple curve degree ≫ map curve.curve.carrier.hom hilbertRepresentation ≫
        Hilbert.translatedAbelMap curve.curve (degree + 1)
          (curve.pointIdealClass ^ (degree + 1))
          (curve.degreeHom_pointIdealClass_pow (degree + 1)) hilbertRepresentation representation =
      Curve.abelJacobiMap curve.curve curve.point.left
        (by simpa using Over.w curve.point) representation := by
  rw [map_translatedAbelMap_eq_abelianSum curve representation compatibility]
  apply markedTuple_abelianSum
  exact Curve.abelJacobiMap_point curve.curve curve.point.left
    (by simpa using Over.w curve.point) representation compatibility

/-- A genuine homomorphism of commutative group schemes preserves the ordered sum. -/
theorem abelianSum_groupHom (sourceGroup targetGroup : CommGrp (Over (Spec (.of baseField))))
    (morphism : curve.curve.carrier ⟶ sourceGroup.X) (groupMap : sourceGroup ⟶ targetGroup)
    (degree : ℕ) :
    abelianSum curve.curve sourceGroup morphism degree ≫
        (CommGrp.forget (Over (Spec (.of baseField)))).map groupMap =
      abelianSum curve.curve targetGroup
        (morphism ≫ (CommGrp.forget (Over (Spec (.of baseField)))).map groupMap) degree := by
  change abelianSum curve.curve sourceGroup morphism degree ≫ groupMap.hom.hom.hom =
    abelianSum curve.curve targetGroup (morphism ≫ groupMap.hom.hom.hom) degree
  let underlyingMap : sourceGroup.X ⟶ targetGroup.X := groupMap.hom.hom.hom
  letI : IsMonHom underlyingMap := by
    change IsMonHom groupMap.hom.hom.hom
    infer_instance
  let power := ∏ᶜ fun _ : Fin degree ↦ curve.curve.carrier
  let postcomp : (power ⟶ sourceGroup.X) →* (power ⟶ targetGroup.X) :=
    { toFun := fun point ↦ point ≫ underlyingMap
      map_one' := MonObj.one_comp _
      map_mul' := fun firstPoint secondPoint ↦ MonObj.mul_comp firstPoint secondPoint _ }
  have comparison := map_prod postcomp
    (fun index : Fin degree ↦ Pi.π (fun _ : Fin degree ↦ curve.curve.carrier) index ≫ morphism)
    Finset.univ
  change (∏ index : Fin degree,
      Pi.π (fun _ : Fin degree ↦ curve.curve.carrier) index ≫ morphism) ≫ underlyingMap =
    ∏ index : Fin degree,
      (Pi.π (fun _ : Fin degree ↦ curve.curve.carrier) index ≫ morphism) ≫ underlyingMap at comparison
  simpa only [abelianSum, Category.assoc] using comparison

end AlgebraicGeometry.Hilbert.OrderedDivisors
