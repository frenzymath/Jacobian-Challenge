import Mathlib.Algebra.Category.Grp.Basic
import Jacobian.CategoryTheory.Monoidal.RepresentableGroup
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Group laws on sheafifications

The sheafification of the underlying presheaf of a presheaf of groups has a
canonical group law. Multiplication and inverse are obtained from local
representatives and gluing. The sheafification map is multiplicative, and a
representing object inherits the corresponding group-object structure.
-/

noncomputable section

universe morphismUniverse objectUniverse

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {site : Type objectUniverse} [Category.{morphismUniverse} site] {topology : GrothendieckTopology site}

namespace SheafifyGrp

variable {presheaf : siteᵒᵖ ⥤ Type (max objectUniverse morphismUniverse)}

/-- The sheafification satisfies the sheaf condition for covering sieves. -/
lemma isSheaf_sheafify : Presieve.IsSheaf topology (sheafify topology presheaf) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((presheafToSheaf topology _).obj presheaf).property

/-- Two sections of the sheafification which agree on a covering sieve are equal. -/
lemma ext {object : site} {firstSection otherFirstSection : (sheafify topology presheaf).obj (op object)} (sieve : Sieve object) (covering : sieve ∈ topology object)
    (property : ∀ ⦃otherObject : site⦄ (restriction : otherObject ⟶ object), sieve restriction → (sheafify topology presheaf).map restriction.op firstSection = (sheafify topology presheaf).map restriction.op otherFirstSection) :
    firstSection = otherFirstSection :=
  (isSheaf_sheafify.isSeparated sieve covering).ext fun _ restriction membership ↦ property restriction membership

/-- Every section of the sheafification locally comes from the presheaf. -/
lemma imageSieve_mem {object : site} (firstSection : (sheafify topology presheaf).obj (op object)) :
    Presheaf.imageSieve (toSheafify topology presheaf) firstSection ∈ topology object :=
  Presheaf.imageSieve_mem topology (toSheafify topology presheaf) (U := op object) firstSection

/-- Presheaf sections with the same image in the sheafification agree locally. -/
lemma equalizerSieve_mem {object : site} {firstElement otherFirstElement : presheaf.obj (op object)}
    (property : (toSheafify topology presheaf).app _ firstElement = (toSheafify topology presheaf).app _ otherFirstElement) :
    Presheaf.equalizerSieve (F := presheaf) (X := op object) firstElement otherFirstElement ∈ topology object :=
  Presheaf.equalizerSieve_mem topology (toSheafify topology presheaf) firstElement otherFirstElement property

/-- Equality can be checked locally where three auxiliary sections have presheaf representatives. -/
lemma ext_of_imageSieve {object : site} (firstValue secondValue thirdValue : (sheafify topology presheaf).obj (op object))
    {firstSection otherFirstSection : (sheafify topology presheaf).obj (op object)}
    (property : ∀ ⦃otherObject : site⦄ (restriction : otherObject ⟶ object) (firstElement secondElement thirdElement : presheaf.obj (op otherObject)),
      (toSheafify topology presheaf).app _ firstElement = (sheafify topology presheaf).map restriction.op firstValue →
      (toSheafify topology presheaf).app _ secondElement = (sheafify topology presheaf).map restriction.op secondValue →
      (toSheafify topology presheaf).app _ thirdElement = (sheafify topology presheaf).map restriction.op thirdValue →
      (sheafify topology presheaf).map restriction.op firstSection = (sheafify topology presheaf).map restriction.op otherFirstSection) :
    firstSection = otherFirstSection := by
  refine ext (Presheaf.imageSieve (toSheafify topology presheaf) firstValue ⊓ Presheaf.imageSieve (toSheafify topology presheaf) secondValue ⊓
    Presheaf.imageSieve (toSheafify topology presheaf) thirdValue) (topology.intersection_covering (topology.intersection_covering
      (imageSieve_mem firstValue) (imageSieve_mem secondValue)) (imageSieve_mem thirdValue))
      fun otherObject restriction ⟨⟨⟨firstElement, firstEquality⟩, ⟨secondElement, secondEquality⟩⟩, ⟨thirdElement, thirdEquality⟩⟩ ↦ property restriction firstElement secondElement thirdElement firstEquality secondEquality thirdEquality

variable (operation : ∀ ⦃otherObject : site⦄, presheaf.obj (op otherObject) → presheaf.obj (op otherObject) → presheaf.obj (op otherObject))
  (naturality : ∀ ⦃otherObject smallerObject : site⦄ (morphism : smallerObject ⟶ otherObject) (firstElement secondElement : presheaf.obj (op otherObject)), presheaf.map morphism.op (operation firstElement secondElement) = operation (presheaf.map morphism.op firstElement)
    (presheaf.map morphism.op secondElement))

include naturality in
/-- A natural binary operation respects equality after sheafification. -/
lemma toSheafify_app_eq {otherObject : site} {firstElement otherFirstElement secondElement otherSecondElement : presheaf.obj (op otherObject)}
    (firstEquality : (toSheafify topology presheaf).app _ firstElement = (toSheafify topology presheaf).app _ otherFirstElement)
    (secondEquality : (toSheafify topology presheaf).app _ secondElement = (toSheafify topology presheaf).app _ otherSecondElement) :
    (toSheafify topology presheaf).app _ (operation firstElement secondElement) = (toSheafify topology presheaf).app _ (operation otherFirstElement otherSecondElement) := by
  refine ext _ (topology.intersection_covering (equalizerSieve_mem firstEquality) (equalizerSieve_mem secondEquality))
    fun refinementObject restriction ⟨firstLocalEquality, secondLocalEquality⟩ ↦ ?_
  rw [← NatTrans.naturality_apply (toSheafify topology presheaf), ← NatTrans.naturality_apply (toSheafify topology presheaf),
    naturality, naturality]
  exact congrArg _ (congrArg₂ _ firstLocalEquality secondLocalEquality)

/-- The local family obtained by applying an operation to presheaf representatives. -/
noncomputable def liftOpFamily {object : site} (firstSection secondSection : (sheafify topology presheaf).obj (op object)) :
    Presieve.FamilyOfElements (sheafify topology presheaf)
      (Presheaf.imageSieve (toSheafify topology presheaf) firstSection ⊓ Presheaf.imageSieve (toSheafify topology presheaf) secondSection).arrows :=
  fun _ _ membership ↦ (toSheafify topology presheaf).app _ (operation membership.1.choose membership.2.choose)

include naturality in
lemma liftOpFamily_compatible {object : site} (firstSection secondSection : (sheafify topology presheaf).obj (op object)) :
    (liftOpFamily operation firstSection secondSection).Compatible := by
  intro firstDomain secondDomain refinementObject firstRestriction secondRestriction firstRefinement secondRefinement firstMembership secondMembership commutativity
  simp only [liftOpFamily]
  rw [← NatTrans.naturality_apply (toSheafify topology presheaf), ← NatTrans.naturality_apply (toSheafify topology presheaf),
    naturality, naturality]
  refine toSheafify_app_eq operation naturality ?_ ?_
  · rw [NatTrans.naturality_apply (toSheafify topology presheaf), NatTrans.naturality_apply (toSheafify topology presheaf),
      firstMembership.1.choose_spec, secondMembership.1.choose_spec, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, commutativity]
  · rw [NatTrans.naturality_apply (toSheafify topology presheaf), NatTrans.naturality_apply (toSheafify topology presheaf),
      firstMembership.2.choose_spec, secondMembership.2.choose_spec, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, commutativity]

/-- Extend a natural binary operation to the sheafification by gluing local representatives. -/
noncomputable def liftOp {object : site} (firstSection secondSection : (sheafify topology presheaf).obj (op object)) :
    (sheafify topology presheaf).obj (op object) :=
  (isSheaf_sheafify _ (topology.intersection_covering (imageSieve_mem firstSection) (imageSieve_mem secondSection))).amalgamate
    (liftOpFamily operation firstSection secondSection)
    (liftOpFamily_compatible operation naturality firstSection secondSection)

/-- The extended operation is computed on any pair of local presheaf representatives. -/
lemma map_liftOp {object otherObject : site} (firstSection secondSection : (sheafify topology presheaf).obj (op object)) (restriction : otherObject ⟶ object) (firstElement secondElement : presheaf.obj (op otherObject))
    (firstEquality : (toSheafify topology presheaf).app _ firstElement = (sheafify topology presheaf).map restriction.op firstSection)
    (secondEquality : (toSheafify topology presheaf).app _ secondElement = (sheafify topology presheaf).map restriction.op secondSection) :
    (sheafify topology presheaf).map restriction.op (liftOp operation naturality firstSection secondSection) = (toSheafify topology presheaf).app _ (operation firstElement secondElement) := by
  have coveringIntersection := topology.intersection_covering (imageSieve_mem firstSection) (imageSieve_mem secondSection)
  refine ext _ (topology.pullback_stable restriction coveringIntersection) fun refinementObject property localMembership ↦ ?_
  rw [← Functor.map_comp_apply, ← op_comp, liftOp,
    Presieve.IsSheafFor.valid_glue (f := property ≫ restriction) (Hf := localMembership),
    ← NatTrans.naturality_apply (toSheafify topology presheaf), naturality]
  refine toSheafify_app_eq operation naturality ?_ ?_
  · rw [localMembership.1.choose_spec, NatTrans.naturality_apply (toSheafify topology presheaf), firstEquality,
      ← Functor.map_comp_apply, ← op_comp]
  · rw [localMembership.2.choose_spec, NatTrans.naturality_apply (toSheafify topology presheaf), secondEquality,
      ← Functor.map_comp_apply, ← op_comp]

end SheafifyGrp

open SheafifyGrp

variable (topology) (groupPresheaf : siteᵒᵖ ⥤ GrpCat.{max objectUniverse morphismUniverse})

/-- Restriction in the underlying presheaf preserves multiplication. -/
lemma map_mul_forget ⦃otherObject smallerObject : site⦄ (morphism : smallerObject ⟶ otherObject) (firstElement secondElement : (groupPresheaf ⋙ forget GrpCat).obj (op otherObject)) :
    (groupPresheaf ⋙ forget GrpCat).map morphism.op (firstElement * secondElement) =
      (groupPresheaf ⋙ forget GrpCat).map morphism.op firstElement * (groupPresheaf ⋙ forget GrpCat).map morphism.op secondElement :=
  map_mul (groupPresheaf.map morphism.op).hom firstElement secondElement

/-- Restriction in the underlying presheaf preserves inversion. -/
lemma map_inv_forget ⦃otherObject smallerObject : site⦄ (morphism : smallerObject ⟶ otherObject) (firstElement : (groupPresheaf ⋙ forget GrpCat).obj (op otherObject)) :
    (groupPresheaf ⋙ forget GrpCat).map morphism.op firstElement⁻¹ = ((groupPresheaf ⋙ forget GrpCat).map morphism.op firstElement)⁻¹ :=
  map_inv (groupPresheaf.map morphism.op).hom firstElement

/-- Restriction in the underlying presheaf preserves the identity. -/
lemma map_one_forget ⦃otherObject smallerObject : site⦄ (morphism : smallerObject ⟶ otherObject) :
    (groupPresheaf ⋙ forget GrpCat).map morphism.op (1 : groupPresheaf.obj (op otherObject)) = 1 :=
  map_one (groupPresheaf.map morphism.op).hom

/-- The group structure on sheafified sections obtained by gluing the original group operations. -/
@[instance_reducible]
noncomputable def sheafifyGroup (object : site) : Group ((sheafify topology (groupPresheaf ⋙ forget GrpCat)).obj (op object)) :=
  letI : Mul ((sheafify topology (groupPresheaf ⋙ forget GrpCat)).obj (op object)) :=
    ⟨liftOp (fun _ firstElement secondElement ↦ firstElement * secondElement) (map_mul_forget groupPresheaf)⟩
  letI : Inv ((sheafify topology (groupPresheaf ⋙ forget GrpCat)).obj (op object)) :=
    ⟨fun firstSection ↦ liftOp (fun _ firstElement _ ↦ firstElement⁻¹) (fun _ _ morphism firstElement _ ↦ map_inv_forget groupPresheaf morphism firstElement) firstSection firstSection⟩
  letI : One ((sheafify topology (groupPresheaf ⋙ forget GrpCat)).obj (op object)) :=
    ⟨(toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ (1 : groupPresheaf.obj (op object))⟩
  have unitRestriction {otherObject : site} (restriction : otherObject ⟶ object) : (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op 1 =
      (toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ (1 : groupPresheaf.obj (op otherObject)) := by
    change (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op
      ((toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ (1 : groupPresheaf.obj (op object))) = _
    rw [← NatTrans.naturality_apply (toSheafify topology _), map_one_forget]
  have mulRestriction {otherObject : site} (firstSection secondSection : (sheafify topology (groupPresheaf ⋙ forget GrpCat)).obj (op object)) (restriction : otherObject ⟶ object) (firstElement secondElement)
      (firstEquality : (toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ firstElement =
        (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op firstSection)
      (secondEquality : (toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ secondElement =
        (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op secondSection) :
      (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op (firstSection * secondSection) =
        (toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ (firstElement * secondElement : groupPresheaf.obj (op otherObject)) :=
    map_liftOp (fun _ firstElement secondElement ↦ firstElement * secondElement) (map_mul_forget groupPresheaf) firstSection secondSection restriction firstElement secondElement firstEquality secondEquality
  have invRestriction {otherObject : site} (firstSection : (sheafify topology (groupPresheaf ⋙ forget GrpCat)).obj (op object)) (restriction : otherObject ⟶ object) (firstElement)
      (firstEquality : (toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ firstElement =
        (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op firstSection) :
      (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op firstSection⁻¹ =
        (toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ (firstElement⁻¹ : groupPresheaf.obj (op otherObject)) :=
    map_liftOp (fun _ firstElement _ ↦ firstElement⁻¹) (fun _ _ morphism firstElement _ ↦ map_inv_forget groupPresheaf morphism firstElement) firstSection firstSection restriction firstElement firstElement firstEquality firstEquality
  { mul_assoc firstSection secondSection thirdSection := ext_of_imageSieve firstSection secondSection thirdSection fun otherObject restriction firstElement secondElement thirdElement firstEquality secondEquality thirdEquality ↦ by
      rw [mulRestriction _ _ restriction (firstElement * secondElement) thirdElement (mulRestriction _ _ restriction firstElement secondElement firstEquality secondEquality).symm thirdEquality,
        mulRestriction _ _ restriction firstElement (secondElement * thirdElement) firstEquality (mulRestriction _ _ restriction secondElement thirdElement secondEquality thirdEquality).symm, _root_.mul_assoc]
    one_mul firstSection := ext_of_imageSieve firstSection firstSection firstSection fun otherObject restriction firstElement _ _ firstEquality _ _ ↦ by
      rw [mulRestriction _ _ restriction 1 firstElement (unitRestriction restriction).symm firstEquality, _root_.one_mul, firstEquality]
    mul_one firstSection := ext_of_imageSieve firstSection firstSection firstSection fun otherObject restriction firstElement _ _ firstEquality _ _ ↦ by
      rw [mulRestriction _ _ restriction firstElement 1 firstEquality (unitRestriction restriction).symm, _root_.mul_one, firstEquality]
    inv_mul_cancel firstSection := ext_of_imageSieve firstSection firstSection firstSection fun otherObject restriction firstElement _ _ firstEquality _ _ ↦ by
      rw [mulRestriction _ _ restriction firstElement⁻¹ firstElement (invRestriction firstSection restriction firstElement firstEquality).symm firstEquality, _root_.inv_mul_cancel, unitRestriction] }

attribute [local instance] sheafifyGroup

/-- Multiplication in the sheafification is computed on local presheaf representatives. -/
lemma map_sheafify_mul {object otherObject : site} (firstSection secondSection : (sheafify topology (groupPresheaf ⋙ forget GrpCat)).obj (op object)) (restriction : otherObject ⟶ object)
    (firstElement secondElement : groupPresheaf.obj (op otherObject))
    (firstEquality : (toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ firstElement =
      (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op firstSection)
    (secondEquality : (toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ secondElement =
      (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op secondSection) :
    (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op (firstSection * secondSection) =
      (toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ (firstElement * secondElement) :=
  map_liftOp (fun _ firstElement secondElement ↦ firstElement * secondElement) (map_mul_forget groupPresheaf) firstSection secondSection restriction firstElement secondElement firstEquality secondEquality

/-- The sheafification map is multiplicative. -/
lemma toSheafify_mul {object : site} (firstElement secondElement : groupPresheaf.obj (op object)) :
    (toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ (firstElement * secondElement) =
      (toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ firstElement * (toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ secondElement := by
  have property := map_sheafify_mul topology groupPresheaf ((toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ firstElement)
    ((toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ secondElement) (𝟙 object) firstElement secondElement (by simp) (by simp)
  simpa using property.symm

/-- Pulling back sections of the sheafification is multiplicative. -/
lemma sheafify_map_mul {object otherObject : site} (restriction : otherObject ⟶ object) (firstSection secondSection : (sheafify topology (groupPresheaf ⋙ forget GrpCat)).obj (op object)) :
    (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op (firstSection * secondSection) =
      (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op firstSection * (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op secondSection :=
  ext_of_imageSieve ((sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op firstSection)
    ((sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op secondSection) ((sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction.op secondSection)
    fun refinementObject property firstElement secondElement _ firstEquality secondEquality _ ↦ by
      rw [map_sheafify_mul topology groupPresheaf _ _ property firstElement secondElement firstEquality secondEquality, ← Functor.map_comp_apply, ← op_comp,
        map_sheafify_mul topology groupPresheaf firstSection secondSection (property ≫ restriction) firstElement secondElement (by rw [op_comp, Functor.map_comp_apply]; exact firstEquality)
          (by rw [op_comp, Functor.map_comp_apply]; exact secondEquality)]

/-- The sheafification of the underlying presheaf, equipped with its induced group law. -/
noncomputable def sheafifyGrp : siteᵒᵖ ⥤ GrpCat.{max objectUniverse morphismUniverse} where
  obj object := letI := sheafifyGroup topology groupPresheaf object.unop
    GrpCat.of ((sheafify topology (groupPresheaf ⋙ forget GrpCat)).obj (op object.unop))
  map {object otherObject} restriction := GrpCat.ofHom
    { toFun := (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction
      map_one' := by
        change (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction
          ((toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ (1 : groupPresheaf.obj object)) =
            (toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ (1 : groupPresheaf.obj otherObject)
        rw [← NatTrans.naturality_apply (toSheafify topology _), ← restriction.op_unop, map_one_forget]
      map_mul' firstSection secondSection := sheafify_map_mul topology groupPresheaf restriction.unop firstSection secondSection }
  map_id object := by
    ext firstSection
    change (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map (𝟙 object) firstSection = firstSection
    simp
  map_comp morphism restriction := by
    ext firstSection
    change (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map (morphism ≫ restriction) firstSection =
      (sheafify topology (groupPresheaf ⋙ forget GrpCat)).map restriction ((sheafify topology (groupPresheaf ⋙ forget GrpCat)).map morphism firstSection)
    simp

/-- Forgetting the induced group law recovers the sheafification of the underlying presheaf. -/
lemma sheafifyGrp_comp_forget :
    sheafifyGrp topology groupPresheaf ⋙ forget GrpCat = sheafify topology (groupPresheaf ⋙ forget GrpCat) :=
  rfl

/-- Sheafification preserves commutativity of the group operations. -/
lemma sheafify_mul_comm (commutative : ∀ (object : siteᵒᵖ) (firstElement secondElement : groupPresheaf.obj object), firstElement * secondElement = secondElement * firstElement) {object : site}
    (firstSection secondSection : (sheafify topology (groupPresheaf ⋙ forget GrpCat)).obj (op object)) : firstSection * secondSection = secondSection * firstSection :=
  ext_of_imageSieve firstSection secondSection secondSection fun otherObject restriction firstElement secondElement _ firstEquality secondEquality _ ↦ by
    rw [map_sheafify_mul topology groupPresheaf firstSection secondSection restriction firstElement secondElement firstEquality secondEquality, map_sheafify_mul topology groupPresheaf secondSection firstSection restriction secondElement firstElement secondEquality firstEquality, commutative]

variable [CartesianMonoidalCategory site] {object : site}

variable (object) in
/-- An object representing the sheafification of a presheaf of groups inherits a group law. -/
@[instance_reducible]
noncomputable def GrpObj.ofRepresentableBySheafify
    (representation : (sheafify topology (groupPresheaf ⋙ forget GrpCat)).RepresentableBy object) : GrpObj object :=
  GrpObj.ofRepresentableBy object (sheafifyGrp topology groupPresheaf) representation

open scoped MonObj in
/-- The representing bijection preserves the induced group operations. -/
lemma homEquiv_mul_ofRepresentableBySheafify
    (representation : (sheafify topology (groupPresheaf ⋙ forget GrpCat)).RepresentableBy object) {otherObject : site} (firstValue secondValue : otherObject ⟶ object) :
    letI := GrpObj.ofRepresentableBySheafify topology groupPresheaf object representation
    representation.homEquiv (firstValue * secondValue) = representation.homEquiv firstValue * representation.homEquiv secondValue := by
  let := GrpObj.ofRepresentableBySheafify topology groupPresheaf object representation
  exact (GrpObj.homMulEquivOfRepresentableBy
    (sourceFunctor := sheafifyGrp topology groupPresheaf) representation otherObject).map_mul
      firstValue secondValue

open scoped MonObj in
/-- The classifying map from original presheaf sections to a representing object is multiplicative. -/
lemma homEquiv_symm_toSheafify_mul
    (representation : (sheafify topology (groupPresheaf ⋙ forget GrpCat)).RepresentableBy object) {otherObject : site} (firstElement secondElement : groupPresheaf.obj (op otherObject)) :
    letI := GrpObj.ofRepresentableBySheafify topology groupPresheaf object representation
    representation.homEquiv.symm ((toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ (firstElement * secondElement)) =
      representation.homEquiv.symm ((toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ firstElement) *
        representation.homEquiv.symm ((toSheafify topology (groupPresheaf ⋙ forget GrpCat)).app _ secondElement) := by
  let := GrpObj.ofRepresentableBySheafify topology groupPresheaf object representation
  apply representation.homEquiv.injective
  rw [homEquiv_mul_ofRepresentableBySheafify, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, toSheafify_mul]

open scoped MonObj in
/-- A representing object of the sheafification of a presheaf of commutative groups is a
commutative group object. -/
lemma isCommMonObj_ofRepresentableBySheafify [BraidedCategory site]
    (commutative : ∀ (otherObject : siteᵒᵖ) (firstElement secondElement : groupPresheaf.obj otherObject), firstElement * secondElement = secondElement * firstElement)
    (representation : (sheafify topology (groupPresheaf ⋙ forget GrpCat)).RepresentableBy object) :
    letI := GrpObj.ofRepresentableBySheafify topology groupPresheaf object representation
    IsCommMonObj object := by
  let := GrpObj.ofRepresentableBySheafify topology groupPresheaf object representation
  refine ⟨?_⟩
  apply representation.homEquiv.injective
  have firstMembership : (β_ object object).hom ≫ μ[object] = CartesianMonoidalCategory.snd object object *
      CartesianMonoidalCategory.fst object object := by
    rw [Hom.mul_def]
    congr 1
    ext <;> simp
  have secondMembership : μ[object] = CartesianMonoidalCategory.fst object object * CartesianMonoidalCategory.snd object object := by
    rw [Hom.mul_def, CartesianMonoidalCategory.lift_fst_snd, Category.id_comp]
  rw [firstMembership, secondMembership, homEquiv_mul_ofRepresentableBySheafify, homEquiv_mul_ofRepresentableBySheafify]
  exact sheafify_mul_comm topology groupPresheaf commutative _ _

end CategoryTheory
