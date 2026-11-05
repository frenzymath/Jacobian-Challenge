import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Morphisms between represented group functors

The representing correspondence for a group-valued presheaf respects the
induced group law. A natural transformation therefore induces a unique group
morphism between representing objects, compatibly with identities, composition
and natural isomorphisms. The values of the presheaves may live in a universe
different from that of the morphisms of the representing category.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace CategoryTheory.GrpObj

open CartesianMonoidalCategory MonoidalCategory Opposite
open scoped MonObj

variable {category : Type u} [Category.{v} category] [CartesianMonoidalCategory category]
  {source target thirdObject : category}
  {sourceFunctor targetFunctor thirdFunctor : categoryᵒᵖ ⥤ GrpCat.{w}}

/-- The representing correspondence of a group-valued presheaf is a group
isomorphism on every test object for the induced group structure. -/
def homMulEquivOfRepresentableBy
    (representation : (sourceFunctor ⋙ forget GrpCat).RepresentableBy source)
    (testObject : category) :
    letI := ofRepresentableBy source sourceFunctor representation
    (testObject ⟶ source) ≃* sourceFunctor.obj (.op testObject) := by
  letI := ofRepresentableBy source sourceFunctor representation
  refine { representation.homEquiv' with map_mul' := fun firstPoint secondPoint ↦ ?_ }
  change representation.homEquiv' (lift firstPoint secondPoint ≫
      representation.homEquiv'.symm
        (representation.homEquiv' (fst source source) *
          representation.homEquiv' (snd source source))) = _
  simp only [representation.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
  simp only [← representation.homEquiv'_comp]
  simp

private def representingHom
    (sourceRepresentation : (sourceFunctor ⋙ forget GrpCat).RepresentableBy source)
    (targetRepresentation : (targetFunctor ⋙ forget GrpCat).RepresentableBy target)
    (transformation : sourceFunctor ⟶ targetFunctor) : source ⟶ target :=
  targetRepresentation.homEquiv'.symm
    ((transformation.app (.op source)).hom (sourceRepresentation.homEquiv' (𝟙 source)))

private theorem representingHom_app
    (sourceRepresentation : (sourceFunctor ⋙ forget GrpCat).RepresentableBy source)
    (targetRepresentation : (targetFunctor ⋙ forget GrpCat).RepresentableBy target)
    (transformation : sourceFunctor ⟶ targetFunctor) {testObject : category}
    (point : testObject ⟶ source) :
    targetRepresentation.homEquiv'
        (point ≫ representingHom sourceRepresentation targetRepresentation transformation) =
      (transformation.app (.op testObject)).hom (sourceRepresentation.homEquiv' point) := by
  rw [targetRepresentation.homEquiv'_comp]
  unfold representingHom
  rw [Equiv.apply_symm_apply, ← transformation.naturality_apply,
    ← sourceRepresentation.homEquiv'_comp, Category.comp_id]

/-- A natural transformation of represented group functors induces a group
morphism for their induced group structures. -/
def mapOfRepresentableBy
    (sourceRepresentation : (sourceFunctor ⋙ forget GrpCat).RepresentableBy source)
    (targetRepresentation : (targetFunctor ⋙ forget GrpCat).RepresentableBy target)
    (transformation : sourceFunctor ⟶ targetFunctor) :
    letI := ofRepresentableBy source sourceFunctor sourceRepresentation
    letI := ofRepresentableBy target targetFunctor targetRepresentation
    Grp.mk source ⟶ Grp.mk target := by
  letI := ofRepresentableBy source sourceFunctor sourceRepresentation
  letI := ofRepresentableBy target targetFunctor targetRepresentation
  let morphism := representingHom sourceRepresentation targetRepresentation transformation
  have preservesProducts {testObject : category} (firstPoint secondPoint : testObject ⟶ source) :
      (firstPoint * secondPoint) ≫ morphism =
        (firstPoint ≫ morphism) * (secondPoint ≫ morphism) := by
    apply (homMulEquivOfRepresentableBy targetRepresentation testObject).injective
    change targetRepresentation.homEquiv' ((firstPoint * secondPoint) ≫ morphism) =
      targetRepresentation.homEquiv' ((firstPoint ≫ morphism) * (secondPoint ≫ morphism))
    rw [representingHom_app]
    change (transformation.app (.op testObject)).hom
        ((homMulEquivOfRepresentableBy sourceRepresentation testObject)
          (firstPoint * secondPoint)) =
      (homMulEquivOfRepresentableBy targetRepresentation testObject)
        ((firstPoint ≫ morphism) * (secondPoint ≫ morphism))
    rw [map_mul, map_mul, map_mul]
    exact congrArg₂ (· * ·)
      (representingHom_app sourceRepresentation targetRepresentation transformation firstPoint).symm
      (representingHom_app sourceRepresentation targetRepresentation transformation secondPoint).symm
  refine Grp.homMk'
    { hom := morphism
      isMonHom_hom.one_hom := ?_
      isMonHom_hom.mul_hom := ?_ }
  · apply (homMulEquivOfRepresentableBy targetRepresentation (𝟙_ category)).injective
    change targetRepresentation.homEquiv' (η[source] ≫ morphism) =
      targetRepresentation.homEquiv' η[target]
    rw [representingHom_app]
    change (transformation.app (.op (𝟙_ category))).hom
        (sourceRepresentation.homEquiv' (sourceRepresentation.homEquiv'.symm 1)) =
      targetRepresentation.homEquiv' (targetRepresentation.homEquiv'.symm 1)
    simp only [Equiv.apply_symm_apply, map_one]
  · calc
      μ[source] ≫ morphism = (fst source source * snd source source) ≫ morphism := by
        rw [CategoryTheory.Hom.mul_def, lift_fst_snd, Category.id_comp]
      _ = (fst source source ≫ morphism) * (snd source source ≫ morphism) :=
        preservesProducts _ _
      _ = (morphism ⊗ₘ morphism) ≫ μ[target] := by
        rw [CategoryTheory.Hom.mul_def]
        congr 1
        ext <;> simp

/-- The induced group morphism represents the given transformation on every test object. -/
theorem homEquiv_mapOfRepresentableBy
    (sourceRepresentation : (sourceFunctor ⋙ forget GrpCat).RepresentableBy source)
    (targetRepresentation : (targetFunctor ⋙ forget GrpCat).RepresentableBy target)
    (transformation : sourceFunctor ⟶ targetFunctor) {testObject : category}
    (point : testObject ⟶ source) :
    targetRepresentation.homEquiv' (point ≫
      (mapOfRepresentableBy sourceRepresentation targetRepresentation transformation).hom.hom) =
        (transformation.app (.op testObject)).hom (sourceRepresentation.homEquiv' point) :=
  representingHom_app sourceRepresentation targetRepresentation transformation point

/-- Identity transformations induce identity group morphisms. -/
@[simp]
theorem mapOfRepresentableBy_id
    (representation : (sourceFunctor ⋙ forget GrpCat).RepresentableBy source) :
    letI := ofRepresentableBy source sourceFunctor representation
    mapOfRepresentableBy representation representation (𝟙 sourceFunctor) = 𝟙 (Grp.mk source) := by
  letI := ofRepresentableBy source sourceFunctor representation
  apply Grp.hom_ext
  apply representation.homEquiv'.injective
  simpa using homEquiv_mapOfRepresentableBy representation representation (𝟙 sourceFunctor)
    (𝟙 source)

/-- Composition of transformations induces composition of group morphisms. -/
theorem mapOfRepresentableBy_comp
    (sourceRepresentation : (sourceFunctor ⋙ forget GrpCat).RepresentableBy source)
    (targetRepresentation : (targetFunctor ⋙ forget GrpCat).RepresentableBy target)
    (thirdRepresentation : (thirdFunctor ⋙ forget GrpCat).RepresentableBy thirdObject)
    (firstTransformation : sourceFunctor ⟶ targetFunctor)
    (secondTransformation : targetFunctor ⟶ thirdFunctor) :
    letI := ofRepresentableBy source sourceFunctor sourceRepresentation
    letI := ofRepresentableBy target targetFunctor targetRepresentation
    letI := ofRepresentableBy thirdObject thirdFunctor thirdRepresentation
    mapOfRepresentableBy sourceRepresentation thirdRepresentation
        (firstTransformation ≫ secondTransformation) =
      mapOfRepresentableBy sourceRepresentation targetRepresentation firstTransformation ≫
        mapOfRepresentableBy targetRepresentation thirdRepresentation secondTransformation := by
  letI := ofRepresentableBy source sourceFunctor sourceRepresentation
  letI := ofRepresentableBy target targetFunctor targetRepresentation
  letI := ofRepresentableBy thirdObject thirdFunctor thirdRepresentation
  apply Grp.hom_ext
  apply thirdRepresentation.homEquiv'.injective
  have firstFormula := homEquiv_mapOfRepresentableBy sourceRepresentation targetRepresentation
    firstTransformation (𝟙 source)
  have compositeFormula := homEquiv_mapOfRepresentableBy sourceRepresentation thirdRepresentation
    (firstTransformation ≫ secondTransformation) (𝟙 source)
  have secondFormula := homEquiv_mapOfRepresentableBy targetRepresentation thirdRepresentation
    secondTransformation
      (mapOfRepresentableBy sourceRepresentation targetRepresentation firstTransformation).hom.hom
  simp only [Category.id_comp] at firstFormula
  simp only [Category.id_comp, NatTrans.comp_app, GrpCat.comp_apply] at compositeFormula
  rw [firstFormula] at secondFormula
  exact compositeFormula.trans secondFormula.symm

/-- A natural isomorphism of represented group functors gives a group isomorphism. -/
def isoOfRepresentableBy
    (sourceRepresentation : (sourceFunctor ⋙ forget GrpCat).RepresentableBy source)
    (targetRepresentation : (targetFunctor ⋙ forget GrpCat).RepresentableBy target)
    (comparison : sourceFunctor ≅ targetFunctor) :
    letI := ofRepresentableBy source sourceFunctor sourceRepresentation
    letI := ofRepresentableBy target targetFunctor targetRepresentation
    Grp.mk source ≅ Grp.mk target := by
  letI := ofRepresentableBy source sourceFunctor sourceRepresentation
  letI := ofRepresentableBy target targetFunctor targetRepresentation
  exact
    { hom := mapOfRepresentableBy sourceRepresentation targetRepresentation comparison.hom
      inv := mapOfRepresentableBy targetRepresentation sourceRepresentation comparison.inv
      hom_inv_id := by rw [← mapOfRepresentableBy_comp, comparison.hom_inv_id,
        mapOfRepresentableBy_id]
      inv_hom_id := by rw [← mapOfRepresentableBy_comp, comparison.inv_hom_id,
        mapOfRepresentableBy_id] }

end CategoryTheory.GrpObj
