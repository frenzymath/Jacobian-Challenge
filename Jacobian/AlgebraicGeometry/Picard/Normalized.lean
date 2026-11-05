import Jacobian.AlgebraicGeometry.Picard.Presheaf
import Jacobian.AlgebraicGeometry.Picard.Group
import Jacobian.Algebra.Group.Subgroup.Split
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Picard classes normalized along a section

A section of a family induces a retraction on Picard groups after every base
change. Classes trivial along the section form a subpresheaf of groups, the
kernel of this retraction. The Picard group of the family splits into the
Picard group of the parameter scheme and these normalized classes.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {source base : Scheme.{schemeUniverse}}

/-- The relative Picard presheaf with its tensor-product group structure. -/
def picardPresheafGrp (morphism : source ⟶ base) :
    (Over base)ᵒᵖ ⥤ GrpCat.{schemeUniverse + 1} where
  obj parameter := GrpCat.of (pullback morphism parameter.unop.hom).Pic
  map restriction := GrpCat.ofHom (Pic.mapHom (baseChangeMap morphism restriction.unop))
  map_id parameter := by
    refine GrpCat.hom_ext (MonoidHom.ext fun picardClass ↦ ?_)
    change Pic.map (baseChangeMap morphism (𝟙 parameter).unop) picardClass = picardClass
    rw [unop_id, baseChangeMap_id, Pic.map_id]
  map_comp firstRestriction secondRestriction := by
    refine GrpCat.hom_ext (MonoidHom.ext fun picardClass ↦ ?_)
    change Pic.map (baseChangeMap morphism (firstRestriction ≫ secondRestriction).unop)
        picardClass = Pic.map (baseChangeMap morphism secondRestriction.unop)
          (Pic.map (baseChangeMap morphism firstRestriction.unop) picardClass)
    rw [unop_comp, baseChangeMap_comp, Pic.map_comp]

/-- Forgetting the group law gives the relative Picard presheaf. -/
lemma picardPresheafGrp_comp_forget (morphism : source ⟶ base) :
    picardPresheafGrp morphism ⋙ forget GrpCat.{schemeUniverse + 1} = picardPresheaf morphism :=
  rfl

/-- Base change of a section of a family. -/
abbrev sectionBaseChange (morphism : source ⟶ base) (sectionMorphism : base ⟶ source)
    (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) (parameter : Over base) :
    parameter.left ⟶ pullback morphism parameter.hom :=
  pullback.lift (parameter.hom ≫ sectionMorphism) (𝟙 parameter.left) (by
    rw [Category.assoc, sectionCondition, Category.comp_id, Category.id_comp])

/-- The source projection of a base-changed section is the original section. -/
@[reassoc (attr := simp)]
lemma sectionBaseChange_fst (morphism : source ⟶ base) (sectionMorphism : base ⟶ source)
    (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) (parameter : Over base) :
    sectionBaseChange morphism sectionMorphism sectionCondition parameter ≫
      pullback.fst morphism parameter.hom = parameter.hom ≫ sectionMorphism :=
  pullback.lift_fst _ _ _

/-- The base-changed section is a section of the parameter projection. -/
@[reassoc (attr := simp)]
lemma sectionBaseChange_snd (morphism : source ⟶ base) (sectionMorphism : base ⟶ source)
    (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) (parameter : Over base) :
    sectionBaseChange morphism sectionMorphism sectionCondition parameter ≫
      pullback.snd morphism parameter.hom = 𝟙 parameter.left :=
  pullback.lift_snd _ _ _

/-- The base-changed sections commute with changes of parameter scheme. -/
lemma sectionBaseChange_comp_baseChangeMap (morphism : source ⟶ base) (sectionMorphism : base ⟶ source)
    (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) {parameter targetParameter : Over base}
    (restriction : parameter ⟶ targetParameter) :
    sectionBaseChange morphism sectionMorphism sectionCondition parameter ≫
        baseChangeMap morphism restriction =
      restriction.left ≫ sectionBaseChange morphism sectionMorphism sectionCondition targetParameter := by
  apply pullback.hom_ext
  · simp [baseChangeMap, Category.assoc]
  · simp [baseChangeMap, Category.assoc]

/-- Pullback from the parameter scheme followed by pullback along the section is the identity. -/
def pullbackSectionBaseChangeSndIso (morphism : source ⟶ base) (sectionMorphism : base ⟶ source)
    (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) (parameter : Over base)
    (moduleSheaf : parameter.left.Modules) :
    (Modules.pullback (sectionBaseChange morphism sectionMorphism sectionCondition parameter)).obj
      ((Modules.pullback (pullback.snd morphism parameter.hom)).obj moduleSheaf) ≅ moduleSheaf :=
  (Modules.pullbackComp _ _).app moduleSheaf ≪≫
    (Modules.pullbackCongr (sectionBaseChange_snd morphism sectionMorphism sectionCondition parameter)).app
      moduleSheaf ≪≫ (Modules.pullbackId _).app moduleSheaf

/-- Relative Picard classes whose pullback along the chosen section is trivial. -/
def picardFunctorNormalized (morphism : source ⟶ base) (sectionMorphism : base ⟶ source)
    (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) : Subfunctor (picardPresheaf morphism) where
  obj parameter := {picardClass |
    Pic.map (sectionBaseChange morphism sectionMorphism sectionCondition parameter.unop) picardClass = 1}
  map := by
    rintro ⟨parameter⟩ ⟨targetParameter⟩ ⟨restriction⟩ picardClass normalized
    change Pic.map (sectionBaseChange morphism sectionMorphism sectionCondition targetParameter)
      (Pic.map (baseChangeMap morphism restriction) picardClass) = 1
    rw [← Pic.map_comp, sectionBaseChange_comp_baseChangeMap, Pic.map_comp, normalized, Pic.map_one]

/-- Normalized classes are the kernel of pullback along the section. -/
lemma mem_picardFunctorNormalized_iff (morphism : source ⟶ base) (sectionMorphism : base ⟶ source)
    (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) (parameter : Over base)
    (picardClass : (pullback morphism parameter.hom).Pic) :
    picardClass ∈ (picardFunctorNormalized morphism sectionMorphism sectionCondition).obj (.op parameter) ↔
      picardClass ∈ (Pic.mapHom (sectionBaseChange morphism sectionMorphism sectionCondition parameter)).ker :=
  Iff.rfl

/-- Normalized relative Picard classes form a presheaf of groups. -/
def picardFunctorNormalizedGrp (morphism : source ⟶ base) (sectionMorphism : base ⟶ source)
    (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) :
    (Over base)ᵒᵖ ⥤ GrpCat.{schemeUniverse + 1} where
  obj parameter := GrpCat.of
    (Pic.mapHom (sectionBaseChange morphism sectionMorphism sectionCondition parameter.unop)).ker
  map restriction := GrpCat.ofHom
    { toFun picardClass := ⟨Pic.map (baseChangeMap morphism restriction.unop) picardClass.1,
        (picardFunctorNormalized morphism sectionMorphism sectionCondition).map restriction picardClass.2⟩
      map_one' := Subtype.ext (Pic.map_one _)
      map_mul' firstClass secondClass := Subtype.ext (Pic.map_mul _ firstClass.1 secondClass.1) }
  map_id parameter := by
    refine GrpCat.hom_ext (MonoidHom.ext fun picardClass ↦ Subtype.ext ?_)
    change Pic.map (baseChangeMap morphism (𝟙 parameter).unop) picardClass.1 = picardClass.1
    rw [unop_id, baseChangeMap_id, Pic.map_id]
  map_comp firstRestriction secondRestriction := by
    refine GrpCat.hom_ext (MonoidHom.ext fun picardClass ↦ Subtype.ext ?_)
    change Pic.map (baseChangeMap morphism (firstRestriction ≫ secondRestriction).unop)
        picardClass.1 = Pic.map (baseChangeMap morphism secondRestriction.unop)
          (Pic.map (baseChangeMap morphism firstRestriction.unop) picardClass.1)
    rw [unop_comp, baseChangeMap_comp, Pic.map_comp]

/-- Forgetting the normalized group law gives the normalized Picard subpresheaf. -/
lemma picardFunctorNormalizedGrp_comp_forget (morphism : source ⟶ base) (sectionMorphism : base ⟶ source)
    (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) :
    picardFunctorNormalizedGrp morphism sectionMorphism sectionCondition ⋙
        forget GrpCat.{schemeUniverse + 1} =
      (picardFunctorNormalized morphism sectionMorphism sectionCondition).toFunctor :=
  rfl

/-- A section splits Picard classes into a parameter class and a normalized class. -/
def picMulEquivProdPicardFunctorNormalized (morphism : source ⟶ base) (sectionMorphism : base ⟶ source)
    (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base) (parameter : Over base) :
    (pullback morphism parameter.hom).Pic ≃* parameter.left.Pic ×
      (Pic.mapHom (sectionBaseChange morphism sectionMorphism sectionCondition parameter)).ker :=
  (Pic.mapHom (sectionBaseChange morphism sectionMorphism sectionCondition parameter)).prodKerEquivOfLeftInverse
    (Pic.mapHom (pullback.snd morphism parameter.hom)) fun picardClass ↦ by
      rw [Pic.mapHom_apply, Pic.mapHom_apply, ← Pic.map_comp, sectionBaseChange_snd, Pic.map_id]

/-- The parameter component of the splitting is pullback along the section. -/
@[simp]
lemma picMulEquivProdPicardFunctorNormalized_apply_fst (morphism : source ⟶ base)
    (sectionMorphism : base ⟶ source) (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base)
    (parameter : Over base) (picardClass : (pullback morphism parameter.hom).Pic) :
    (picMulEquivProdPicardFunctorNormalized morphism sectionMorphism sectionCondition parameter picardClass).1 =
      Pic.map (sectionBaseChange morphism sectionMorphism sectionCondition parameter) picardClass :=
  rfl

/-- The normalized component removes the pullback of the restriction to the section. -/
@[simp]
lemma coe_picMulEquivProdPicardFunctorNormalized_apply_snd (morphism : source ⟶ base)
    (sectionMorphism : base ⟶ source) (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base)
    (parameter : Over base) (picardClass : (pullback morphism parameter.hom).Pic) :
    ((picMulEquivProdPicardFunctorNormalized morphism sectionMorphism sectionCondition parameter
      picardClass).2 : (pullback morphism parameter.hom).Pic) =
      picardClass * (Pic.map (pullback.snd morphism parameter.hom)
        (Pic.map (sectionBaseChange morphism sectionMorphism sectionCondition parameter) picardClass))⁻¹ :=
  rfl

/-- The inverse splitting tensors a normalized class with a class pulled back from the base. -/
@[simp]
lemma picMulEquivProdPicardFunctorNormalized_symm_apply (morphism : source ⟶ base)
    (sectionMorphism : base ⟶ source) (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base)
    (parameter : Over base)
    (pair : parameter.left.Pic ×
      (Pic.mapHom (sectionBaseChange morphism sectionMorphism sectionCondition parameter)).ker) :
    (picMulEquivProdPicardFunctorNormalized morphism sectionMorphism sectionCondition parameter).symm pair =
      Pic.map (pullback.snd morphism parameter.hom) pair.1 * pair.2 :=
  rfl

end AlgebraicGeometry
