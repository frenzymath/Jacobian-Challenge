import Jacobian.AlgebraicGeometry.Picard.Normalized
import Jacobian.AlgebraicGeometry.Picard.Sheaf
import Jacobian.CategoryTheory.Sites.SheafifyGrp

/-!
# Group structures on represented Picard sheaves

The fppf Picard sheaf inherits a commutative group law from tensor product of
invertible module sheaves. If the Picard sheaf is represented, its representing
object is a commutative group object, and the classifying maps preserve tensor
products. Representability is an explicit hypothesis, not a conclusion here.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory Limits
open scoped MonObj

namespace AlgebraicGeometry

open Scheme

variable {source base : Scheme.{schemeUniverse}}

/-- The relative Picard sheaf as a presheaf of groups. -/
def picardFunctorGrp (morphism : source ⟶ base) :
    (Over base)ᵒᵖ ⥤ GrpCat.{schemeUniverse + 1} :=
  sheafifyGrp (fppfTopology.over base) (picardPresheafGrp morphism)

/-- Forgetting the group structure recovers the relative Picard sheaf. -/
lemma picardFunctorGrp_comp_forget (morphism : source ⟶ base) :
    picardFunctorGrp morphism ⋙ forget GrpCat.{schemeUniverse + 1} = (picardFunctor morphism).obj :=
  rfl

/-- The map from Picard classes to the relative Picard sheaf is a group homomorphism. -/
def toPicardFunctorHom (morphism : source ⟶ base) (parameter : Over base) :
    (pullback morphism parameter.hom).Pic →* (picardFunctorGrp morphism).obj (.op parameter) where
  toFun := (toPicardFunctor morphism).app (.op parameter)
  map_one' := rfl
  map_mul' := toSheafify_mul (fppfTopology.over base) (picardPresheafGrp morphism)

/-- The canonical group homomorphism acts by the sheafification map. -/
@[simp]
lemma toPicardFunctorHom_apply (morphism : source ⟶ base) (parameter : Over base)
    (picardClass : (pullback morphism parameter.hom).Pic) :
    toPicardFunctorHom morphism parameter picardClass =
      (toPicardFunctor morphism).app (.op parameter) picardClass :=
  rfl

/-- A scheme representing the relative Picard sheaf inherits a commutative group structure. -/
@[instance_reducible]
def picardFunctorCommGrpObj (morphism : source ⟶ base) {representing : Over base}
    (representation : (picardFunctor morphism).obj.RepresentableBy representing) :
    CommGrpObj representing := by
  letI := GrpObj.ofRepresentableBySheafify (fppfTopology.over base)
    (picardPresheafGrp morphism) representing representation
  haveI := isCommMonObj_ofRepresentableBySheafify (fppfTopology.over base)
    (picardPresheafGrp morphism)
    (fun parameter (firstClass secondClass : (pullback morphism parameter.unop.hom).Pic) ↦
      mul_comm firstClass secondClass) representation
  exact {}

/-- The classifying map to a represented Picard sheaf sends tensor products to products. -/
lemma homEquiv_symm_toPicardFunctor_mul (morphism : source ⟶ base) {representing : Over base}
    (representation : (picardFunctor morphism).obj.RepresentableBy representing)
    {parameter : Over base} (firstClass secondClass : (pullback morphism parameter.hom).Pic) :
    letI := picardFunctorCommGrpObj morphism representation
    representation.homEquiv.symm
        ((toPicardFunctor morphism).app (.op parameter) (firstClass * secondClass)) =
      representation.homEquiv.symm ((toPicardFunctor morphism).app (.op parameter) firstClass) *
        representation.homEquiv.symm ((toPicardFunctor morphism).app (.op parameter) secondClass) := by
  letI := picardFunctorCommGrpObj morphism representation
  exact homEquiv_symm_toSheafify_mul (fppfTopology.over base) (picardPresheafGrp morphism)
    representation firstClass secondClass

/-- The classifying map to a represented Picard sheaf is a group homomorphism. -/
def picardClassifyingHom (morphism : source ⟶ base) {representing : Over base}
    (representation : (picardFunctor morphism).obj.RepresentableBy representing)
    (parameter : Over base) :
    letI := picardFunctorCommGrpObj morphism representation
    (pullback morphism parameter.hom).Pic →* (parameter ⟶ representing) := by
  letI := picardFunctorCommGrpObj morphism representation
  exact MonoidHom.mk'
    (fun picardClass ↦ representation.homEquiv.symm
      ((toPicardFunctor morphism).app (.op parameter) picardClass))
    (homEquiv_symm_toPicardFunctor_mul morphism representation)

/-- The classifying homomorphism sends a class to the point classifying its sheafification. -/
@[simp]
lemma picardClassifyingHom_apply (morphism : source ⟶ base) {representing : Over base}
    (representation : (picardFunctor morphism).obj.RepresentableBy representing)
    (parameter : Over base) (picardClass : (pullback morphism parameter.hom).Pic) :
    letI := picardFunctorCommGrpObj morphism representation
    picardClassifyingHom morphism representation parameter picardClass =
      representation.homEquiv.symm ((toPicardFunctor morphism).app (.op parameter) picardClass) :=
  rfl

end AlgebraicGeometry
