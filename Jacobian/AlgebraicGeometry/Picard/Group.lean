import Jacobian.AlgebraicGeometry.Picard.Pullback
import Jacobian.AlgebraicGeometry.Modules.Dual
import Mathlib.Algebra.Group.Hom.Defs

/-!
# The Picard group

Tensor product makes the Picard classes of a scheme into a commutative group.
The structure sheaf represents the identity, and the internal-hom dual
represents the inverse. Pullback of module sheaves induces a group homomorphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Pic

variable {scheme source target : Scheme.{schemeUniverse}}

/-- The unit Picard class is represented by the structure sheaf. -/
instance : One scheme.Pic :=
  ⟨mk (𝟙_ scheme.Modules)⟩

/-- Multiplication of Picard classes is induced by tensor product. -/
instance : Mul scheme.Pic :=
  ⟨fun firstClass secondClass ↦ mk
    ((fromSkeleton scheme.Modules).obj firstClass.val ⊗
      (fromSkeleton scheme.Modules).obj secondClass.val)⟩

/-- Inversion of Picard classes is induced by the internal-hom dual. -/
instance : Inv scheme.Pic :=
  ⟨fun picardClass ↦ mk ((fromSkeleton scheme.Modules).obj picardClass.val)ᵛ⟩

/-- The unit Picard class is the class of the structure sheaf. -/
lemma one_eq_mk_unit : (1 : scheme.Pic) = mk (SheafOfModules.unit scheme.ringCatSheaf) :=
  rfl

/-- A product is the class of the tensor product of the chosen representatives. -/
lemma mul_def (firstClass secondClass : scheme.Pic) :
    firstClass * secondClass = mk
      ((fromSkeleton scheme.Modules).obj firstClass.val ⊗
        (fromSkeleton scheme.Modules).obj secondClass.val) :=
  rfl

/-- An inverse is the class of the dual of the chosen representative. -/
lemma inv_def (picardClass : scheme.Pic) :
    picardClass⁻¹ = mk ((fromSkeleton scheme.Modules).obj picardClass.val)ᵛ :=
  rfl

/-- The chosen representative of a product is the tensor product of representatives. -/
def mulIso (firstClass secondClass : scheme.Pic) :
    (fromSkeleton scheme.Modules).obj (firstClass * secondClass).val ≅
      (fromSkeleton scheme.Modules).obj firstClass.val ⊗
        (fromSkeleton scheme.Modules).obj secondClass.val :=
  mkIso _

/-- The chosen representative of the unit class is the structure sheaf. -/
def oneIso : (fromSkeleton scheme.Modules).obj (1 : scheme.Pic).val ≅ 𝟙_ scheme.Modules :=
  mkIso _

/-- Tensor product and dualization give the commutative group structure on Picard classes. -/
instance instCommGroup : CommGroup scheme.Pic where
  mul_assoc firstClass secondClass thirdClass := by
    exact eq_iff_nonempty_iso.2 ⟨mulIso _ _ ≪≫ whiskerRightIso (mulIso _ _) _ ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso _ (mulIso _ _).symm ≪≫ (mulIso _ _).symm⟩
  one_mul picardClass := by
    exact eq_iff_nonempty_iso.2 ⟨mulIso _ _ ≪≫ whiskerRightIso oneIso _ ≪≫ λ_ _⟩
  mul_one picardClass := by
    exact eq_iff_nonempty_iso.2 ⟨mulIso _ _ ≪≫ whiskerLeftIso _ oneIso ≪≫ ρ_ _⟩
  inv_mul_cancel picardClass := by
    exact eq_iff_nonempty_iso.2 ⟨mulIso _ _ ≪≫ whiskerRightIso (mkIso _) _ ≪≫ β_ _ _ ≪≫
      Modules.tensorObjDualIsoUnit ((fromSkeleton scheme.Modules).obj picardClass.val) ≪≫
        oneIso.symm⟩
  mul_comm firstClass secondClass := by
    exact eq_iff_nonempty_iso.2 ⟨mulIso _ _ ≪≫ β_ _ _ ≪≫ (mulIso _ _).symm⟩

/-- The class of a tensor product is the product of the two classes. -/
@[simp]
lemma mk_tensorObj (moduleSheaf targetSheaf : scheme.Modules)
    [moduleSheaf.IsInvertible] [targetSheaf.IsInvertible] :
    mk (moduleSheaf ⊗ targetSheaf) = mk moduleSheaf * mk targetSheaf :=
  (mk_eq_mk_iff _ _).2 ⟨(mkIso moduleSheaf).symm ⊗ᵢ (mkIso targetSheaf).symm⟩

/-- Dualization of line bundles induces inversion of Picard classes. -/
@[simp]
lemma mk_dual (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible] :
    mk moduleSheafᵛ = (mk moduleSheaf)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← mk_tensorObj]
  exact (mk_eq_mk_iff _ _).2 ⟨β_ _ _ ≪≫ Modules.tensorObjDualIsoUnit moduleSheaf⟩

/-- Pullback of Picard classes preserves products. -/
@[simp]
lemma map_mul (morphism : source ⟶ target) (firstClass secondClass : target.Pic) :
    map morphism (firstClass * secondClass) = map morphism firstClass * map morphism secondClass :=
  eq_iff_nonempty_iso.2 ⟨fromSkeletonToSkeletonIso _ ≪≫
    (Modules.pullback morphism).mapIso (mulIso firstClass secondClass) ≪≫
    Modules.pullbackTensorObjIso morphism ((fromSkeleton target.Modules).obj firstClass.val)
      ((fromSkeleton target.Modules).obj secondClass.val) ≪≫
    ((fromSkeletonToSkeletonIso _).symm ⊗ᵢ (fromSkeletonToSkeletonIso _).symm) ≪≫
    (mulIso (map morphism firstClass) (map morphism secondClass)).symm⟩

/-- Pullback of Picard classes preserves the identity. -/
@[simp]
lemma map_one (morphism : source ⟶ target) : map morphism (1 : target.Pic) = 1 :=
  map_mk_unit morphism

/-- Pullback on Picard groups as a group homomorphism. -/
def mapHom (morphism : source ⟶ target) : target.Pic →* source.Pic :=
  MonoidHom.mk' (map morphism) (map_mul morphism)

/-- The pullback homomorphism acts by pullback of representatives. -/
@[simp]
lemma mapHom_apply (morphism : source ⟶ target) (picardClass : target.Pic) :
    mapHom morphism picardClass = map morphism picardClass :=
  rfl

end AlgebraicGeometry.Scheme.Pic
