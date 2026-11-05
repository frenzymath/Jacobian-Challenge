import Jacobian.AlgebraicGeometry.Modules.Invertible
import Mathlib.CategoryTheory.Skeletal

/-!
# Picard classes of a scheme

The Picard classes of a scheme are the isomorphism classes of its invertible
module sheaves, realized inside the skeleton of the category of module sheaves.
Two invertible module sheaves define the same class exactly when they are
isomorphic, and every class has an invertible representative.

The group structure induced by tensor product is separate from this construction.
-/

noncomputable section

universe schemeUniverse

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {scheme : Scheme.{schemeUniverse}}

/-- The chosen representative of an invertible module sheaf's skeleton class is invertible. -/
lemma _root_.SheafOfModules.IsInvertible.fromSkeleton_toSkeleton
    (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible] :
    ((fromSkeleton scheme.Modules).obj (toSkeleton moduleSheaf)).IsInvertible :=
  SheafOfModules.IsInvertible.of_iso.{schemeUniverse, schemeUniverse, schemeUniverse}
    (fromSkeletonToSkeletonIso moduleSheaf).symm

variable (scheme) in
/-- Isomorphism classes of invertible module sheaves on a scheme. -/
def Pic : Type (schemeUniverse + 1) :=
  { skeletonClass : Skeleton scheme.Modules //
      ((fromSkeleton scheme.Modules).obj skeletonClass).IsInvertible }

namespace Pic

/-- The skeleton class underlying a Picard class. -/
def val (picardClass : scheme.Pic) : Skeleton scheme.Modules :=
  Subtype.val picardClass

/-- The chosen module sheaf representing a Picard class is invertible. -/
instance isInvertible (picardClass : scheme.Pic) :
    ((fromSkeleton scheme.Modules).obj picardClass.val).IsInvertible :=
  Subtype.property picardClass

/-- Picard classes are determined by their underlying skeleton classes. -/
@[ext]
lemma ext {firstClass secondClass : scheme.Pic}
    (equality : firstClass.val = secondClass.val) : firstClass = secondClass :=
  Subtype.ext equality

/-- The Picard class of an invertible module sheaf. -/
def mk (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible] : scheme.Pic :=
  Subtype.mk
    (p := fun skeletonClass ↦ ((fromSkeleton scheme.Modules).obj skeletonClass).IsInvertible)
    (toSkeleton moduleSheaf) (SheafOfModules.IsInvertible.fromSkeleton_toSkeleton moduleSheaf)

/-- The skeleton class of an invertible module sheaf's Picard class. -/
@[simp]
lemma val_mk (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible] :
    (mk moduleSheaf).val = toSkeleton moduleSheaf :=
  rfl

/-- The chosen representative of a module sheaf's Picard class is isomorphic to that sheaf. -/
def mkIso (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible] :
    (fromSkeleton scheme.Modules).obj (mk moduleSheaf).val ≅ moduleSheaf :=
  fromSkeletonToSkeletonIso moduleSheaf

/-- Invertible module sheaves have the same Picard class exactly when they are isomorphic. -/
lemma mk_eq_mk_iff (moduleSheaf targetSheaf : scheme.Modules)
    [moduleSheaf.IsInvertible] [targetSheaf.IsInvertible] :
    mk moduleSheaf = mk targetSheaf ↔ Nonempty (moduleSheaf ≅ targetSheaf) := by
  rw [← toSkeleton_eq_toSkeleton_iff]
  exact ⟨fun equality ↦ congrArg val equality, fun equality ↦ ext equality⟩

/-- Picard classes agree exactly when their chosen representatives are isomorphic. -/
lemma eq_iff_nonempty_iso {firstClass secondClass : scheme.Pic} :
    firstClass = secondClass ↔
      Nonempty ((fromSkeleton scheme.Modules).obj firstClass.val ≅
        (fromSkeleton scheme.Modules).obj secondClass.val) := by
  rw [Pic.ext_iff, ← toSkeleton_eq_toSkeleton_iff, toSkeleton_fromSkeleton_obj,
    toSkeleton_fromSkeleton_obj]

/-- Every Picard class is the class of an invertible module sheaf. -/
lemma exists_mk_eq (picardClass : scheme.Pic) :
    ∃ (moduleSheaf : scheme.Modules) (invertible : moduleSheaf.IsInvertible),
      @mk scheme moduleSheaf invertible = picardClass := by
  refine ⟨(fromSkeleton scheme.Modules).obj picardClass.val, picardClass.isInvertible, ?_⟩
  exact ext (toSkeleton_fromSkeleton_obj picardClass.val)

/-- A Picard class is the class of its chosen representative. -/
@[simp]
lemma mk_fromSkeleton (picardClass : scheme.Pic) :
    mk ((fromSkeleton scheme.Modules).obj picardClass.val) = picardClass :=
  ext (toSkeleton_fromSkeleton_obj picardClass.val)

end Pic

end AlgebraicGeometry.Scheme
