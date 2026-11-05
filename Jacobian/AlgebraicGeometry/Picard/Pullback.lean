import Jacobian.AlgebraicGeometry.Picard.Basic

/-!
# Pullback of Picard classes

Pullback of invertible module sheaves induces a contravariant map on Picard
classes. These maps preserve the class of the structure sheaf and satisfy the
identity and composition laws.
-/

noncomputable section

universe schemeUniverse

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Pic

variable {source target thirdScheme : Scheme.{schemeUniverse}}

/-- Pullback of Picard classes along a scheme morphism. -/
def map (morphism : source ⟶ target) (picardClass : target.Pic) : source.Pic :=
  mk ((Modules.pullback morphism).obj ((fromSkeleton target.Modules).obj picardClass.val))

/-- The underlying skeleton class of a pullback is the class of the pulled-back representative. -/
@[simp]
lemma val_map (morphism : source ⟶ target) (picardClass : target.Pic) :
    (map morphism picardClass).val =
      toSkeleton ((Modules.pullback morphism).obj
        ((fromSkeleton target.Modules).obj picardClass.val)) :=
  rfl

/-- Pullback of a represented class is represented by the pulled-back sheaf. -/
@[simp]
lemma map_mk (morphism : source ⟶ target) (moduleSheaf : target.Modules)
    [moduleSheaf.IsInvertible] :
    map morphism (mk moduleSheaf) = mk ((Modules.pullback morphism).obj moduleSheaf) :=
  (mk_eq_mk_iff _ _).2 ⟨(Modules.pullback morphism).mapIso (mkIso moduleSheaf)⟩

/-- Identity pullback fixes every Picard class. -/
@[simp]
lemma map_id (picardClass : source.Pic) : map (𝟙 source) picardClass = picardClass := by
  refine ext ?_
  rw [val_map]
  conv_rhs => rw [← toSkeleton_fromSkeleton_obj picardClass.val]
  exact congr_toSkeleton_of_iso ((Modules.pullbackId source).app _)

/-- Pullback of Picard classes is contravariantly compatible with composition. -/
lemma map_comp (firstMorphism : source ⟶ target) (secondMorphism : target ⟶ thirdScheme)
    (picardClass : thirdScheme.Pic) :
    map (firstMorphism ≫ secondMorphism) picardClass =
      map firstMorphism (map secondMorphism picardClass) := by
  refine ext ?_
  simp only [val_map]
  exact congr_toSkeleton_of_iso
    (((Modules.pullbackComp firstMorphism secondMorphism).app _).symm ≪≫
      (Modules.pullback firstMorphism).mapIso (fromSkeletonToSkeletonIso _).symm)

/-- Pullback preserves the class of the structure sheaf. -/
@[simp]
lemma map_mk_unit (morphism : source ⟶ target) :
    map morphism (mk (SheafOfModules.unit target.ringCatSheaf)) =
      mk (SheafOfModules.unit source.ringCatSheaf) := by
  exact ext (congr_toSkeleton_of_iso
    ((Modules.pullback morphism).mapIso (fromSkeletonToSkeletonIso _) ≪≫
      Modules.pullbackObjUnitIso morphism))

end AlgebraicGeometry.Scheme.Pic
