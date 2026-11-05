import Jacobian.AlgebraicGeometry.Modules.Rigidification
import Jacobian.AlgebraicGeometry.Picard.LocalTriviality
import Jacobian.AlgebraicGeometry.Picard.Normalized

/-!
# Rigidifying representatives of normalized Picard classes

An equality of Picard classes gives an isomorphism between chosen invertible
representatives. Along a section, chosen trivializations can be respected by a
unique such isomorphism whenever the canonical pushforward structure-module
map is an isomorphism. These are the unique transition isomorphisms used in
normalized descent.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {source base : Scheme.{schemeUniverse}}

/-- Equal normalized classes have a unique isomorphism respecting section trivializations. -/
theorem existsUnique_iso_of_normalized_picard_eq (morphism : source ⟶ base)
    (sectionMorphism : base ⟶ source) (sectionCondition : sectionMorphism ≫ morphism = 𝟙 base)
    (parameter : Over base) [IsIso (pushforwardUnitMap (pullback.snd morphism parameter.hom))]
    (firstClass secondClass :
      (picardFunctorNormalized morphism sectionMorphism sectionCondition).toFunctor.obj (.op parameter))
    (equality : firstClass = secondClass)
    (firstTrivialization :
      (Modules.pullback (sectionBaseChange morphism sectionMorphism sectionCondition parameter)).obj
          ((fromSkeleton _).obj firstClass.1.val) ≅ SheafOfModules.unit parameter.left.ringCatSheaf)
    (secondTrivialization :
      (Modules.pullback (sectionBaseChange morphism sectionMorphism sectionCondition parameter)).obj
          ((fromSkeleton _).obj secondClass.1.val) ≅ SheafOfModules.unit parameter.left.ringCatSheaf) :
    ∃! normalizedIso : (fromSkeleton _).obj firstClass.1.val ≅
        (fromSkeleton _).obj secondClass.1.val,
      (Modules.pullback (sectionBaseChange morphism sectionMorphism sectionCondition parameter)).map
          normalizedIso.hom ≫ secondTrivialization.hom = firstTrivialization.hom := by
  obtain ⟨isomorphism⟩ := Pic.eq_iff_nonempty_iso.mp (congrArg Subtype.val equality)
  exact Modules.existsUnique_iso_of_isIso_pushforwardUnitMap (pullback.snd morphism parameter.hom)
    (sectionBaseChange morphism sectionMorphism sectionCondition parameter)
    (sectionBaseChange_snd morphism sectionMorphism sectionCondition parameter)
    firstTrivialization secondTrivialization isomorphism

end AlgebraicGeometry
