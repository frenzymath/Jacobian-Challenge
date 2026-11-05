import Jacobian.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-!
# Sheaves of modules as a Grothendieck category

The underlying abelian-sheaf functor detects exactness of filtered colimits.
Sheafifications of free modules on representables form a small separating
family. Together these give the Grothendieck abelian structure.
-/

universe u

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The sheafifications of the free presheaves of modules `R[yoneda X]` on the representable
presheaves form a separating family of sheaves of `R`-modules. -/
lemma isSeparating_sheafification_freeYoneda :
    ObjectProperty.IsSeparating (.ofObj fun X : C ↦ (PresheafOfModules.sheafification
      (𝟙 R.obj)).obj ((PresheafOfModules.free R.obj).obj (yoneda.obj X))) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
  intro M N f g hfg
  refine (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map_injective
    (PresheafOfModules.freeYoneda.isSeparating R.obj _ _ ?_)
  rintro _ ⟨X⟩ a
  apply (adj.homEquiv _ _).symm.injective
  have h := hfg _ (ObjectProperty.ofObj_apply _ X) ((adj.homEquiv _ _).symm a)
  rw [← Adjunction.homEquiv_naturality_right_symm,
    ← Adjunction.homEquiv_naturality_right_symm] at h
  exact h

/-- **Sheaves of modules form a Grothendieck abelian category.** -/
theorem isGrothendieckAbelian : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) := by
  have : HasFilteredColimitsOfSize.{u, u} (SheafOfModules.{u} R) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{u, u} (SheafOfModules.{u} R) :=
    ⟨fun K _ _ ↦ HasExactColimitsOfShape.domain_of_functor K (toSheaf.{u} R)⟩
  have : HasSeparator (SheafOfModules.{u} R) :=
    ⟨_, (isSeparating_sheafification_freeYoneda R).isSeparator_coproduct⟩
  exact {}

end SheafOfModules
