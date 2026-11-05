import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Pointwise finite sums of morphisms of abelian groups.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open CategoryTheory

/-- A finite sum of morphisms of abelian groups is computed pointwise. -/
lemma AddCommGrpCat.sum_apply {moduleSheaf exponent : AddCommGrpCat} {indexType : Type*} (morphism : indexType → (moduleSheaf ⟶ exponent))
    (sectionValue : Finset indexType) (element : moduleSheaf) : (∑ index ∈ sectionValue, morphism index) element = ∑ index ∈ sectionValue, morphism index element := by
  rw [← AddMonoidHom.finsetSum_apply]
  exact congr($(map_sum AddCommGrpCat.homAddEquiv morphism sectionValue) element)
