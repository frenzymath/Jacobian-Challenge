import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Isomorphisms in the first variable of Ext

Precomposition with an isomorphism induces an additive equivalence of Ext groups.
-/

noncomputable section

universe objectUniverse morphismUniverse extUniverse

namespace CategoryTheory.Abelian.Ext

variable {category : Type objectUniverse} [Category.{morphismUniverse} category]
  [Abelian category] [HasExt.{extUniverse} category]
  {source target : category}

/-- Precomposition with an isomorphism is an additive equivalence on Ext. -/
def precompAddEquiv (isomorphism : source ≅ target) (coefficient : category) (degree : ℕ) :
    Ext target coefficient degree ≃+ Ext source coefficient degree where
  __ := (Ext.mk₀ isomorphism.hom).precomp coefficient (zero_add degree)
  invFun := (Ext.mk₀ isomorphism.inv).precomp coefficient (zero_add degree)
  left_inv _ := by simp [Ext.mk₀_comp_mk₀_assoc]
  right_inv _ := by simp [Ext.mk₀_comp_mk₀_assoc]

end CategoryTheory.Abelian.Ext
