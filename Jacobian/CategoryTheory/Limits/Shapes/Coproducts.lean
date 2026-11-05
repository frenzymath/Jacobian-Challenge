import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Coproducts of cokernels

A coproduct of cokernel diagrams is a cokernel diagram, by their universal
properties.
-/

noncomputable section

namespace CategoryTheory.Limits

/-- A coproduct of cokernels is a cokernel: if each `g i : B i ⟶ Z i` is a cokernel of
`f i : A i ⟶ B i`, then `Sigma.map g` is a cokernel of `Sigma.map f`:
```
  ∐ A ──Sigma.map f──▶ ∐ B ──Sigma.map g──▶ ∐ Z
   ▲                    ▲                    ▲
   │ ι i                │ ι i                │ ι i
  A i ───────f i──────▶ B i ──────g i──────▶ Z i
```
-/
noncomputable def isColimitCokernelCoforkSigmaMap {categoryType : Type*} [Category categoryType] [HasZeroMorphisms categoryType]
    {indexType : Type*} {sourceObjects targetObjects quotientObjects : indexType → categoryType} [HasCoproduct sourceObjects] [HasCoproduct targetObjects] [HasCoproduct quotientObjects]
    (firstMaps : ∀ index, sourceObjects index ⟶ targetObjects index) (secondMaps : ∀ index, targetObjects index ⟶ quotientObjects index) (w : ∀ index, firstMaps index ≫ secondMaps index = 0)
    (colimitProofs : ∀ index, IsColimit (CokernelCofork.ofπ (secondMaps index) (w index))) :
    IsColimit (CokernelCofork.ofπ (Sigma.map secondMaps) (show Sigma.map firstMaps ≫ Sigma.map secondMaps = 0 by
      ext index
      simp [reassoc_of% (w index)])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun candidate hk ↦ Sigma.desc fun index ↦ (colimitProofs index).desc (CokernelCofork.ofπ (Sigma.ι targetObjects index ≫ candidate) (by
      rw [← Sigma.ι_map_assoc, hk, comp_zero])))
    (fun candidate hk ↦ by
      ext index
      simp only [Sigma.ι_map_assoc, colimit.ι_desc, Cofan.mk_ι_app]
      exact (colimitProofs index).fac _ WalkingParallelPair.one)
    (fun candidate hk otherCandidate hm ↦ by
      ext index
      simp only [colimit.ι_desc, Cofan.mk_ι_app]
      refine Cofork.IsColimit.hom_ext (colimitProofs index) ?_
      refine Eq.trans ?_
        ((colimitProofs index).fac (CokernelCofork.ofπ (Sigma.ι targetObjects index ≫ candidate) _) WalkingParallelPair.one).symm
      simp [← hm])

end CategoryTheory.Limits
