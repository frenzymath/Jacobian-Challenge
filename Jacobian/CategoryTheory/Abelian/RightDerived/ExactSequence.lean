import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Jacobian.CategoryTheory.Abelian.RightDerived.Comparison
import Jacobian.CategoryTheory.Abelian.Injective.Resolution

/-!
# The long exact sequence of right derived functors

A short exact sequence gives connecting morphisms for right derived functors, with exactness at both neighboring terms.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CategoryTheory

open Limits Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D]

namespace ShortComplex.ShortExact

variable (F : C ⥤ D) [F.Additive] {S : ShortComplex C} (hS : S.ShortExact)

include hS

/-- The long exact sequence of the right derived functors of `F`: a short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` gives a connecting morphism `δ : R^q F C ⟶ R^{q+1} F A` such that
```
  R^q F B ──R^q F g──▶ R^q F C ──δ──▶ R^{q+1} F A ──R^{q+1} F f──▶ R^{q+1} F B
```
is exact at `R^q F C` and at `R^{q+1} F A`. The connecting morphism is the one of the long
exact homology sequence of the distinguished triangle `R⁺F(A[0]) ⟶ R⁺F(B[0]) ⟶ R⁺F(C[0]) ⟶`
in the bounded below derived category of `D`. -/
theorem exists_rightDerived_δ_exact (q : ℕ) :
    ∃ (δ : (F.rightDerived q).obj S.X₃ ⟶ (F.rightDerived (q + 1)).obj S.X₁)
      (w₁ : (F.rightDerived q).map S.g ≫ δ = 0) (w₂ : δ ≫ (F.rightDerived (q + 1)).map S.f = 0),
      (ShortComplex.mk _ _ w₁).Exact ∧ (ShortComplex.mk _ _ w₂).Exact := by
  have := enoughInjectives_of_hasInjectiveResolutions (C := C)
  let _ := HasDerivedCategory.standard C
  let _ := HasDerivedCategory.standard D
  let s := DerivedCategory.Plus.singleFunctor C 0
  let i := DerivedCategory.Plus.singleFunctorιIso C 0
  let δT : s.obj S.X₃ ⟶ (s.obj S.X₁)⟦(1 : ℤ)⟧ :=
    DerivedCategory.Plus.ι.preimage (i.hom.app S.X₃ ≫ hS.singleδ ≫
      (i.inv.app S.X₁)⟦(1 : ℤ)⟧' ≫ (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app _)
  let T : Triangle (DerivedCategory.Plus C) := Triangle.mk (s.map S.f) (s.map S.g) δT
  have hT : T ∈ distTriang _ := by
    rw [← DerivedCategory.Plus.ι.map_distinguished_iff]
    refine isomorphic_distinguished _ hS.singleTriangle_distinguished _ ?_
    refine Triangle.isoMk _ _ (i.app S.X₁) (i.app S.X₂) (i.app S.X₃) ?_ ?_ ?_
    · exact i.hom.naturality S.f
    · exact i.hom.naturality S.g
    · change (DerivedCategory.Plus.ι.map δT ≫
        (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app _) ≫
          (i.hom.app S.X₁)⟦(1 : ℤ)⟧' = i.hom.app S.X₃ ≫ hS.singleδ
      rw [Functor.map_preimage]
      simp only [Category.assoc]
      erw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id,
        Category.comp_id]
  let T' := (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj T
  have hT' : T' ∈ distTriang _ := Functor.map_distinguished _ _ hT
  let e (n : ℕ) := F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n
  have h : (q : ℤ) + 1 = ((q + 1 : ℕ) : ℤ) := by push_cast; rfl
  let δ' := DerivedCategory.HomologySequence.δ T' q _ h
  refine ⟨(e q).inv.app S.X₃ ≫ δ' ≫ (e (q + 1)).hom.app S.X₁, ?_, ?_, ?_, ?_⟩
  · refine ((e q).inv.naturality_assoc S.g _).trans ?_
    refine (congrArg ((e q).inv.app S.X₂ ≫ ·)
      (DerivedCategory.HomologySequence.comp_δ_assoc T' hT' q _ h _)).trans ?_
    erw [zero_comp, comp_zero]
  · rw [Category.assoc]
    refine (congrArg ((e q).inv.app S.X₃ ≫ ·) (Category.assoc δ' _ _)).trans ?_
    refine (congrArg (fun x ↦ (e q).inv.app S.X₃ ≫ δ' ≫ x)
      ((e (q + 1)).hom.naturality S.f).symm).trans ?_
    refine (congrArg ((e q).inv.app S.X₃ ≫ ·)
      (DerivedCategory.HomologySequence.δ_comp_assoc T' hT' q _ h _)).trans ?_
    erw [zero_comp, comp_zero]
  · refine (ShortComplex.exact_iff_of_iso ?_).1
      (DerivedCategory.HomologySequence.exact₃ T' hT' q _ h)
    exact ShortComplex.isoMk ((e q).app S.X₂) ((e q).app S.X₃) ((e (q + 1)).app S.X₁)
      ((e q).hom.naturality S.g).symm (Iso.hom_inv_id_app_assoc (e q) S.X₃ _)
  · refine (ShortComplex.exact_iff_of_iso ?_).1
      (DerivedCategory.HomologySequence.exact₁ T' hT' q _ h)
    exact ShortComplex.isoMk ((e q).app S.X₃) ((e (q + 1)).app S.X₁) ((e (q + 1)).app S.X₂)
      (Iso.hom_inv_id_app_assoc (e q) S.X₃ _) ((e (q + 1)).hom.naturality S.f).symm

end ShortComplex.ShortExact

end CategoryTheory
