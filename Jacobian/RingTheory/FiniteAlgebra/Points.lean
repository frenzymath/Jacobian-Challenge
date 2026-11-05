import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Rational points of a finite algebra

Distinct field-valued algebra homomorphisms form a linearly independent family.
If their number equals the algebra dimension, evaluation is bijective. No
reducedness, separability, or characteristic hypothesis is needed.
-/

noncomputable section
set_option autoImplicit false
universe u
namespace AlgHom
section FiniteAlgebra

variable {K A ι : Type u} [Field K] [CommRing A] [Algebra K A]
  [FiniteDimensional K A] [Fintype ι]

/-- A full-dimensional family of distinct rational points separates a finite algebra.
This works in every characteristic and does not assume the algebra is reduced. -/
theorem evaluation_injective_of_card_eq_finrank (g : ι → (A →ₐ[K] K))
    (hg : Function.Injective g) (hcard : Fintype.card ι = Module.finrank K A) :
    Function.Injective (AlgHom.pi g) := by
  have hlin : LinearIndependent K (fun i => (g i).toLinearMap) :=
    (linearIndependent_algHom_toLinearMap K A K).comp g hg
  have hspan : Submodule.span K (Set.range (fun i => (g i).toLinearMap)) = ⊤ :=
    hlin.span_eq_top_of_card_eq_finrank' (by
      simpa only [Subspace.dual_finrank_eq] using hcard)
  intro x y hxy
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff K (x - y)).mp
  intro l
  have hker : Submodule.span K (Set.range (fun i => (g i).toLinearMap)) ≤
      LinearMap.ker (Module.Dual.eval K A (x - y)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change g i (x - y) = 0
    rw [map_sub, show g i x = g i y from congrFun hxy i, sub_self]
  change l ∈ LinearMap.ker (Module.Dual.eval K A (x - y))
  apply hker
  rw [hspan]
  exact Submodule.mem_top

/-- Evaluation identifies the algebra with a product of copies of the field. -/
theorem evaluation_bijective_of_card_eq_finrank (g : ι → (A →ₐ[K] K))
    (hg : Function.Injective g) (hcard : Fintype.card ι = Module.finrank K A) :
    Function.Bijective (AlgHom.pi g) := by
  have hinj := evaluation_injective_of_card_eq_finrank g hg hcard
  refine ⟨hinj, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (AlgHom.pi g).toLinearMap) ?_).mp hinj
  rw [Module.finrank_fintype_fun_eq_card]
  exact hcard.symm

end FiniteAlgebra
end AlgHom
