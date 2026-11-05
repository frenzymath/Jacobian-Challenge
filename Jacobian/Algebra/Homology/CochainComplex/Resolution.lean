import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Resolutions from augmented complexes

A monic exact augmentation into a nonnegative complex exact in positive degrees
defines a quasi-isomorphism from the object in degree zero.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits Opposite ZeroObject

namespace CochainComplex

/-- A complex `K` augmented by `ε : Z ⟶ K⁰` is a resolution of `Z` as soon as `ε` is a
monomorphism, `Z ⟶ K⁰ ⟶ K¹` is exact and `K` is exact in positive degrees. -/
lemma quasiIso_fromSingle₀Equiv_symm {C : Type*} [Category* C] [Abelian C] {Z : C}
    {K : CochainComplex C ℕ} (ε : Z ⟶ K.X 0) (hε : ε ≫ K.d 0 1 = 0)
    (h₀ : (ShortComplex.mk ε (K.d 0 1) hε).Exact) [Mono ε] (hK : ∀ n, K.ExactAt (n + 1)) :
    QuasiIso ((CochainComplex.fromSingle₀Equiv K Z).symm ⟨ε, hε⟩) := ⟨fun n ↦ by
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2 ⟨h₀, by dsimp; infer_instance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [CochainComplex.fromSingle₀Equiv]) (by simp)
    all_goals first | rfl | exact HomologicalComplex.shape _ _ _ (by simp)
  | succ n =>
    rw [quasiIsoAt_iff_exactAt]
    · exact hK n
    · exact CochainComplex.exactAt_succ_single_obj _ _⟩

end CochainComplex
