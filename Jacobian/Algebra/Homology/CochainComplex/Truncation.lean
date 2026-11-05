import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Factoring resolutions through quotient truncation

A bounded-above resolution of a nonnegative complex factors through its
canonical nonnegative quotient truncation. Both maps in the factorization are
quasi-isomorphisms, and the truncation retains the upper bound.
-/

noncomputable section

open CategoryTheory Limits

namespace CochainComplex

variable {A : Type*} [Category* A] [Abelian A]

/-- A bounded-above resolution of a nonnegative complex factors through its
nonnegative quotient truncation, with the canonical degreewise identifications. -/
theorem exists_truncGE_quasiIso_factorization
    (C Q : CochainComplex A ℤ) (d : ℕ)
    (hCge : C.IsStrictlyGE 0) (hQle : Q.IsStrictlyLE d)
    (e : Q ⟶ C) (he : QuasiIso e) :
    ∃ p : Q.truncGE 0 ⟶ C,
      QuasiIso (Q.πTruncGE 0) ∧ QuasiIso p ∧
      Q.πTruncGE 0 ≫ p = e ∧
      (Q.truncGE 0).IsStrictlyGE 0 ∧ (Q.truncGE 0).IsStrictlyLE d ∧
      Nonempty ((Q.truncGE 0).X 0 ≅ Q.opcycles 0) ∧
      ∀ (n : ℤ), 0 < n → Nonempty ((Q.truncGE 0).X n ≅ Q.X n) := by
  letI : C.IsStrictlyGE 0 := hCge
  letI : Q.IsStrictlyLE (d : ℤ) := hQle
  letI : QuasiIso e := he
  letI : Q.IsGE 0 :=
    (HomologicalComplex.isSupported_iff_of_quasiIso e
      (ComplexShape.embeddingUpIntGE 0)).mpr inferInstance
  letI : QuasiIso (CochainComplex.truncGEMap e 0) := by
    rw [CochainComplex.quasiIso_truncGEMap_iff]
    intro n hn
    infer_instance
  let p := CochainComplex.truncGEMap e 0 ≫ inv (C.πTruncGE 0)
  refine ⟨p, inferInstance, inferInstance, ?_, inferInstance, inferInstance,
    ⟨Q.truncGEXIsoOpcycles 0⟩, ?_⟩
  · dsimp [p]
    rw [← Category.assoc, CochainComplex.πTruncGE_naturality]
    simp
  · intro n hn
    exact ⟨Q.truncGEXIso 0 n hn⟩

end CochainComplex
