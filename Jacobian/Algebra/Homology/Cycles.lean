import Mathlib.Algebra.Homology.HomologySequence

/-!
# Short exact sequences of cycles

Exactness at the next degree turns adjacent cycles into a short exact
sequence. Chain maps commute with these maps and with reindexing cycles.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HomologicalComplex

open CategoryTheory Limits

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {K : HomologicalComplex C c}

/-- Exactness makes the incoming map to cycles an epimorphism. -/
lemma ExactAt.epi_toCycles {j : ι} (hj : K.ExactAt j) (i : ι) (hi : c.prev j = i) :
    Epi (K.toCycles i j) := by
  subst hi
  exact (K.sc j).exact_iff_epi_toCycles.1 hj

variable (K) in
/-- The short complex of adjacent cycles. -/
@[simps]
noncomputable def cyclesShortComplex (i j : ι) : ShortComplex C :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i j) (by
    rw [← cancel_mono (K.iCycles j), Category.assoc, toCycles_i, iCycles_d, zero_comp])

/-- If `K` is exact at `j` and `c.Rel i j`, then
`0 ⟶ K.cycles i ⟶ K.X i ⟶ K.cycles j ⟶ 0` is a short exact sequence. -/
lemma ExactAt.shortExact_cyclesShortComplex {i j : ι} (hj : K.ExactAt j) (hij : c.Rel i j) :
    (K.cyclesShortComplex i j).ShortExact := by
  have := hj.epi_toCycles i (c.prev_eq' hij)
  refine ShortComplex.ShortExact.mk' ?_ (inferInstanceAs (Mono (K.iCycles i))) this
  let φ : K.cyclesShortComplex i j ⟶ ShortComplex.mk _ _ (K.iCycles_d i j) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles j
      comm₁₂ := by simp [cyclesShortComplex]
      comm₂₃ := by simp [cyclesShortComplex] }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel i j (c.next_eq' hij))

end HomologicalComplex

namespace HomologicalComplex
open CategoryTheory Limits
variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}

section CyclesMap

variable {K L : HomologicalComplex C c} (φ : K ⟶ L)

/-- A chain map commutes with the maps `K.toCycles i j : K.X i ⟶ K.cycles j`. -/
@[reassoc]
lemma toCycles_cyclesMap (i j : ι) :
    K.toCycles i j ≫ cyclesMap φ j = φ.f i ≫ L.toCycles i j := by
  rw [← cancel_mono (L.iCycles j)]
  simp

/-- `cyclesMap` commutes with the identifications `K.cycles a = K.cycles b` for `a = b`. -/
lemma eqToHom_comp_cyclesMap {a b : ι}
    (h : a = b) :
    (eqToHom (by rw [h]) : K.cycles a ⟶ K.cycles b) ≫ cyclesMap φ b =
      cyclesMap φ a ≫ (eqToHom (by rw [h]) : L.cycles a ⟶ L.cycles b) := by
  subst h
  simp

end CyclesMap

end HomologicalComplex
