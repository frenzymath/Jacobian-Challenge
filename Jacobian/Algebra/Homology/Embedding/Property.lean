import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Properties of terms of extended complexes

Properties containing zero and stable under isomorphisms pass termwise to an extended complex.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HomologicalComplex

open CategoryTheory Limits

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

/-- If `P` contains zero objects and is closed under isomorphisms and all terms of `K` satisfy
`P`, then all terms of `K.extend e` satisfy `P`. -/
lemma prop_extend_X (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    {K : HomologicalComplex C c} (e : c.Embedding c') (hK : ∀ i, P (K.X i)) (i' : ι') :
    P ((K.extend e).X i') := by
  by_cases h : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := h
    exact P.prop_of_iso (K.extendXIso e hi).symm (hK i)
  · exact P.prop_of_isZero (K.isZero_extend_X e i' (by simpa using h))

end HomologicalComplex
