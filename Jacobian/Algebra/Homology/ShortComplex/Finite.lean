import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite modules in exact sequences

Over a Noetherian ring, the middle term of an exact sequence is finite when
both outer terms are finite.
-/

open CategoryTheory

universe u v

namespace CategoryTheory.ShortComplex

variable {baseRing : Type u} [CommRing baseRing] [IsNoetherianRing baseRing]
  {shortComplex : ShortComplex (ModuleCat.{v} baseRing)}

/-- Finiteness of the outer terms of an exact sequence implies finiteness of its middle term. -/
lemma Exact.moduleFinite_X₂ (exact_sequence : shortComplex.Exact)
    [Module.Finite baseRing shortComplex.X₁] [Module.Finite baseRing shortComplex.X₃] :
    Module.Finite baseRing shortComplex.X₂ := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at exact_sequence
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker shortComplex.g.hom
    (IsNoetherian.noetherian _) ?_⟩
  rw [top_inf_eq, ← exact_sequence, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

end CategoryTheory.ShortComplex
