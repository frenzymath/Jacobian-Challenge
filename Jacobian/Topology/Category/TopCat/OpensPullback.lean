import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.Topology.Category.TopCat.Opens

/-!
# Inverse image of open subsets

Inverse image of open subsets is final and preserves finite products.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace TopologicalSpace.Opens

variable {X Y : TopCat.{u}}

instance (f : X ⟶ Y) : (Opens.map f).Final where
  out U := isConnected_of_isTerminal _ (IsTerminal.ofUniqueHom
    (X := StructuredArrow.mk (S := U) (Y := (⊤ : Opens Y))
      (homOfLE (by simp) : U ⟶ (Opens.map f).obj ⊤))
    (fun _ ↦ StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _))
    (fun _ _ ↦ StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)))

variable (X) in
lemma terminal_eq_top : (⊤_ (Opens X)) = ⊤ :=
  le_antisymm le_top (leOfHom (terminalIsTerminal.from ⊤))

lemma isIso_prodComparison_map (f : X ⟶ Y) (U V : Opens Y) :
    IsIso (prodComparison (Opens.map f) U V) :=
  ⟨homOfLE (by rw [CompleteLattice.prod_eq_inf, CompleteLattice.prod_eq_inf]; exact le_rfl),
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Taking preimages of open sets along a continuous map preserves binary products, i.e.
binary intersections. -/
lemma preservesBinaryProducts_map (f : X ⟶ Y) :
    PreservesLimitsOfShape (Discrete WalkingPair) (Opens.map f) := by
  letI (U V : Opens Y) := isIso_prodComparison_map f U V
  exact preservesBinaryProducts_of_isIso_prodComparison _

lemma isIso_terminalComparison_map (f : X ⟶ Y) :
    IsIso (terminalComparison (Opens.map f)) :=
  ⟨homOfLE (by rw [terminal_eq_top, terminal_eq_top]; exact le_of_eq (Opens.map_top f).symm),
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Taking preimages of open sets along a continuous map preserves the terminal object. -/
lemma preservesTerminal_map (f : X ⟶ Y) :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (Opens.map f) := by
  letI := isIso_terminalComparison_map f
  have : PreservesLimit (Functor.empty.{0} (Opens Y)) (Opens.map f) :=
    PreservesTerminal.of_iso_comparison _
  exact preservesLimitsOfShape_pempty_of_preservesTerminal _

end TopologicalSpace.Opens

end
