import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The long exact sequence of native Ext sheaf cohomology and its degree-zero H.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe cohomologyUniverse' cohomologyUniverse indexUniverse' indexUniverse coefficientUniverse' coefficientUniverse
namespace CategoryTheory
open Abelian Limits AddCommGrpCat

section Connecting

variable {category : Type coefficientUniverse} [Category.{indexUniverse} category] {topology : GrothendieckTopology category}
  [HasSheafify topology AddCommGrpCat.{cohomologyUniverse}] [HasExt.{cohomologyUniverse'} (Sheaf topology AddCommGrpCat.{cohomologyUniverse})]
  {sequence : ShortComplex (Sheaf topology AddCommGrpCat.{cohomologyUniverse})} (hS : sequence.ShortExact)

/-- The connecting homomorphism `Hⁿ(S.X₃) → Hⁿ⁺¹(S.X₁)` of the long exact cohomology sequence
of a short exact sequence of abelian sheaves: composition with the extension class of `S`. -/
noncomputable def Sheaf.H.δSucc (size : ℕ) : H sequence.X₃ size →+ H sequence.X₁ (size + 1) :=
  hS.extClass.postcomp _ rfl

lemma Sheaf.H.δSucc_apply (size : ℕ) (element : H sequence.X₃ size) : H.δSucc hS size element = element.comp hS.extClass rfl :=
  rfl

/-- The long exact cohomology sequence is exact at `Hⁿ(S.X₃)`: the kernel of the connecting
homomorphism `Hⁿ(S.X₃) → Hⁿ⁺¹(S.X₁)` is the image of `Hⁿ(S.X₂) → Hⁿ(S.X₃)`. -/
lemma Sheaf.H.exact_map_δSucc (size : ℕ) : Function.Exact (H.map sequence.g size) (H.δSucc hS size) :=
  (ShortComplex.ab_exact_iff_function_exact _).1 (Ext.covariant_sequence_exact₃' _ hS size _ rfl)

/-- The long exact cohomology sequence is exact at `Hⁿ⁺¹(S.X₁)`: the kernel of
`Hⁿ⁺¹(S.X₁) → Hⁿ⁺¹(S.X₂)` is the image of the connecting homomorphism. -/
lemma Sheaf.H.exact_δSucc_map (size : ℕ) : Function.Exact (H.δSucc hS size) (H.map sequence.f (size + 1)) :=
  (ShortComplex.ab_exact_iff_function_exact _).1 (Ext.covariant_sequence_exact₁' _ hS size _ rfl)

/-- The connecting homomorphism is natural in the short exact sequence. -/
lemma Sheaf.H.map_δSucc {sequence' : ShortComplex (Sheaf topology AddCommGrpCat.{cohomologyUniverse})}
    (hS' : sequence'.ShortExact) (coefficientMap : sequence ⟶ sequence') (size : ℕ) (element : H sequence.X₃ size) :
    H.map coefficientMap.τ₁ (size + 1) (H.δSucc hS size element) = H.δSucc hS' size (H.map coefficientMap.τ₃ size element) := by
  rw [H.δSucc_apply, H.δSucc_apply, H.map_apply, H.map_apply,
    Ext.comp_assoc_of_third_deg_zero, hS.extClass_naturality hS' coefficientMap,
    Ext.comp_assoc_of_second_deg_zero]

/-- The connecting homomorphism `Hⁿ(S.X₃) → Hⁿ⁺¹(S.X₁)` is surjective when
`Hⁿ⁺¹(S.X₂) = 0`. -/
lemma Sheaf.H.δSucc_surjective (size : ℕ) [Subsingleton (H sequence.X₂ (size + 1))] :
    Function.Surjective (H.δSucc hS size) := by
  intro element
  obtain ⟨otherElement, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS element (Subsingleton.elim _ _) rfl
  exact ⟨otherElement, rfl⟩

/-- The connecting homomorphism `Hⁿ(S.X₃) → Hⁿ⁺¹(S.X₁)`, as a morphism between the values of
the cohomology functors `CategoryTheory.Sheaf.functorH`. -/
noncomputable def Sheaf.functorHδ (size : ℕ) :
    (functorH.{cohomologyUniverse'} topology size).obj sequence.X₃ ⟶ (functorH.{cohomologyUniverse'} topology (size + 1)).obj sequence.X₁ :=
  AddCommGrpCat.ofHom (H.δSucc hS size)

lemma Sheaf.functorHδ_apply (size : ℕ) (element : H sequence.X₃ size) : functorHδ hS size element = H.δSucc hS size element :=
  rfl

@[reassoc]
lemma Sheaf.functorHδ_naturality (size : ℕ) {sequence' : ShortComplex (Sheaf topology AddCommGrpCat.{cohomologyUniverse})}
    (hS' : sequence'.ShortExact) (coefficientMap : sequence ⟶ sequence') :
    functorHδ hS size ≫ (functorH.{cohomologyUniverse'} topology (size + 1)).map coefficientMap.τ₁ =
      (functorH.{cohomologyUniverse'} topology size).map coefficientMap.τ₃ ≫ functorHδ hS' size := by
  ext element
  exact H.map_δSucc hS hS' coefficientMap size element

lemma Sheaf.functorHδ_eq_zero_iff (size : ℕ) (element : H sequence.X₃ size) :
    functorHδ hS size element = 0 ↔ element ∈ ((functorH.{cohomologyUniverse'} topology size).map sequence.g).hom.range :=
  ((H.exact_map_δSucc hS size) element).trans (by rfl)

lemma Sheaf.functorHδ_surjective (size : ℕ) [Subsingleton (H sequence.X₂ (size + 1))] :
    Function.Surjective (functorHδ hS size) :=
  H.δSucc_surjective hS size

end Connecting

section Zero

variable {category : Type coefficientUniverse} [Category.{indexUniverse} category] (topology : GrothendieckTopology category)
  [HasSheafify topology AddCommGrpCat.{cohomologyUniverse}] [HasExt.{cohomologyUniverse} (Sheaf topology AddCommGrpCat.{cohomologyUniverse})] {terminalObject : category}
  (hT : IsTerminal terminalObject)

/-- `H⁰` is the functor of sections over a terminal object. -/
noncomputable def Sheaf.functorHZeroIso :
    functorH.{cohomologyUniverse} topology 0 ≅ sheafToPresheaf topology AddCommGrpCat.{cohomologyUniverse} ⋙
      (evaluation categoryᵒᵖ AddCommGrpCat.{cohomologyUniverse}).obj (Opposite.op terminalObject) :=
  NatIso.ofComponents (fun sheaf ↦ (H.equiv₀ sheaf hT).toAddCommGrpIso) fun coefficientMap ↦ by
    ext element
    exact (H.equiv₀_naturality (hT := hT) coefficientMap element).symm

end Zero
end CategoryTheory
