import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Flatness of opcycles

In a braided closed abelian monoidal category, tensoring with an opcycle
preserves finite limits if the two adjacent terms have this property and
tensoring the complex with every object is exact in the preceding degree.
The proof lifts a section through the opcycle cokernel, corrects it by a
boundary, and uses exactness for the adjacent terms.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [MonoidalPreadditive C]

/-- Tensoring with the actual degree-`a` opcycle preserves finite limits if the
adjacent terms have that property and tensoring the complex with every object
is exact in degree `a - 1`. -/
theorem preservesFiniteLimits_tensorLeft_opcycles_of_exactAt
    (P : CochainComplex C ℤ) (a : ℤ)
    (h₁ : PreservesFiniteLimits (tensorLeft (P.X (a - 1))))
    (h₂ : PreservesFiniteLimits (tensorLeft (P.X a)))
    (hP : ∀ F : C,
      (((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1)) :
    PreservesFiniteLimits (tensorLeft (P.opcycles a)) := by
  have : PreservesFiniteLimits (tensorLeft (P.X (a - 1))) := h₁
  have : PreservesFiniteLimits (tensorLeft (P.X a)) := h₂
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  refine ⟨hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance, ?_⟩
  have := hS.mono_f
  have := hS.epi_g
  dsimp
  set d := P.d (a - 1) a
  set d' := P.d (a - 1 - 1) (a - 1)
  set p := P.pOpcycles a
  have hdp : d ≫ p = 0 := P.d_pOpcycles _ _
  have (F : C) : PreservesColimitsOfSize.{0, 0} (tensorRight F) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)
  have hcok (F : C) : (ShortComplex.mk (d ▷ F) (p ▷ F)
      (by rw [← comp_whiskerRight, hdp, MonoidalPreadditive.zero_whiskerRight])).Exact := by
    have h : (ShortComplex.mk d p hdp).Exact :=
      ShortComplex.exact_of_g_is_cokernel _ (P.opcyclesIsCokernel _ _ (by simp))
    exact h.map_of_epi_of_preservesCokernel (tensorRight F) (by dsimp; infer_instance)
      inferInstance
  have hpe (F : C) : Epi (p ▷ F) := (tensorRight F).map_epi p
  have hge (X : C) : Epi (X ◁ S.g) := (tensorLeft X).map_epi S.g
  refine Preadditive.mono_of_cancel_zero _ (fun {T} x hx ↦ ?_)
  obtain ⟨T₁, π₁, _, y, hy⟩ := surjective_up_to_refinements_of_epi (p ▷ S.X₁) x
  obtain ⟨T₂, π₂, _, z, hz⟩ :=
      (hcok S.X₂).exact_up_to_refinements (y ≫ P.X a ◁ S.f) (by
    dsimp
    rw [Category.assoc, whisker_exchange, ← Category.assoc, ← hy, Category.assoc,
      hx, comp_zero])
  have hex := (HomologicalComplex.exactAt_iff' _ (a - 1 - 1) (a - 1) a (by simp)
    (by simp)).1 (hP S.X₃)
  obtain ⟨T₃, π₃, _, w, hw⟩ := hex.exact_up_to_refinements (z ≫ P.X (a - 1) ◁ S.g) (by
    change (z ≫ P.X (a - 1) ◁ S.g) ≫ d ▷ S.X₃ = 0
    dsimp at hz
    rw [Category.assoc, whisker_exchange, ← Category.assoc, ← hz, Category.assoc,
      Category.assoc, ← MonoidalCategory.whiskerLeft_comp, S.zero,
      MonoidalPreadditive.whiskerLeft_zero, comp_zero, comp_zero])
  let w₀ : T₃ ⟶ P.X (a - 1 - 1) ⊗ S.X₃ := w
  have hw₂ : π₃ ≫ z ≫ P.X (a - 1) ◁ S.g = w₀ ≫ d' ▷ S.X₃ := hw
  obtain ⟨T₄, π₄, _, w', hw'⟩ :=
    surjective_up_to_refinements_of_epi (P.X (a - 1 - 1) ◁ S.g) w₀
  dsimp at hz
  have hz' : (π₄ ≫ π₃ ≫ z - w' ≫ d' ▷ S.X₂) ≫ P.X (a - 1) ◁ S.g = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, hw₂, Category.assoc,
      ← whisker_exchange, ← reassoc_of% hw', sub_self]
  have hex₁ : (S.map (tensorLeft (P.X (a - 1)))).Exact := hS.exact.map _
  have : Mono (S.map (tensorLeft (P.X (a - 1)))).f :=
    (tensorLeft (P.X (a - 1))).map_mono S.f
  have : Mono (P.X a ◁ S.f) := (tensorLeft (P.X a)).map_mono S.f
  let v : T₄ ⟶ P.X (a - 1) ⊗ S.X₁ := hex₁.lift _ hz'
  have hv : v ≫ P.X (a - 1) ◁ S.f = π₄ ≫ π₃ ≫ z - w' ≫ d' ▷ S.X₂ :=
    hex₁.lift_f _ hz'
  have hvy : v ≫ d ▷ S.X₁ = π₄ ≫ π₃ ≫ π₂ ≫ y := by
    rw [← cancel_mono (P.X a ◁ S.f)]
    simp only [Category.assoc]
    rw [← whisker_exchange, reassoc_of% hv,
      Preadditive.sub_comp, Category.assoc, Category.assoc, ← hz, Category.assoc,
      ← comp_whiskerRight, P.d_comp_d, MonoidalPreadditive.zero_whiskerRight, comp_zero,
      sub_zero]
  rw [← cancel_epi (π₄ ≫ π₃ ≫ π₂ ≫ π₁), comp_zero]
  simp only [Category.assoc]
  rw [hy, ← reassoc_of% hvy, ← comp_whiskerRight, hdp,
    MonoidalPreadditive.zero_whiskerRight, comp_zero]


end CategoryTheory
