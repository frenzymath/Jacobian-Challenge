import Jacobian.CategoryTheory.Abelian.RightDerived.ExactSequence
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape

/-!
# Acyclic objects for a left exact functor

Positive right-derived vanishing is stable under isomorphisms, finite sums
and cokernels of monomorphisms between acyclic objects. A class closed under
injective dimension shifting is acyclic whenever the functor is right exact
on short exact sequences whose first term lies in that class.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoryTheory

open Limits ZeroObject

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D]

namespace Functor

variable (F : C ⥤ D) [F.Additive]

/-- An object `A` is `F`-acyclic if `R^q F A = 0` for all `q > 0`. This is acyclicity of an
object with respect to `F`, not acyclicity of a complex in the sense of
`HomologicalComplex.Acyclic`. -/
def rightAcyclic : ObjectProperty C :=
  fun A ↦ ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)

instance : F.rightAcyclic.IsClosedUnderIsomorphisms where
  of_iso e hA q := (hA q).of_iso ((F.rightDerived (q + 1)).mapIso e.symm)

instance : F.rightAcyclic.ContainsZero where
  exists_zero := ⟨0, isZero_zero C, fun _ ↦ Functor.map_isZero _ (isZero_zero C)⟩

variable {F}

/-- Injective objects are `F`-acyclic. -/
lemma rightAcyclic_of_injective (A : C) [Injective A] : F.rightAcyclic A :=
  fun q ↦ F.isZero_rightDerived_obj_injective_succ q A

/-- `F`-acyclic objects are closed under binary biproducts. -/
lemma rightAcyclic_biprod {A B : C} (hA : F.rightAcyclic A) (hB : F.rightAcyclic B) :
    F.rightAcyclic (A ⊞ B) := by
  intro q
  have := preservesBinaryBiproducts_of_preservesBiproducts (F.rightDerived (q + 1))
  exact ((biprod_isZero_iff _ _).2 ⟨hA q, hB q⟩).of_iso ((F.rightDerived (q + 1)).mapBiprod A B)

instance : F.rightAcyclic.IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨h⟩
    refine F.rightAcyclic.prop_of_iso ?_
      (rightAcyclic_biprod (h.prop_diag_obj ⟨.left⟩) (h.prop_diag_obj ⟨.right⟩))
    exact biprod.isoProd _ _ ≪≫ HasLimit.isoOfNatIso (diagramIsoPair h.diag).symm ≪≫
      (limit.isLimit _).conePointUniqueUpToIso h.isLimit

end Functor

namespace ShortComplex.ShortExact

variable {F : C ⥤ D} [F.Additive] {S : ShortComplex C} (hS : S.ShortExact)

include hS

/-- `F`-acyclic objects are closed under cokernels of monomorphisms: if `0 ⟶ A ⟶ B ⟶ C ⟶ 0`
is short exact and `A` and `B` are `F`-acyclic, then so is `C`. -/
lemma rightAcyclic_X₃ (h₁ : F.rightAcyclic S.X₁) (h₂ : F.rightAcyclic S.X₂) :
    F.rightAcyclic S.X₃ := by
  intro q
  obtain ⟨δ, w₁, w₂, h, -⟩ := hS.exists_rightDerived_δ_exact F (q + 1)
  exact (h.isZero_X₂_iff).2 ⟨(h₂ q).eq_of_src _ _, (h₁ (q + 1)).eq_of_tgt _ _⟩

/-- A left exact functor `F` sends a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` with `A`
`F`-acyclic to a short exact sequence `0 ⟶ F A ⟶ F B ⟶ F C ⟶ 0`: exactness on the right
follows from `R^1 F A = 0`. -/
lemma map_of_rightAcyclic [PreservesFiniteLimits F] (h₁ : F.rightAcyclic S.X₁) :
    (S.map F).ShortExact := by
  have := hS.mono_f
  have hf : IsLimit (KernelFork.ofι (F.map S.f) (S.map F).zero) :=
    isLimitForkMapOfIsLimit' F S.zero hS.exact.fIsKernel
  have : Mono (S.map F).f := mono_of_isLimit_fork hf
  obtain ⟨δ, w₁, -, h, -⟩ := hS.exists_rightDerived_δ_exact F 0
  have : Epi ((F.rightDerived 0).map S.g) := h.epi_f ((h₁ 0).eq_of_tgt _ _)
  have : Epi (S.map F).g := by
    change Epi (F.map S.g)
    rw [← NatIso.naturality_1 F.rightDerivedZeroIsoSelf S.g]
    infer_instance
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hf) inferInstance
    inferInstance

end ShortComplex.ShortExact

end CategoryTheory

namespace CategoryTheory.Functor

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- **A criterion for acyclicity.** Let `P` be a property of objects of `C` which holds for the
injective objects and passes to the cokernel of a monomorphism between objects of `P`, and such
that `F` sends every short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` with `A` in `P` to an
epimorphism `F B ⟶ F C`. Then every object of `P` is `F`-acyclic.

Embed `A` into an injective object `I`, with cokernel `Q` in `P`. In the long exact sequence
`R^q F I ⟶ R^q F Q ⟶ R^{q+1} F A ⟶ R^{q+1} F I = 0`, the first map is an epimorphism for
`q = 0`, and `R^q F Q = 0` for `q > 0` by induction. -/
theorem rightAcyclic_of_epi_map_g (P : ObjectProperty C) (hinj : ∀ (I : C) [Injective I], P I)
    (hX₃ : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
    (hepi : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → Epi (F.map S.g)) {A : C}
    (hA : P A) : F.rightAcyclic A := by
  have := enoughInjectives_of_hasInjectiveResolutions (C := C)
  intro q
  induction q generalizing A with
  | zero =>
    let S := ShortComplex.mk (Injective.ι A) (cokernel.π (Injective.ι A)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    obtain ⟨δ, w₁, w₂, h₁, h₂⟩ := hS.exists_rightDerived_δ_exact F 0
    have : Epi ((F.rightDerived 0).map S.g) := by
      rw [← NatIso.naturality_2 F.rightDerivedZeroIsoSelf S.g]
      have := hepi S hS hA
      infer_instance
    exact h₂.isZero_X₂_iff.2 ⟨h₁.epi_f_iff.1 this,
      (F.isZero_rightDerived_obj_injective_succ 0 S.X₂).eq_of_tgt _ _⟩
  | succ q ih =>
    let S := ShortComplex.mk (Injective.ι A) (cokernel.π (Injective.ι A)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    obtain ⟨δ, w₁, w₂, -, h₂⟩ := hS.exists_rightDerived_δ_exact F (q + 1)
    exact h₂.isZero_X₂_iff.2 ⟨(ih (hX₃ S hS hA (hinj _))).eq_of_src _ _,
      (F.isZero_rightDerived_obj_injective_succ (q + 1) S.X₂).eq_of_tgt _ _⟩

end CategoryTheory.Functor
