import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Order.Directed
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

/-!
# Tensor products and filtered ring colimits

Elements of a tensor product over a directed ring colimit lift to a finite stage,
and an element that vanishes in the colimit vanishes at a later stage.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace TensorProduct

/-- Tensor elements lift to a finite stage, and vanishing is detected at a later stage. -/
theorem directedColimitBaseChangeElementwise
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (M₀ : Type w) [AddCommGroup M₀] [Module (F.obj i₀) M₀] :
    let S := F.obj i₀
    let R := colimit F
    letI : Algebra S R := (colimit.ι F i₀).hom.toAlgebra
    (∀ x : R ⊗[S] M₀, ∃ (i : I) (h : i₀ ≤ i),
      letI : Algebra S (F.obj i) := (F.map (homOfLE h)).hom.toAlgebra
      let αᵢ : F.obj i →ₐ[S] R :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE h)) }
      ∃ t : F.obj i ⊗[S] M₀, αᵢ.toLinearMap.rTensor M₀ t = x) ∧
    (∀ (i : I) (h : i₀ ≤ i),
      letI : Algebra S (F.obj i) := (F.map (homOfLE h)).hom.toAlgebra
      let αᵢ : F.obj i →ₐ[S] R :=
        { (colimit.ι F i).hom with
          commutes' := fun s ↦
            congrArg (fun f : F.obj i₀ ⟶ colimit F ↦ f s) (colimit.w F (homOfLE h)) }
      ∀ t : F.obj i ⊗[S] M₀, αᵢ.toLinearMap.rTensor M₀ t = 0 →
        ∃ (i' : I) (h' : i ≤ i'),
          letI : Algebra S (F.obj i') := (F.map (homOfLE (h.trans h'))).hom.toAlgebra
          let αᵢ'ᵢ : F.obj i →ₐ[S] F.obj i' :=
            { (F.map (homOfLE h')).hom with
              commutes' := fun s ↦
                congrArg (fun f : F.obj i₀ ⟶ F.obj i' ↦ f s)
                  (F.map_comp (homOfLE h) (homOfLE h')).symm }
          αᵢ'ᵢ.toLinearMap.rTensor M₀ t = 0) := by
  classical
  let : Nonempty I := ⟨i₀⟩
  let : IsFiltered I := inferInstance
  let : PreservesColimit F (forget CommRingCat) := inferInstance
  let S := F.obj i₀
  let R := colimit F
  let : Algebra S R := (colimit.ι F i₀).hom.toAlgebra
  let J := {i : I // i₀ ≤ i}
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirectedOrder J := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let A : J → Type v := fun i ↦ F.obj i.val
  let : ∀ i, CommRing (A i) := fun i ↦ inferInstance
  let : ∀ i, Algebra S (A i) := fun i ↦ (F.map (homOfLE i.property)).hom.toAlgebra
  let f (i j : J) (h : i ≤ j) : A i →ₗ[S] A j :=
    AlgHom.toLinearMap
      { (F.map (homOfLE h)).hom with
        commutes' := fun s ↦ congrArg (fun p : F.obj i₀ ⟶ F.obj j.val ↦ p s)
          (F.map_comp (homOfLE i.property) (homOfLE h)).symm }
  let α (i : J) : A i →ₗ[S] R :=
    AlgHom.toLinearMap
      { (colimit.ι F i.val).hom with
        commutes' := fun s ↦ congrArg (fun p : F.obj i₀ ⟶ colimit F ↦ p s)
          (colimit.w F (homOfLE i.property)) }
  have compat (i j : J) (h : i ≤ j) (a : A i) : α j (f i j h a) = α i a := by
    exact ConcreteCategory.congr_hom (colimit.w F (homOfLE h)) a
  let : DirectedSystem A (fun {i j} h ↦ f i j h) :=
    { map_self := by
        intro i a
        change F.map (homOfLE (le_refl i.val)) a = a
        simp
      map_map := by
        intro i j k hij hjk a
        change F.map (homOfLE hjk) (F.map (homOfLE hij) a) =
          F.map (homOfLE (hij.trans hjk)) a
        exact (ConcreteCategory.congr_hom
          (F.map_comp (homOfLE hij) (homOfLE hjk)) a).symm }
  let g : Module.DirectLimit A f →ₗ[S] R :=
    Module.DirectLimit.lift S J A f α compat
  have ginj : Function.Injective g := by
    intro x y hxy
    obtain ⟨i, a, hx⟩ := Module.DirectLimit.exists_of x
    obtain ⟨j, b, hy⟩ := Module.DirectLimit.exists_of y
    rw [← hx, ← hy] at hxy ⊢
    simp only [g, Module.DirectLimit.lift_of] at hxy
    obtain ⟨k, u, v, he⟩ := Concrete.colimit_exists_of_rep_eq F a b hxy
    let k' : J := ⟨k, i.property.trans (leOfHom u)⟩
    have he' : f i k' (leOfHom u) a = f j k' (leOfHom v) b := he
    rw [← Module.DirectLimit.of_f (f := f) (i := i) (j := k') (hij := leOfHom u),
      ← Module.DirectLimit.of_f (f := f) (i := j) (j := k') (hij := leOfHom v), he']
  have gsurj : Function.Surjective g := by
    intro r
    obtain ⟨i, a, ha⟩ := Concrete.colimit_exists_rep F r
    obtain ⟨j, h₀j, hij⟩ := exists_ge_ge i₀ i
    let j' : J := ⟨j, h₀j⟩
    refine ⟨Module.DirectLimit.of S J A f j' (F.map (homOfLE hij) a), ?_⟩
    simp only [g, Module.DirectLimit.lift_of]
    change colimit.ι F j (F.map (homOfLE hij) a) = r
    exact (ConcreteCategory.congr_hom (colimit.w F (homOfLE hij)) a).trans ha
  let E : Module.DirectLimit A f ≃ₗ[S] R := LinearEquiv.ofBijective g ⟨ginj, gsurj⟩
  let ft (i j : J) (h : i ≤ j) := (f i j h).rTensor M₀
  let e : Module.DirectLimit (fun i ↦ A i ⊗[S] M₀) ft ≃ₗ[S] R ⊗[S] M₀ :=
    (TensorProduct.directLimitLeft f M₀).symm.trans (E.rTensor M₀)
  have e_of (i : J) (t : A i ⊗[S] M₀) :
      e (Module.DirectLimit.of S J (fun i ↦ A i ⊗[S] M₀) ft i t) =
        (α i).rTensor M₀ t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      dsimp only [e, ft]
      rw [LinearEquiv.trans_apply, TensorProduct.directLimitLeft_symm_of_tmul,
        LinearEquiv.rTensor_tmul, LinearMap.rTensor_tmul]
      change g (Module.DirectLimit.of S J A f i a) ⊗ₜ[S] m = α i a ⊗ₜ[S] m
      simp only [g, Module.DirectLimit.lift_of]
    | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu
  let : DirectedSystem (fun i ↦ A i ⊗[S] M₀) (fun {i j} h ↦ ft i j h) :=
    { map_self := by
        intro i t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul a m => simp only [ft, LinearMap.rTensor_tmul, DirectedSystem.map_self']
        | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu
      map_map := by
        intro i j k hij hjk t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul a m => simp only [ft, LinearMap.rTensor_tmul, DirectedSystem.map_map']
        | add t u ht hu => simpa only [map_add] using congrArg₂ (· + ·) ht hu }
  dsimp only
  constructor
  · intro x
    obtain ⟨i, t, ht⟩ := Module.DirectLimit.exists_of (e.symm x)
    refine ⟨i.val, i.property, t, ?_⟩
    change (α i).rTensor M₀ t = x
    rw [← e_of, ht, e.apply_symm_apply]
  · intro i h t ht
    let i' : J := ⟨i, h⟩
    have hz : Module.DirectLimit.of S J (fun i ↦ A i ⊗[S] M₀) ft i' t = 0 := by
      apply e.injective
      rw [e_of, map_zero]
      exact ht
    obtain ⟨j, hij, he⟩ := Module.DirectLimit.of.zero_exact hz
    exact ⟨j.val, hij, he⟩

end TensorProduct
end
