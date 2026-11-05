import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Descent along a finite faithfully flat family

Compatible tensor coactions descend modules along a finite jointly faithfully flat family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open LinearMap

namespace TensorProduct

section Pi

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {ι : Type*} {P : ι → Type*} [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]

/-- The `i`-th component of `TensorProduct.piRight` is `lTensor M (proj i)`. -/
lemma piRight_apply_eq_lTensor_proj [Fintype ι] [DecidableEq ι] (x : M ⊗[R] (∀ i, P i)) (i : ι) :
    piRight R R M P x i = (LinearMap.proj i : (∀ i, P i) →ₗ[R] P i).lTensor M x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m p => simp
  | add x y hx hy => simp_all

/-- An element of `M ⊗[R] (∀ i, P i)` (with `ι` finite) vanishes if all its components
`lTensor M (proj i) x` vanish. -/
lemma eq_zero_of_lTensor_proj_eq_zero [Finite ι] (x : M ⊗[R] (∀ i, P i))
    (h : ∀ i, (LinearMap.proj i : (∀ i, P i) →ₗ[R] P i).lTensor M x = 0) : x = 0 := by
  classical
  have := Fintype.ofFinite ι
  apply (piRight R R M P).injective
  ext i
  simp only [piRight_apply_eq_lTensor_proj, h, map_zero]

end Pi

variable {A : Type*} [CommRing A] {J : Type*}
  {B : J → Type*} [∀ j, CommRing (B j)] [∀ j, Algebra A (B j)]
  {N : J → Type*} [∀ j, AddCommGroup (N j)] [∀ j, Module (B j) (N j)] [∀ j, Module A (N j)]
  [∀ j, IsScalarTower A (B j) (N j)]

/-- The `A`-linear map `(∀ j, N j) → ∀ j k, B j ⊗[A] N k` sending `n` to
`θ j k (n j) - 1 ⊗ₜ n k`. Its kernel is the module of descended elements. -/
def descentDiff (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k) :
    (∀ j, N j) →ₗ[A] ∀ j k, B j ⊗[A] N k :=
  LinearMap.pi fun j ↦ LinearMap.pi fun k ↦
    (θ j k).restrictScalars A ∘ₗ LinearMap.proj j -
      (TensorProduct.mk A (B j) (N k) 1) ∘ₗ LinearMap.proj k

/-- The components of `descentDiff θ n` are `θ j k (n j) - 1 ⊗ₜ n k`. -/
@[simp]
lemma descentDiff_apply (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k) (n : ∀ j, N j) (j k : J) :
    descentDiff θ n j k = θ j k (n j) - 1 ⊗ₜ n k :=
  rfl

/-- The `A`-submodule of `∀ j, N j` of families `n` with `θ j k (n j) = 1 ⊗ₜ n k`
for all `j k`. -/
def descentSubmodule (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k) : Submodule A (∀ j, N j) :=
  LinearMap.ker (descentDiff θ)

/-- A family `n` lies in `descentSubmodule θ` iff `θ j k (n j) = 1 ⊗ₜ n k` for all `j k`. -/
lemma mem_descentSubmodule (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k) (n : ∀ j, N j) :
    n ∈ descentSubmodule θ ↔ ∀ j k, θ j k (n j) = 1 ⊗ₜ n k := by
  simp [descentSubmodule, funext_iff, sub_eq_zero]

/-- The `B l`-linear map `B l ⊗[A] descentSubmodule θ → N l`, `b ⊗ₜ n ↦ b • n l`. -/
def descentLift (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k) (l : J) :
    B l ⊗[A] descentSubmodule θ →ₗ[B l] N l :=
  (LinearMap.proj l ∘ₗ (descentSubmodule θ).subtype).liftBaseChange (B l)

/-- The value of `descentLift θ l` on a pure tensor `b ⊗ₜ n` is `b • n l`. -/
@[simp]
lemma descentLift_tmul (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k) (l : J) (b : B l)
    (n : descentSubmodule θ) :
    descentLift θ l (b ⊗ₜ n) = b • (n : ∀ j, N j) l :=
  rfl

/-- `descentLift θ l` factors through `lTensor (B l)` of the inclusion of the descent submodule
followed by `b ⊗ₜ n ↦ b • n l`. -/
lemma descentLift_eq (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k) (l : J)
    (w : B l ⊗[A] descentSubmodule θ) :
    descentLift θ l w = (LinearMap.id : N l →ₗ[A] N l).liftBaseChange (B l)
      ((LinearMap.proj l : (∀ j, N j) →ₗ[A] N l).lTensor (B l)
        ((descentSubmodule θ).subtype.lTensor (B l) w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b n => simp
  | add x y hx hy => simp_all

/-- For a `B`-linear `θ : N →ₗ[B] P`, applying `B ⊗ θ` and then the action map
`B ⊗[A] P → P` agrees with applying the action map `B ⊗[A] N → N` and then `θ`. -/
lemma liftBaseChange_lTensor_restrictScalars {B N P : Type*} [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]
    (θ : N →ₗ[B] P) (x : B ⊗[A] N) :
    (LinearMap.id : P →ₗ[A] P).liftBaseChange B ((θ.restrictScalars A).lTensor B x) =
      θ ((LinearMap.id : N →ₗ[A] N).liftBaseChange B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b n => simp
  | add x y hx hy => simp_all

/-- Applying `b ⊗ₜ n ↦ b ⊗ₜ 1 ⊗ₜ n` and then multiplying the first two factors is the identity
of `B ⊗[A] N`. -/
lemma liftBaseChange_lTensor_mk_one {B N : Type*} [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] (x : B ⊗[A] N) :
    (LinearMap.id : B ⊗[A] N →ₗ[A] B ⊗[A] N).liftBaseChange B
      ((TensorProduct.mk A B N 1).lTensor B x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b n => simp [smul_tmul']
  | add x y hx hy => simp_all

/-- **Descent for a finite family of flat algebras.** Given descent data `θ` satisfying the unit
and cocycle conditions, for every `l` with `B l` flat over `A`, the natural map
`B l ⊗[A] descentSubmodule θ → N l`, `b ⊗ₜ n ↦ b • n l`, is bijective. -/
theorem bijective_descentLift_of_flat (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k)
    (hunit : ∀ j (x : N j), (LinearMap.id : N j →ₗ[A] N j).liftBaseChange (B j) (θ j j x) = x)
    (hcocycle : ∀ j k l (x : N j),
      ((θ k l).restrictScalars A).lTensor (B j) (θ j k x) =
        (TensorProduct.mk A (B k) (N l) 1).lTensor (B j) (θ j l x))
    [Finite J] (l : J) [Module.Flat A (B l)] :
    Function.Bijective (descentLift θ l) := by
  classical
  have := Fintype.ofFinite J
  have hinj : Function.Injective ((descentSubmodule θ).subtype.lTensor (B l)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (descentSubmodule θ).injective_subtype
  have hex : Function.Exact ((descentSubmodule θ).subtype.lTensor (B l))
      ((descentDiff θ).lTensor (B l)) :=
    Module.Flat.lTensor_exact (B l) (LinearMap.exact_subtype_ker_map _)
  have hcomp (z : B l ⊗[A] (∀ j, N j)) (j k : J) :
      (LinearMap.proj k).lTensor (B l)
        ((LinearMap.proj j).lTensor (B l) ((descentDiff θ).lTensor (B l) z)) =
        ((θ j k).restrictScalars A).lTensor (B l) ((LinearMap.proj j).lTensor (B l) z) -
          (TensorProduct.mk A (B j) (N k) 1).lTensor (B l)
            ((LinearMap.proj k).lTensor (B l) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b n => simp [tmul_sub]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
      abel
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    apply hinj
    rw [map_zero]
    apply eq_zero_of_lTensor_proj_eq_zero
    intro k
    have hlk := hcomp ((descentSubmodule θ).subtype.lTensor (B l) w) l k
    rw [hex.apply_apply_eq_zero, map_zero, map_zero, eq_comm, sub_eq_zero] at hlk
    have := congrArg ((LinearMap.id : B l ⊗[A] N k →ₗ[A] B l ⊗[A] N k).liftBaseChange (B l)) hlk
    rw [liftBaseChange_lTensor_restrictScalars, liftBaseChange_lTensor_mk_one,
      ← descentLift_eq, hw, map_zero] at this
    exact this.symm
  · intro x
    set z := (piRight A A (B l) N).symm (fun j ↦ θ l j x) with hz
    have hzj (j : J) : (LinearMap.proj j : (∀ j, N j) →ₗ[A] N j).lTensor (B l) z = θ l j x := by
      rw [← piRight_apply_eq_lTensor_proj, hz, LinearEquiv.apply_symm_apply]
    have hker : (descentDiff θ).lTensor (B l) z = 0 := by
      apply eq_zero_of_lTensor_proj_eq_zero
      intro j
      apply eq_zero_of_lTensor_proj_eq_zero
      intro k
      rw [hcomp, hzj, hzj, hcocycle, sub_self]
    obtain ⟨w, hw⟩ := (hex z).mp hker
    exact ⟨w, by rw [descentLift_eq, hw, hzj, hunit]⟩

/-- The `B l`-linear equivalence `B l ⊗[A] descentSubmodule θ ≃ₗ[B l] N l` obtained from
`TensorProduct.bijective_descentLift_of_flat`. -/
noncomputable def descentEquiv (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k)
    (hunit : ∀ j (x : N j), (LinearMap.id : N j →ₗ[A] N j).liftBaseChange (B j) (θ j j x) = x)
    (hcocycle : ∀ j k l (x : N j),
      ((θ k l).restrictScalars A).lTensor (B j) (θ j k x) =
        (TensorProduct.mk A (B k) (N l) 1).lTensor (B j) (θ j l x))
    [Finite J] (l : J) [Module.Flat A (B l)] :
    B l ⊗[A] descentSubmodule θ ≃ₗ[B l] N l :=
  LinearEquiv.ofBijective (descentLift θ l) (bijective_descentLift_of_flat θ hunit hcocycle l)

/-- `descentEquiv` agrees with `descentLift`. -/
@[simp]
lemma descentEquiv_apply (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k)
    (hunit : ∀ j (x : N j), (LinearMap.id : N j →ₗ[A] N j).liftBaseChange (B j) (θ j j x) = x)
    (hcocycle : ∀ j k l (x : N j),
      ((θ k l).restrictScalars A).lTensor (B j) (θ j k x) =
        (TensorProduct.mk A (B k) (N l) 1).lTensor (B j) (θ j l x))
    [Finite J] (l : J) [Module.Flat A (B l)] (w : B l ⊗[A] descentSubmodule θ) :
    descentEquiv θ hunit hcocycle l w = descentLift θ l w :=
  rfl

/-- The value of `descentEquiv` on a pure tensor `b ⊗ₜ n` is `b • n l`. -/
lemma descentEquiv_tmul (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k)
    (hunit : ∀ j (x : N j), (LinearMap.id : N j →ₗ[A] N j).liftBaseChange (B j) (θ j j x) = x)
    (hcocycle : ∀ j k l (x : N j),
      ((θ k l).restrictScalars A).lTensor (B j) (θ j k x) =
        (TensorProduct.mk A (B k) (N l) 1).lTensor (B j) (θ j l x))
    [Finite J] (l : J) [Module.Flat A (B l)] (b : B l) (n : descentSubmodule θ) :
    descentEquiv θ hunit hcocycle l (b ⊗ₜ n) = b • (n : ∀ j, N j) l :=
  rfl

section Amitsur

variable {A B N : Type*} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup N] [Module A N]

/-- The coaction `b ⊗ n ↦ b ⊗ (1 ⊗ n)` of `B ⊗[A] N`, whose descent submodule is the equalizer
of the two maps `B ⊗[A] N → B ⊗[A] B ⊗[A] N`. -/
noncomputable abbrev amitsurCoaction (A B N : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] (_ _ : Unit) :
    B ⊗[A] N →ₗ[B] B ⊗[A] (B ⊗[A] N) :=
  (TensorProduct.mk A B N 1).baseChange B

lemma amitsurCoaction_tmul (b : B) (n : N) :
    amitsurCoaction A B N () () (b ⊗ₜ n) = b ⊗ₜ (1 ⊗ₜ n) :=
  rfl

/-- The inclusion `n ↦ (1 ⊗ n)` of `N` into the descent submodule of `amitsurCoaction`. -/
noncomputable def amitsurInclusion : N →ₗ[A] descentSubmodule (amitsurCoaction A B N) where
  toFun n := ⟨fun _ ↦ 1 ⊗ₜ n, by
    rw [mem_descentSubmodule]
    intro j k
    rfl⟩
  map_add' n n' := by ext; simp [tmul_add]
  map_smul' a n := by ext; simp [tmul_smul]

/-- **Amitsur exactness in degree zero.** For a faithfully flat `A`-algebra `B`, an element of
`B ⊗[A] N` whose two images in `B ⊗[A] B ⊗[A] N` agree is of the form `1 ⊗ n`.

This is the degree-zero part of `Module.FaithfullyFlat.exact_amitsurComplex`, stated with the
tensor factors in the order `B ⊗ N` and the maps `includeLeft`, `includeRight`; here it is
deduced from the descent statement `TensorProduct.bijective_descentLift_of_flat`. -/
theorem _root_.Module.FaithfullyFlat.exists_eq_one_tmul_of_rTensor_eq [Module.FaithfullyFlat A B]
    (t : B ⊗[A] N)
    (ht : (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap.rTensor N t =
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap.rTensor N t) :
    ∃ n : N, t = 1 ⊗ₜ n := by
  have hunit : ∀ (j : Unit) (x : B ⊗[A] N),
      (LinearMap.id : B ⊗[A] N →ₗ[A] B ⊗[A] N).liftBaseChange B
        (amitsurCoaction A B N j j x) = x := by
    intro j x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b n => simp [smul_tmul']
    | add x y hx hy => simp_all
  have hcocycle : ∀ (j k l : Unit) (x : B ⊗[A] N),
      ((amitsurCoaction A B N k l).restrictScalars A).lTensor B
        (amitsurCoaction A B N j k x) =
        (TensorProduct.mk A B (B ⊗[A] N) 1).lTensor B (amitsurCoaction A B N j l x) := by
    intro j k l x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b n => rfl
    | add x y hx hy => simp_all
  have hbij := bijective_descentLift_of_flat (amitsurCoaction A B N) hunit hcocycle ()

  have hsec : ∀ x : B ⊗[A] N,
      descentLift (amitsurCoaction A B N) ()
        ((amitsurInclusion (A := A) (B := B) (N := N)).lTensor B x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b n => simp [amitsurInclusion, smul_tmul']
    | add x y hx hy => simp_all
  have hincl : Function.Bijective (amitsurInclusion (A := A) (B := B) (N := N)) := by
    have hl : Function.Bijective ((amitsurInclusion (A := A) (B := B) (N := N)).lTensor B) := by
      constructor
      · intro x y hxy
        rw [← hsec x, ← hsec y, hxy]
      · intro z
        refine ⟨descentLift (amitsurCoaction A B N) () z, ?_⟩
        apply hbij.1
        exact hsec _
    have key := Module.FaithfullyFlat.lTensor_bijective_iff_bijective (R := A) (M := B)
      (N := N) (N' := descentSubmodule (amitsurCoaction A B N))
      (amitsurInclusion (A := A) (B := B) (N := N))
    exact key.mp hl
  have ht' : (fun _ : Unit ↦ t) ∈ descentSubmodule (amitsurCoaction A B N) := by
    rw [mem_descentSubmodule]
    intro j k
    have h1 : ∀ x : B ⊗[A] N, TensorProduct.assoc A B B N
        ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap.rTensor N x) =
        amitsurCoaction A B N () () x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b n => simp
      | add x y hx hy => simp_all
    have h2 : ∀ x : B ⊗[A] N, TensorProduct.assoc A B B N
        ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap.rTensor N x) =
        1 ⊗ₜ x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b n => simp
      | add x y hx hy => simp_all [tmul_add]
    rw [← h1, ht, h2]
  obtain ⟨n, hn⟩ := hincl.2 ⟨_, ht'⟩
  exact ⟨n, (congr_fun (congr_arg Subtype.val hn) ()).symm⟩

end Amitsur

end TensorProduct
