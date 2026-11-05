import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Bounded acyclic complexes of flat modules

In a bounded-above acyclic complex of flat modules, the kernels of the
outgoing differentials are flat, by downward induction from the upper bound.
The resulting short exact sequences of cycles remain exact after tensoring
with any module. Thus an arbitrary tensor functor preserves acyclicity of
such complexes; no lower bound or flatness of the tensor factor is required.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace Module.Flat

variable {R : Type u} [CommRing R]

/-- In a short exact sequence, flatness of the middle and quotient implies
flatness of the actual left module. -/
theorem of_injective_exact_of_flat_quotient
    {K M N : Type u} [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
    [Module R K] [Module R M] [Module R N] [Module.Flat R M] [Module.Flat R N]
    (i : K →ₗ[R] M) (p : M →ₗ[R] N) (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) : Module.Flat R K := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro A B _ _ _ _ f hf
  have hia : Function.Injective (i.lTensor A) :=
    LinearMap.lTensor_injective_of_exact_of_flat p hp i hi hex A
  have hfm : Function.Injective (f.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  apply Function.Injective.of_comp (f := i.lTensor B)
  change Function.Injective ((i.lTensor B).comp (f.rTensor K))
  rw [LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor]
  exact hfm.comp hia

end Module.Flat

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- Every actual kernel of the outgoing differential of a bounded-above acyclic
complex of flat modules is flat. No bounded-below hypothesis is needed. -/
theorem flat_kernel_d_of_boundedAbove_acyclic
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hflat : ∀ n : ℤ, Module.Flat R (P.X n))
    (hexact : ∀ n : ℤ, P.ExactAt n) (n : ℤ) :
    Module.Flat R (LinearMap.ker (P.d n (n + 1)).hom) := by
  have above (m : ℤ) (hm : b < m) :
      Module.Flat R (LinearMap.ker (P.d m (m + 1)).hom) := by
    letI : Subsingleton (P.X m) :=
      ModuleCat.isZero_iff_subsingleton.mp (P.isZero_of_isStrictlyLE b m hm)
    infer_instance
  have step (m : ℤ)
      (hnext : Module.Flat R (LinearMap.ker (P.d (m + 1) (m + 1 + 1)).hom)) :
      Module.Flat R (LinearMap.ker (P.d m (m + 1)).hom) := by
    let d := (P.d m (m + 1)).hom
    let d' := (P.d (m + 1) (m + 1 + 1)).hom
    have hdd (x : P.X m) : d' (d x) = 0 := by
      exact congrArg (fun f : P.X m ⟶ P.X (m + 1 + 1) => f x)
        (P.d_comp_d m (m + 1) (m + 1 + 1))
    let q : P.X m →ₗ[R] LinearMap.ker d' := d.codRestrict _ hdd
    have hq : Function.Surjective q := by
      have he := (HomologicalComplex.exactAt_iff' P m (m + 1) (m + 1 + 1)
        (by simp) (by simp)).mp (hexact (m + 1))
      intro x
      obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp he x.val x.property
      exact ⟨y, Subtype.ext hy⟩
    have he : Function.Exact (LinearMap.ker d).subtype q := by
      intro x
      constructor
      · intro h
        exact ⟨⟨x, congrArg Subtype.val h⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact Subtype.ext y.property
    letI : Module.Flat R (P.X m) := hflat m
    letI : Module.Flat R (LinearMap.ker d') := hnext
    exact Module.Flat.of_injective_exact_of_flat_quotient
      (LinearMap.ker d).subtype q (LinearMap.ker d).subtype_injective hq he
  by_cases hn : n ≤ b
  · apply Int.leInductionDown (m := b) (motive := fun m _ =>
      Module.Flat R (LinearMap.ker (P.d m (m + 1)).hom)) ?_ ?_ n hn
    · exact step b (above (b + 1) (by omega))
    · intro m hm ih
      have h := step (m - 1)
      have he : m - 1 + 1 = m := by omega
      rw [he] at h ⊢
      exact h ih
  · exact above n (by omega)

end CochainComplex

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- An acyclic module complex whose actual cycles are flat stays acyclic after
tensoring with any module. The complex and its tensor action are the actual
ModuleCat objects. -/
theorem tensorRight_exactAt_of_flat_kernels
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hexact : ∀ n : ℤ, P.ExactAt n)
    (hflat : ∀ n : ℤ, Module.Flat R (LinearMap.ker (P.d n (n + 1)).hom))
    (N : ModuleCat.{u} R) (n : ℤ) :
    (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P).ExactAt n := by
  let K (m : ℤ) := LinearMap.ker (P.d m (m + 1)).hom
  let q (m : ℤ) : P.X m →ₗ[R] K (m + 1) :=
    (P.d m (m + 1)).hom.codRestrict _ (fun x =>
      congrArg (fun f : P.X m ⟶ P.X (m + 1 + 1) => f x)
        (P.d_comp_d m (m + 1) (m + 1 + 1)))
  have hsurj (m : ℤ) : Function.Surjective (q m) := by
    have he := (HomologicalComplex.exactAt_iff' P m (m + 1) (m + 1 + 1)
      (by simp) (by simp)).mp (hexact (m + 1))
    intro x
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp he x.val x.property
    exact ⟨y, Subtype.ext hy⟩
  have hseq (m : ℤ) : Function.Exact (K m).subtype (q m) := by
    intro x
    constructor
    · intro h
      exact ⟨⟨x, congrArg Subtype.val h⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext y.property
  have hinj (m : ℤ) : Function.Injective ((K m).subtype.rTensor N) := by
    letI : Module.Flat R (K (m + 1)) := hflat (m + 1)
    apply (LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp
    exact LinearMap.lTensor_injective_of_exact_of_flat (q m) (hsurj m)
      (K m).subtype (K m).subtype_injective (hseq m) N
  have he := rTensor_exact N (hseq n) (hsurj n)
  have hp := (hinj (n + 1)).comp_exact_iff_exact
    (f := (K n).subtype.rTensor N) (g := (q n).rTensor N)
  have he' := hp.mpr he
  let qprev : P.X (n - 1) →ₗ[R] K n :=
    (P.d (n - 1) n).hom.codRestrict _ (fun x =>
      congrArg (fun f : P.X (n - 1) ⟶ P.X (n + 1) => f x)
        (P.d_comp_d (n - 1) n (n + 1)))
  have hprev : Function.Surjective qprev := by
    have h := (HomologicalComplex.exactAt_iff' P (n - 1) n (n + 1)
      (by simp) (by simp)).mp (hexact n)
    intro x
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp h x.val x.property
    exact ⟨y, Subtype.ext hy⟩
  have hq := (LinearMap.rTensor_surjective N hprev).comp_exact_iff_exact
    (f := (K n).subtype.rTensor N)
    (g := ((K (n + 1)).subtype.rTensor N).comp ((q n).rTensor N))
  have he'' := hq.mpr he'
  have fac (m : ℤ) : (K (m + 1)).subtype.comp (q m) =
      (P.d m (m + 1)).hom := by ext x; rfl
  rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp, fac n] at he''
  have fac' : (K n).subtype.comp qprev = (P.d (n - 1) n).hom := by ext x; rfl
  rw [fac'] at he''
  apply (HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1)
    (by simp) (by simp)).mpr
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  exact he''

/-- Every bounded-above acyclic complex of flat modules remains acyclic after
tensoring with an arbitrary module. No lower bound is assumed. -/
theorem tensorRight_exactAt_of_boundedAbove_acyclic_flat
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hflat : ∀ n : ℤ, Module.Flat R (P.X n))
    (hexact : ∀ n : ℤ, P.ExactAt n) (N : ModuleCat.{u} R) (n : ℤ) :
    (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P).ExactAt n :=
  tensorRight_exactAt_of_flat_kernels P hexact
    (flat_kernel_d_of_boundedAbove_acyclic P b hflat hexact) N n

end CochainComplex
