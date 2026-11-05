import Jacobian.RingTheory.Ideal.Quotient.Product
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness in short exact sequences

Extensions of flat modules are flat, as are kernels of surjections between
flat modules. In particular, quotients by products of regular elements are flat
when the two factor quotients are flat.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

/-- **Extensions of flat modules are flat.** In a short exact sequence
`0 ⟶ M' ⟶ M ⟶ M'' ⟶ 0` of `R`-modules with `M'` and `M''` flat, `M` is flat. -/
lemma Module.Flat.of_exact_of_flat_of_flat {R M' M M'' : Type*} [CommRing R]
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M''] [Module R M'] [Module R M]
    [Module R M''] [Module.Flat R M'] [Module.Flat R M''] (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    Module.Flat R M := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ ι hι
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : g.lTensor N x = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := M'') ι hι
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply, hx, map_zero, map_zero]
  obtain ⟨y, rfl⟩ := (_root_.lTensor_exact N H hg x).mp h1
  have h2 : ι.rTensor M' y = 0 := by
    apply LinearMap.lTensor_injective_of_exact_of_flat g hg f hf H P
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
      LinearMap.comp_apply, hx, map_zero]
  have h3 : y = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := M') ι hι
    rw [h2, map_zero]
  rw [h3, map_zero]

/-- **Kernels of surjections of flat modules are flat.** In a short exact sequence
`0 ⟶ M' ⟶ M ⟶ M'' ⟶ 0` of `R`-modules with `M` and `M''` flat, `M'` is flat. -/
lemma Module.Flat.of_exact_of_flat_of_flat_right {R M' M M'' : Type*} [CommRing R]
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M''] [Module R M'] [Module R M]
    [Module R M''] [Module.Flat R M] [Module.Flat R M''] (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    Module.Flat R M' := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ ι hι
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : f.lTensor N x = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := M) ι hι
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply, hx, map_zero, map_zero]
  exact LinearMap.lTensor_injective_of_exact_of_flat g hg f hf H N (h1.trans (map_zero _).symm)

section Quotient

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (v₁ v₂ : B)

/-- If `v₁` is a non-zerodivisor and `B ⧸ (v₁)`, `B ⧸ (v₂)` are flat over `R`, then so is
`B ⧸ (v₁ v₂)`. -/
lemma Ideal.Quotient.flat_span_singleton_mul (hv : v₁ ∈ nonZeroDivisors B)
    [Module.Flat R (B ⧸ Ideal.span {v₁})] [Module.Flat R (B ⧸ Ideal.span {v₂})] :
    Module.Flat R (B ⧸ Ideal.span {v₁ * v₂}) :=
  Module.Flat.of_exact_of_flat_of_flat _ _ (Ideal.Quotient.injective_mulSpanSingleton v₁ v₂ hv)
    (Ideal.Quotient.surjective_factorSpanSingleton v₁ v₂)
    (Ideal.Quotient.exact_mulSpanSingleton_factorSpanSingleton v₁ v₂)

end Quotient

/-- A regular element remains regular after base change when its quotient is flat. -/
theorem Algebra.TensorProduct.includeLeftRingHom_mem_nonZeroDivisors_of_flat
    {A B C A' : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing A'] [Algebra A B]
    [Algebra A A'] (q : B →+* C) (hq : Function.Surjective q) {f : B}
    (hker : RingHom.ker q = Ideal.span {f}) (hflat : (q.comp (algebraMap A B)).Flat)
    (hf : f ∈ nonZeroDivisors B) :
    (Algebra.TensorProduct.includeLeftRingHom f : B ⊗[A] A') ∈ nonZeroDivisors (B ⊗[A] A') := by
  let := (q.comp (algebraMap A B)).toAlgebra
  have : Module.Flat A C := hflat
  let qA : B →ₗ[A] C :=
    { toFun := q
      map_add' := map_add q
      map_smul' := fun a b ↦ by
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra] }
  have hex : Function.Exact (LinearMap.mulLeft A f) qA := fun b ↦
    (RingHom.mem_ker (f := q)).symm.trans <| by
      rw [hker, Ideal.mem_span_singleton']
      simp [mul_comm]
  have hinj := LinearMap.lTensor_injective_of_exact_of_flat qA hq (LinearMap.mulLeft A f)
    (isRegular_iff_mem_nonZeroDivisors.mpr hf).left hex A'
  have hcomm (x : B ⊗[A] A') :
      (LinearMap.mulLeft A f).lTensor A' (TensorProduct.comm A B A' x) =
        TensorProduct.comm A B A' (Algebra.TensorProduct.includeLeftRingHom f * x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b a => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add, map_add]
  have key (x : B ⊗[A] A') (hx : Algebra.TensorProduct.includeLeftRingHom f * x = 0) :
      x = 0 := by
    have := hcomm x
    rw [hx, map_zero, ← map_zero ((LinearMap.mulLeft A f).lTensor A')] at this
    simpa using hinj this
  exact mem_nonZeroDivisors_iff.mpr ⟨key, fun x hx ↦ key x (by rwa [mul_comm])⟩


universe flatCyclesUniverse

namespace Module.Flat

variable {A : Type flatCyclesUniverse} [CommRing A] {K M N : Type flatCyclesUniverse} [AddCommGroup K] [Module A K]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
  {f : K →ₗ[A] M} {g : M →ₗ[A] N}

omit [AddCommGroup N] [Module A N] in
/-- Tensoring on the left and on the right commute. -/
private lemma rTensor_lTensor_apply {P Q : Type flatCyclesUniverse} [AddCommGroup P] [Module A P] [AddCommGroup Q]
    [Module A Q] (h : P →ₗ[A] Q) (f : K →ₗ[A] M) (x : P ⊗[A] K) :
    h.rTensor M (f.lTensor P x) = f.lTensor Q (h.rTensor K x) := by
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.comp_apply]

/-- **`Tor₁(A/I, N)` as a kernel.** If `0 ⟶ K ⟶ M ⟶ N ⟶ 0` is exact, `M` is flat and
`A/I ⊗ K ⟶ A/I ⊗ M` is injective for every ideal `I`, then `N` is flat. -/
theorem of_exact_of_lTensor_quotient_injective [Flat A M] (hfg : Function.Exact f g)
    (hg : Function.Surjective g)
    (h : ∀ I : Ideal A, Function.Injective (f.lTensor (A ⧸ I))) : Flat A N := by
  rw [iff_rTensor_injective]
  intro I _
  rw [injective_iff_map_eq_zero]
  intro w hw
  let ι : I →ₗ[A] A := I.subtype
  let q : A →ₗ[A] A ⧸ I := I.mkQ
  have hιq : Function.Exact ι q := by
    intro x
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩
  have hq : Function.Surjective q := Submodule.mkQ_surjective I
  obtain ⟨cI, rfl⟩ := LinearMap.lTensor_surjective I hg w
  have h₁ : g.lTensor A (ι.rTensor M cI) = 0 := by
    rw [← rTensor_lTensor_apply]
    exact hw
  obtain ⟨zA, hzA⟩ := ((_root_.lTensor_exact A hfg hg) _).1 h₁
  have h₂ : q.rTensor K zA = 0 := by
    refine h I ?_
    rw [map_zero, ← rTensor_lTensor_apply, hzA, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      hιq.linearMap_comp_eq_zero, LinearMap.rTensor_zero, LinearMap.zero_apply]
  obtain ⟨zI, hzI⟩ := ((_root_.rTensor_exact K hιq hq) _).1 h₂
  have h₃ : cI = f.lTensor I zI := by
    refine rTensor_preserves_injective_linearMap (M := M) ι Subtype.val_injective ?_
    rw [rTensor_lTensor_apply, hzI, hzA]
  rw [h₃, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hfg.linearMap_comp_eq_zero,
    LinearMap.lTensor_zero, LinearMap.zero_apply]

end Module.Flat
