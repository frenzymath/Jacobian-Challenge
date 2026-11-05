import Jacobian.RingTheory.LocalRing.ResidueField.RegularFiber
import Mathlib.RingTheory.IsTensorProduct

/-!
# Iterated algebra pushouts and prime lifts

Tensoring an intermediate base preserves an algebra pushout. Primes with the
same image in the base lift to primes of the pushout over the specified fiber.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

namespace Algebra.IsPushout

variable (R₀ A₁ A B₀ B : Type*) [CommRing R₀] [CommRing A₁] [CommRing A] [CommRing B₀]
  [CommRing B] [Algebra R₀ A₁] [Algebra A₁ A] [Algebra R₀ A] [IsScalarTower R₀ A₁ A]
  [Algebra R₀ B₀] [Algebra A B] [Algebra B₀ B] [Algebra R₀ B] [IsScalarTower R₀ A B]
  [IsScalarTower R₀ B₀ B] [Algebra.IsPushout R₀ A B₀ B]

/-- If `B = A ⊗[R₀] B₀` and `A₁ → A` is a map of `R₀`-algebras, the `A₁ ⊗[R₀] B₀`-algebra
structure on `B` given by `A₁ ⊗[R₀] B₀ → A ⊗[R₀] B₀ ≅ B`. -/
noncomputable abbrev tensorProductAlgebra : Algebra (A₁ ⊗[R₀] B₀) B :=
  (((Algebra.IsPushout.equiv R₀ A B₀ B).toAlgHom.restrictScalars R₀).comp
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ A₁ A) (AlgHom.id R₀ B₀))).toAlgebra

lemma tensorProductAlgebra_algebraMap_tmul (a : A₁) (b : B₀) :
    letI := tensorProductAlgebra R₀ A₁ A B₀ B
    algebraMap (A₁ ⊗[R₀] B₀) B (a ⊗ₜ b) =
      algebraMap A B (algebraMap A₁ A a) * algebraMap B₀ B b := by
  simp [RingHom.algebraMap_toAlgebra, Algebra.IsPushout.equiv_tmul]

variable [Algebra A₁ B] [IsScalarTower A₁ A B]

lemma isScalarTower_tensorProductAlgebra :
    letI := tensorProductAlgebra R₀ A₁ A B₀ B
    IsScalarTower A₁ (A₁ ⊗[R₀] B₀) B := by
  let := tensorProductAlgebra R₀ A₁ A B₀ B
  refine .of_algebraMap_eq fun r ↦ ?_
  rw [Algebra.TensorProduct.algebraMap_apply, tensorProductAlgebra_algebraMap_tmul,
    Algebra.algebraMap_self, RingHom.id_apply, map_one, mul_one,
    ← IsScalarTower.algebraMap_apply]

/-- If `B = A ⊗[R₀] B₀` and `A₁ → A` is a map of `R₀`-algebras, then
`B = A ⊗[A₁] (A₁ ⊗[R₀] B₀)`. -/
theorem tensorProduct :
    letI := tensorProductAlgebra R₀ A₁ A B₀ B
    haveI := isScalarTower_tensorProductAlgebra R₀ A₁ A B₀ B
    Algebra.IsPushout A₁ A (A₁ ⊗[R₀] B₀) B := by
  let := tensorProductAlgebra R₀ A₁ A B₀ B
  have := isScalarTower_tensorProductAlgebra R₀ A₁ A B₀ B
  let : Algebra (A₁ ⊗[R₀] B₀) (A ⊗[A₁] (A₁ ⊗[R₀] B₀)) := Algebra.TensorProduct.rightAlgebra
  refine Algebra.IsPushout.of_equiv ((Algebra.TensorProduct.cancelBaseChange R₀ A₁ A A B₀).trans
    (Algebra.IsPushout.equiv R₀ A B₀ B)) (RingHom.ext fun x ↦ ?_)
  induction x with
  | zero => simp
  | tmul a b =>
    simp [RingHom.algebraMap_toAlgebra, Algebra.IsPushout.equiv_tmul,
      Algebra.algebraMap_eq_smul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Algebra.IsPushout

namespace PrimeSpectrum

/-- A prime of a factor with the specified image in the base lifts to a prime of the pushout. -/
theorem exists_comap_eq_of_isPushout {A₁ A B₁ B : Type*} [CommRing A₁] [CommRing A]
    [CommRing B₁] [CommRing B] [Algebra A₁ A] [Algebra A₁ B₁] [Algebra A B] [Algebra B₁ B]
    [Algebra A₁ B] [IsScalarTower A₁ A B] [IsScalarTower A₁ B₁ B] [Algebra.IsPushout A₁ A B₁ B]
    {y : PrimeSpectrum A} (K : Type*) [Field K] [Algebra A K]
    (hK : RingHom.ker (algebraMap A K) = y.asIdeal) (q₁ : PrimeSpectrum B₁)
    (hq₁ : comap (algebraMap A₁ B₁) q₁ = comap (algebraMap A₁ A) y) :
    ∃ q : PrimeSpectrum B, comap (algebraMap A B) q = y ∧ comap (algebraMap B₁ B) q = q₁ := by
  let : Algebra A₁ K := ((algebraMap A K).comp (algebraMap A₁ A)).toAlgebra
  have : IsScalarTower A₁ A K := .of_algebraMap_eq fun _ ↦ rfl
  have hker : RingHom.ker (algebraMap A₁ K) = q₁.asIdeal.comap (algebraMap A₁ B₁) := by
    rw [IsScalarTower.algebraMap_eq A₁ A K, ← RingHom.comap_ker, hK, ← comap_asIdeal,
      ← comap_asIdeal, hq₁]
  obtain ⟨P, hP, hPq⟩ :=
    Algebra.exists_isPrime_comap_includeLeft_eq (Field.toIsField K) q₁.asIdeal hker
  let f : A →ₐ[A₁] B₁ ⊗[A₁] K :=
    (Algebra.TensorProduct.includeRight : K →ₐ[A₁] B₁ ⊗[A₁] K).comp
      (IsScalarTower.toAlgHom A₁ A K)
  let ψ : B →ₐ[A₁] B₁ ⊗[A₁] K := Algebra.pushoutDesc B f Algebra.TensorProduct.includeLeft
    fun _ _ ↦ mul_comm _ _
  have hbot : P.comap (Algebra.TensorProduct.includeRight : K →ₐ[A₁] B₁ ⊗[A₁] K).toRingHom = ⊥ :=
    Ideal.eq_bot_of_prime _
  have hψA (a : A) : ψ (algebraMap A B a) = f a := Algebra.pushoutDesc_left _ _ _ _ a
  have hψB (b : B₁) : ψ (algebraMap B₁ B b) = Algebra.TensorProduct.includeLeft b :=
    Algebra.pushoutDesc_right _ _ _ _ b
  refine ⟨comap (ψ : B →+* B₁ ⊗[A₁] K) ⟨P, hP⟩, ?_, ?_⟩
  · ext a
    rw [comap_asIdeal, comap_asIdeal, Ideal.mem_comap, Ideal.mem_comap]
    erw [hψA]
    rw [← hK, RingHom.mem_ker, ← Ideal.mem_bot, ← hbot, Ideal.mem_comap]
    rfl
  · ext b
    rw [comap_asIdeal, comap_asIdeal, Ideal.mem_comap, Ideal.mem_comap]
    erw [hψB]
    rw [← hPq, Ideal.mem_comap]
    rfl

end PrimeSpectrum
