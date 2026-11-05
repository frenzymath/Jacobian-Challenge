import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.NormTrace

/-!
# Norms and prime ideals in finite free algebras

The norm of an element belongs to a prime ideal exactly when the element belongs to
some prime lying over it. Equivalently, the norm is nonvanishing at a prime exactly when
the element is nonvanishing at every prime above it.
-/

set_option backward.isDefEq.respectTransparency false

open Module

namespace Algebra

variable {baseRing extensionRing : Type*} [CommRing baseRing] [CommRing extensionRing]
  [Algebra baseRing extensionRing]

/-- An element of a finite free algebra is a unit exactly when its norm is a unit. -/
theorem isUnit_norm_iff [Module.Free baseRing extensionRing] [Module.Finite baseRing extensionRing] {element : extensionRing} :
    IsUnit (Algebra.norm baseRing element) ↔ IsUnit element := by
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det]
  refine ⟨fun norm_isUnit ↦ ?_, fun element_isUnit ↦ element_isUnit.map (Algebra.lmul baseRing extensionRing)⟩
  obtain ⟨inverse, inverse_eq⟩ := ((Module.End.isUnit_iff _).mp norm_isUnit).2 1
  exact IsUnit.of_mul_eq_one inverse inverse_eq

/-- The norm belongs to a prime exactly when the element belongs to a prime above it. -/
theorem norm_mem_iff_exists_isPrime [Module.Free baseRing extensionRing] [Module.Finite baseRing extensionRing] (prime : Ideal baseRing)
    [prime.IsPrime] (element : extensionRing) : Algebra.norm baseRing element ∈ prime ↔
      ∃ overPrime : Ideal extensionRing, overPrime.IsPrime ∧ overPrime.comap (algebraMap baseRing extensionRing) = prime ∧ element ∈ overPrime := by
  classical
  let localizedExtension := Localization (Algebra.algebraMapSubmonoid extensionRing prime.primeCompl)
  let localizedBasis := (Module.Free.chooseBasis baseRing extensionRing).localizationLocalization (Localization.AtPrime prime)
    prime.primeCompl localizedExtension
  have : Module.Free (Localization.AtPrime prime) localizedExtension := .of_basis localizedBasis
  have : Module.Finite (Localization.AtPrime prime) localizedExtension := .of_basis localizedBasis
  rw [← not_iff_not, ← Ideal.mem_primeCompl_iff,
    ← IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime prime) prime,
    ← Algebra.norm_localization baseRing prime.primeCompl (Sₘ := localizedExtension), isUnit_norm_iff]
  have disjoint_primes (overPrime : Ideal extensionRing) (overPrime_isPrime : overPrime.comap (algebraMap baseRing extensionRing) ≤ prime) :
      Disjoint (Algebra.algebraMapSubmonoid extensionRing prime.primeCompl : Set extensionRing) overPrime := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨scalar, scalar_mem, rfl⟩ image_mem
    exact scalar_mem (overPrime_isPrime image_mem)
  refine ⟨fun unit_norm ⟨overPrime, overPrime_isPrime, prime_comap_eq, element_mem⟩ ↦ ?_, fun no_overPrime ↦ ?_⟩
  · have := IsLocalization.isPrime_of_isPrime_disjoint _ localizedExtension overPrime overPrime_isPrime (disjoint_primes overPrime prime_comap_eq.le)
    exact this.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ element_mem) unit_norm)
  · by_contra unit_norm
    obtain ⟨maximal, maximal_isMaximal, span_le⟩ := Ideal.exists_le_maximal (Ideal.span {algebraMap extensionRing localizedExtension element})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have comap_le : (maximal.comap (algebraMap extensionRing localizedExtension)).comap (algebraMap baseRing extensionRing) ≤ prime := by
      intro scalar scalar_mem
      by_contra scalar_notMem
      refine maximal_isMaximal.ne_top (maximal.eq_top_of_isUnit_mem scalar_mem ?_)
      exact IsLocalization.map_units localizedExtension (⟨algebraMap baseRing extensionRing scalar, scalar, scalar_notMem, rfl⟩ :
        Algebra.algebraMapSubmonoid extensionRing prime.primeCompl)
    obtain ⟨largerPrime, maximal_le, largerPrime_isPrime, largerPrime_comap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral prime _ comap_le
    exact no_overPrime ⟨largerPrime, largerPrime_isPrime, largerPrime_comap, maximal_le (span_le (Ideal.mem_span_singleton_self _))⟩

/-- The norm avoids a prime exactly when the element avoids every prime above it. -/
theorem norm_notMem_iff [Module.Free baseRing extensionRing]
    [Module.Finite baseRing extensionRing] (prime : Ideal baseRing) [prime.IsPrime]
    (element : extensionRing) : Algebra.norm baseRing element ∉ prime ↔
      ∀ overPrime : Ideal extensionRing, overPrime.IsPrime →
        overPrime.comap (algebraMap baseRing extensionRing) = prime → element ∉ overPrime := by
  simp only [norm_mem_iff_exists_isPrime, not_exists, not_and]

end Algebra
