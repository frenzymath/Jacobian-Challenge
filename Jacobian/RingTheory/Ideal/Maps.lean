import Mathlib.RingTheory.Ideal.Maps

/-!
# Generators and kernels of surjective ring maps

Generators of the image of an ideal lift to generators of the ideal modulo the kernel.
-/

namespace Ideal

/-- Generators of the image of an ideal generate the original ideal together with the kernel. -/
theorem eq_span_sup_ker_of_map_eq_span {R S : Type*} [Ring R] [Ring S] {f : R →+* S}
    (hf : Function.Surjective f) {I : Ideal R} (hI : RingHom.ker f ≤ I) {s : Set R}
    (h : I.map f = span (f '' s)) : I = span s ⊔ RingHom.ker f := by
  rw [← comap_map_of_surjective' f hf (span s), map_span, ← h, comap_map_of_surjective' f hf,
    sup_eq_left.2 hI]

end Ideal
