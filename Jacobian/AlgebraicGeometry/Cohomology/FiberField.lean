import Jacobian.AlgebraicGeometry.Cohomology.Fiber
import Jacobian.AlgebraicGeometry.Cohomology.Isomorphism
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Fibers over a field

The unique residue-field fiber of a scheme over a field is the scheme itself,
up to scheme and scalar-field isomorphisms. Its cohomology dimensions and Euler
characteristic therefore agree with those of the original module sheaf.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Cohomology dimensions on the residue fiber over a field are the original ones. -/
theorem hFiber_eq_finrankH {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    (M : X.Modules) (q : ℕ) (s : Spec (.of k)) :
    M.hFiber f q s =
      (letI : X.Over (Spec (.of k)) := ⟨f⟩; M.finrankH k q) := by
  let φ := (Spec (.of k)).fromSpecResidueField s
  have : IsClosedImmersion φ := isClosed_singleton_iff_isClosedImmersion.1 (by
    rw [← (Set.subsingleton_of_subsingleton).eq_singleton_of_mem (Set.mem_univ s)]
    exact isClosed_univ)
  have : Surjective φ := ⟨fun t ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
  have : IsIso φ := isIso_of_isClosedImmersion_of_surjective φ
  have : IsIso (f.fiberι s) := by unfold Scheme.Hom.fiberι; infer_instance
  have : IsIso (Spec.preimage φ) := by
    have : IsIso (Scheme.Spec.map (Spec.preimage φ).op) := by
      change IsIso (Spec.map (Spec.preimage φ))
      rw [Spec.map_preimage]
      infer_instance
    have := isIso_of_reflects_iso (Spec.preimage φ).op Scheme.Spec
    exact isIso_of_op _
  have hfac : f.fiberι s ≫ f =
      f.fiberToSpecResidueField s ≫ Spec.map (Spec.preimage φ) := by
    rw [Spec.map_preimage]
    exact pullback.condition
  refine (finrankH_eq_of_comp_specMap (k := k)
    (L := (Spec (.of k)).residueField s) (Spec.preimage φ)
    (f.fiberToSpecResidueField s) _ q).symm.trans ?_
  rw [← hfac]
  exact finrankH_pullback_of_isIso (f.fiberι s) f M q

/-- The residue-fiber Euler characteristic over a field is the original one. -/
theorem eulerCharFiber_eq_eulerChar {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (M : X.Modules) (s : Spec (.of k)) :
    M.eulerCharFiber f s =
      (letI : X.Over (Spec (.of k)) := ⟨f⟩; M.eulerChar k) := by
  simp only [eulerCharFiber, eulerChar, hFiber_eq_finrankH f M _ s]

end AlgebraicGeometry.Scheme.Modules
