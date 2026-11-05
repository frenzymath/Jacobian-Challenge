import Jacobian.AlgebraicGeometry.Modules.RestrictionLimits
import Jacobian.AlgebraicGeometry.Modules.Vanishing
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-!
# Restriction and kernels

These lemmas record the kernel and cokernel consequences of a morphism becoming
an isomorphism, or having a zero source or target, after restriction to an open.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)

/-- The kernel of a morphism vanishes on any open on which the morphism is an isomorphism. -/
lemma isZero_restrict_kernel_of_isIso [IsIso ((restrictFunctor U.ι).map φ)] :
    IsZero ((kernel φ).restrict U.ι) :=
  (isZero_kernel_of_mono ((restrictFunctor U.ι).map φ)).of_iso
    (PreservesKernel.iso (restrictFunctor U.ι) φ)

/-- The cokernel of a morphism vanishes on any open on which the morphism is an isomorphism. -/
lemma isZero_restrict_cokernel_of_isIso [IsIso ((restrictFunctor U.ι).map φ)] :
    IsZero ((cokernel φ).restrict U.ι) :=
  (isZero_cokernel_of_epi ((restrictFunctor U.ι).map φ)).of_iso
    (PreservesCokernel.iso (restrictFunctor U.ι) φ)

/-- The kernel of a morphism vanishes on any open on which its source vanishes. -/
lemma isZero_restrict_kernel_of_isZero (h : IsZero (M.restrict U.ι)) :
    IsZero ((kernel φ).restrict U.ι) :=
  (isZero_restrict_iff _ U).mpr fun V hV ↦ ⟨fun _ _ ↦ injective_kernelι_app φ V
    (((isZero_restrict_iff M U).mp h V hV).elim _ _)⟩

/-- The cokernel of a morphism vanishes on any open on which its target vanishes. -/
lemma isZero_restrict_cokernel_of_isZero (h : IsZero (N.restrict U.ι)) :
    IsZero ((cokernel φ).restrict U.ι) := by
  have : IsZero (cokernel ((restrictFunctor U.ι).map φ)) := by
    refine (IsZero.iff_id_eq_zero _).mpr (coequalizer.hom_ext ?_)
    exact h.eq_of_src _ _
  exact this.of_iso (PreservesCokernel.iso (restrictFunctor U.ι) φ)

end AlgebraicGeometry.Scheme.Modules
