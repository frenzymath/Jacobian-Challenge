import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Concrete homology of cochain complexes of modules

The homology of a cochain complex of modules is the quotient of cycles by
boundaries. For a complex indexed by the natural numbers, degree-zero homology
is the kernel of the first differential.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace CochainComplex

/-- The homology in degree `j` of a cochain complex of modules, as the quotient of the kernel of
the outgoing differential by the image of the incoming one. -/
noncomputable def homologyLinearEquivQuotient {R : Type u} [Ring R]
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (i j k : ℕ) (hi : (ComplexShape.up ℕ).prev j = i)
    (hk : (ComplexShape.up ℕ).next j = k) :
    K.homology j ≃ₗ[R] LinearMap.ker (K.d j k).hom ⧸
      LinearMap.range (K.sc' i j k).moduleCatToCycles :=
  ((K.homologyIsoSc' i j k hi hk) ≪≫ (K.sc' i j k).moduleCatHomologyIso).toLinearEquiv

/-- The homology in degree `0` of a cochain complex of modules is the kernel of the
differential. -/
noncomputable def homologyZeroLinearEquiv {R : Type u} [Ring R]
    (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    K.homology 0 ≃ₗ[R] LinearMap.ker (K.d 0 1).hom :=
  (K.homologyLinearEquivQuotient 0 0 1 (by simp) (by simp)).trans
    (Submodule.quotEquivOfEqBot _ (LinearMap.range_eq_bot.2 (LinearMap.ext fun x ↦
      Subtype.ext (by
        change (K.d 0 0).hom x = 0
        rw [K.shape 0 0 (by simp)]
        rfl))))

end CochainComplex
