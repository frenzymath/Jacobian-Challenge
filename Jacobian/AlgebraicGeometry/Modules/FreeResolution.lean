import Jacobian.Algebra.Homology.CochainComplex.Truncation
import Jacobian.AlgebraicGeometry.Modules.FinitePresentation

/-!
# Finite presentation in free resolutions

The degree-zero opcycle of a complex of finite free module sheaves has a finite
global presentation: it is the cokernel of the incoming differential. This is
the degree-zero term of the canonical nonnegative quotient truncation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The degree-zero opcycle of a complex of finite free module sheaves is
finitely presented, without any noetherian assumption. -/
theorem finitePresentation_opcycles_zero {X : Scheme.{u}}
    (Q : CochainComplex X.Modules ℤ)
    (hfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := X.ringCatSheaf) (ULift.{u} (Fin r)))) :
    (Q.opcycles 0).IsFinitePresentation := by
  obtain ⟨m, ⟨em⟩⟩ := hfree (-1)
  obtain ⟨n, ⟨en⟩⟩ := hfree 0
  let f := em.inv ≫ Q.d (-1) 0 ≫ en.hom
  let g := en.inv ≫ Q.pOpcycles 0
  have hfg : f ≫ g = 0 := by simp [f, g]
  have hg : IsColimit (CokernelCofork.ofπ g hfg) :=
    IsCokernel.ofIso (Q.d (-1) 0) (Q.opcyclesIsCokernel (-1) 0 (by simp))
      (CokernelCofork.ofπ g hfg) em en (Iso.refl _) (by simp [f]) (by simp [g])
  let P := SheafOfModules.presentationOfIsCokernelFree f g hfg hg
  letI : P.IsFinite :=
    ⟨⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩,
      ⟨inferInstanceAs (Finite (ULift.{u} (Fin m)))⟩⟩
  exact P.isFinitePresentation

end AlgebraicGeometry.Scheme.Modules
