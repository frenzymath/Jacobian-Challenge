import Jacobian.AlgebraicGeometry.Modules.Limits

/-!
# Limits and restriction to open subschemes

Restriction preserves limits because the underlying presheaf is obtained by
precomposition, and the forgetful functor preserves and reflects limits.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction along an open immersion preserves limits. -/
noncomputable instance preservesLimitsOfSize_restrictFunctor
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesLimitsOfSize.{u,u} (restrictFunctor f) := by
  have : PreservesLimitsOfSize.{u,u}
      ((Functor.whiskeringLeft X.Opensᵒᵖ Y.Opensᵒᵖ Ab.{u}).obj f.opensFunctor.op) :=
    preservesLimits_of_evaluation _ fun U ↦ inferInstanceAs
      (PreservesLimitsOfSize.{u,u}
        ((CategoryTheory.evaluation _ _).obj (f.opensFunctor.op.obj U)))
  have : PreservesLimitsOfSize.{u,u} (restrictFunctor f ⋙ toPresheaf X) :=
    inferInstanceAs (PreservesLimitsOfSize.{u,u}
      (toPresheaf Y ⋙ (Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op))
  have : ReflectsLimitsOfSize.{u,u} (toPresheaf X) := reflectsLimits_of_reflectsIsomorphisms
  exact preservesLimits_of_reflects_of_preserves (restrictFunctor f) (toPresheaf X)

end AlgebraicGeometry.Scheme.Modules
