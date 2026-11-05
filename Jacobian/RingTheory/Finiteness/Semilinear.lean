import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite generation under semilinear comparison

A bijective semilinear map transports finite generation over a smaller
coefficient ring to finite generation over the domain scalar ring.
-/

noncomputable section

namespace Module.Finite

/-- A bijective semilinear comparison with a module finite over a ring mapping
into the domain scalars makes the source finite over its own scalar ring. -/
theorem of_bijective_semilinear
    {domainRing targetRing coefficientRing sourceModule targetModule : Type*} [CommRing domainRing] [CommRing targetRing] [CommRing coefficientRing]
    {scalarMap : domainRing →+* targetRing} [AddCommGroup sourceModule] [Module domainRing sourceModule] [AddCommGroup targetModule] [Module targetRing targetModule]
    (comparison : sourceModule →ₛₗ[scalarMap] targetModule) (bijective : Function.Bijective comparison)
    (coefficientMap : coefficientRing →+* domainRing)
    (finite : letI := Module.compHom targetModule (scalarMap.comp coefficientMap); Module.Finite coefficientRing targetModule) :
    Module.Finite domainRing sourceModule := by
  letI := Module.compHom targetModule (scalarMap.comp coefficientMap)
  letI : Algebra coefficientRing domainRing := coefficientMap.toAlgebra
  letI : Module coefficientRing sourceModule := Module.compHom sourceModule coefficientMap
  letI : IsScalarTower coefficientRing domainRing sourceModule := ⟨fun a r m ↦ by
    change (coefficientMap a * r) • m = coefficientMap a • r • m
    rw [mul_smul]⟩
  let comparison' : sourceModule ≃ₗ[coefficientRing] targetModule :=
    { toFun := comparison
      map_add' := comparison.map_add
      map_smul' := fun a m ↦ comparison.map_smulₛₗ (coefficientMap a) m
      invFun := Function.surjInv bijective.2
      left_inv := Function.leftInverse_surjInv bijective
      right_inv := Function.rightInverse_surjInv bijective.2 }
  letI : Module.Finite coefficientRing sourceModule := Module.Finite.equiv comparison'.symm
  exact Module.Finite.of_restrictScalars_finite coefficientRing domainRing sourceModule

end Module.Finite
