import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechResolution

/-!
# Cech resolutions with relatively affine intersections

A finite cover with intersections affine over the base gives a pushforward-acyclic
Cech resolution, without requiring the base itself to be affine.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- For an open `V` of a scheme `X` separated over `S` with `V ⟶ S` affine and a quasi-coherent
`ℱ`, the module `j_* (ℱ|_V)` is `f_*`-acyclic: the inclusion `j : V ⟶ X` and the composite
`V ⟶ S` are affine morphisms. -/
theorem rightAcyclic_extendRestrict_of_isAffineHom [IsSeparated f]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules) [ℱ.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineHom (V.ι ≫ f)) :
    (pushforward f).rightAcyclic ((extendRestrictFunctor V).obj ℱ) := by
  have := isGrothendieckAbelian V
  have : IsAffineHom V.ι := IsAffineHom.of_comp V.ι f
  exact rightAcyclic_pushforward_obj_of_isZero V.ι f _
    (fun q ↦ isZero_higherDirectImage_of_isAffineHom _ _ q.succ_pos)
    (fun q ↦ isZero_higherDirectImage_of_isAffineHom _ _ q.succ_pos)

variable {ι : Type u} (U : ι → X.Opens)

/-- The terms of the Čech complex are `f_*`-acyclic, for a finite cover whose finite
intersections are affine over the base and a quasi-coherent module. -/
theorem rightAcyclic_cechResolution_X_of_isAffineHom [IsSeparated f] [Finite ι]
    [HasInjectiveResolutions X.Modules]
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineHom ((⨅ l, U (y l)).ι ≫ f)) (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] (k : ℕ) : (pushforward f).rightAcyclic ((cechResolution U ℱ).X k) := by
  have : (pushforward f).rightAcyclic.IsClosedUnderFiniteProducts := .mk'
  change (pushforward f).rightAcyclic
    (∏ᶜ fun y : Fin (k + 1) → ι ↦ (cechPresheaf ℱ).obj (Opposite.op (∏ᶜ fun l ↦ U (y l))))
  refine ObjectProperty.prop_product _ fun y ↦ ?_
  exact rightAcyclic_extendRestrict_of_isAffineHom f ℱ ((piObj_eq_iInf U y).symm ▸ hU k y)

/-- **The Čech resolution computes the higher direct images over an arbitrary base.** Let
`f : X ⟶ S` be separated, `U` a finite cover of `X` whose finite intersections are affine over
`S`, and `ℱ` a quasi-coherent `𝒪_X`-module. Then `R^q f_* ℱ` is the `q`-th cohomology sheaf of
the complex `f_* Č(U, ℱ)` of `𝒪_S`-modules. -/
noncomputable def higherDirectImageIsoCechResolutionOfIsAffineHom [IsSeparated f] [Finite ι]
    [HasInjectiveResolutions X.Modules]
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineHom ((⨅ l, U (y l)).ι ≫ f))
    (hU' : ⨆ i, U i = ⊤) (ℱ : X.Modules) [ℱ.IsQuasicoherent] (q : ℕ) :
    (higherDirectImage f q).obj ℱ ≅
      (((pushforward f).mapHomologicalComplex _).obj (cechResolution U ℱ)).homology q :=
  have := quasiIso_cechResolutionι U ℱ hU'
  (pushforward f).rightDerivedObjIsoOfResolution (cechResolutionι U ℱ)
    (rightAcyclic_cechResolution_X_of_isAffineHom f U hU ℱ) q

end AlgebraicGeometry.Scheme.Modules
