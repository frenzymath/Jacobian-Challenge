import Jacobian.AlgebraicGeometry.GlobalSections.BaseChange
import Jacobian.AlgebraicGeometry.Modules.PushforwardUnit
import Jacobian.AlgebraicGeometry.Modules.LocalIsomorphism

/-!
# Structure sheaves after base change

For a quasi-compact quasi-separated scheme over a field with constant global
functions, every base change has the base structure sheaf as its pushforward.
Proper geometrically integral schemes satisfy this criterion in every dimension.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {baseField : Type schemeUniverse} [Field baseField]
  {source : Scheme.{schemeUniverse}} [source.Over (Spec (.of baseField))]

/-- The structure module pushes forward to the base structure module after any base change. -/
theorem isIso_pushforwardUnitMap_pullback_snd
    [CompactSpace source] [QuasiSeparatedSpace source]
    [IsIso (source ↘ Spec (.of baseField)).appTop]
    (parameter : Over (Spec (.of baseField))) :
    IsIso (pushforwardUnitMap (pullback.snd (source ↘ Spec (.of baseField)) parameter.hom)) := by
  refine Modules.isIso_of_bijective_app_of_isAffineOpen _ fun openSubset affineOpen ↦ ?_
  have := Scheme.isIso_app_of_isPullback_of_isIso_appTop
    (IsPullback.of_hasPullback (source ↘ Spec (.of baseField)) parameter.hom) affineOpen
  have functionEquation :
      (Modules.Hom.app
        (pushforwardUnitMap (pullback.snd (source ↘ Spec (.of baseField)) parameter.hom))
        openSubset : Γ(parameter.left, openSubset) → _) =
        ((pullback.snd (source ↘ Spec (.of baseField)) parameter.hom).app openSubset :
          Γ(parameter.left, openSubset) → _) :=
    funext (pushforwardUnitMap_app _ openSubset)
  exact functionEquation.symm ▸ ConcreteCategory.bijective_of_isIso
    ((pullback.snd (source ↘ Spec (.of baseField)) parameter.hom).app openSubset)

/-- Proper geometrically integral schemes have universally trivial structure-sheaf pushforward. -/
theorem isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral
    [IsProper (source ↘ Spec (.of baseField))]
    [GeometricallyIntegral (source ↘ Spec (.of baseField))]
    (parameter : Over (Spec (.of baseField))) :
    IsIso (pushforwardUnitMap (pullback.snd (source ↘ Spec (.of baseField)) parameter.hom)) := by
  have : CompactSpace source :=
    QuasiCompact.compactSpace_of_compactSpace (source ↘ Spec (.of baseField))
  have : QuasiSeparatedSpace source :=
    quasiSeparatedSpace_of_quasiSeparated (source ↘ Spec (.of baseField))
  have : IsIso (source ↘ Spec (.of baseField)).appTop :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_appTop_of_isProper_of_geometricallyIntegral (source ↘ Spec (.of baseField)))
  exact isIso_pushforwardUnitMap_pullback_snd parameter

end AlgebraicGeometry
