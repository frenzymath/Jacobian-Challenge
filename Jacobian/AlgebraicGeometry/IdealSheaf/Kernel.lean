import Jacobian.AlgebraicGeometry.IdealSheaf.Modules
import Jacobian.AlgebraicGeometry.Modules.Invertible
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The ideal module of a closed immersion

The ideal module of the scheme-theoretic image of a closed immersion is the
kernel of restriction of functions to its source. The comparison uses the
isomorphism from the source to its scheme-theoretic image.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {source middle target : Scheme.{u}}

/-- Restriction of functions to a composite factors through the intermediate scheme. -/
theorem unitToPushforwardObjUnit_comp (first : source ⟶ middle) (second : middle ⟶ target) :
    SheafOfModules.unitToPushforwardObjUnit (first ≫ second).toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit second.toRingCatSheafHom ≫
        (pushforward second).map
          (SheafOfModules.unitToPushforwardObjUnit first.toRingCatSheafHom) ≫
        (pushforwardComp first second).hom.app (SheafOfModules.unit source.ringCatSheaf) := by
  apply hom_ext
  intro openSubset
  ext value
  rfl

private theorem isIso_unitToPushforwardObjUnit (morphism : source ⟶ target)
    [IsIso morphism] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit morphism.toRingCatSheafHom) := by
  apply Hom.isIso_iff_isIso_app.mpr
  intro openSubset
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (fun value : Γ(target, openSubset) ↦ morphism.app openSubset value)
  exact ConcreteCategory.bijective_of_isIso (morphism.app openSubset)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

variable {source target : Scheme.{u}}

/-- A closed immersion has the same ideal module as its scheme-theoretic image. -/
def kerToModulesIso (morphism : source ⟶ target) [IsClosedImmersion morphism] :
    morphism.ker.toModules ≅
      kernel (SheafOfModules.unitToPushforwardObjUnit morphism.toRingCatSheafHom) := by
  letI := Modules.isIso_unitToPushforwardObjUnit morphism.toImage
  let codomainIso :=
    (Modules.pushforward morphism.imageι).mapIso
        (asIso (SheafOfModules.unitToPushforwardObjUnit morphism.toImage.toRingCatSheafHom)) ≪≫
      (Modules.pushforwardComp morphism.toImage morphism.imageι).app
        (SheafOfModules.unit source.ringCatSheaf)
  have compatibility : morphism.ker.toPushforwardSubscheme ≫ codomainIso.hom =
      SheafOfModules.unitToPushforwardObjUnit
        (morphism.toImage ≫ morphism.imageι).toRingCatSheafHom :=
    (Modules.unitToPushforwardObjUnit_comp morphism.toImage morphism.imageι).symm
  exact (kernelCompMono morphism.ker.toPushforwardSubscheme codomainIso.hom).symm ≪≫
    kernelIsoOfEq compatibility ≪≫
    eqToIso (congrArg (fun arrow : source ⟶ target ↦
      kernel (SheafOfModules.unitToPushforwardObjUnit arrow.toRingCatSheafHom))
      morphism.toImage_imageι)

end AlgebraicGeometry.Scheme.Hom
