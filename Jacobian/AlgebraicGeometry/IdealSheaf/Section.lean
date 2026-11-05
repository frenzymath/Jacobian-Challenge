import Jacobian.AlgebraicGeometry.IdealSheaf.Kernel
import Jacobian.AlgebraicGeometry.IdealSheaf.RelativeCartier

/-!
# Sections of smooth relative curves

A section of a separated smooth morphism of relative dimension one is a
relative effective Cartier divisor. In particular, the kernel of restriction
of functions to the section is an invertible module sheaf.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {source baseScheme : Scheme.{u}}

/-- The closed subscheme defined by a section is isomorphic to the base. -/
theorem isIso_ker_subschemeι_comp_of_section (morphism : baseScheme ⟶ source)
    (projection : source ⟶ baseScheme) [IsSeparated projection]
    (section_eq : morphism ≫ projection = 𝟙 _) :
    IsIso (morphism.ker.subschemeι ≫ projection) := by
  haveI : IsClosedImmersion morphism := by
    haveI : IsClosedImmersion (morphism ≫ projection) := by
      rw [section_eq]
      infer_instance
    exact IsClosedImmersion.of_comp morphism projection
  let imageIso := asIso morphism.toImage
  have projection_eq : morphism.ker.subschemeι ≫ projection = imageIso.inv := by
    apply (cancel_epi imageIso.hom).mp
    change morphism.toImage ≫ (morphism.imageι ≫ projection) =
      imageIso.hom ≫ imageIso.inv
    rw [← Category.assoc, morphism.toImage_imageι, section_eq, imageIso.hom_inv_id]
  rw [projection_eq]
  infer_instance

/-- A section of a separated smooth relative curve is a relative effective Cartier divisor. -/
theorem isRelativeEffectiveCartier_ker_of_section (morphism : baseScheme ⟶ source)
    (projection : source ⟶ baseScheme) [IsSeparated projection]
    [SmoothOfRelativeDimension 1 projection] (section_eq : morphism ≫ projection = 𝟙 _) :
    morphism.ker.IsRelativeEffectiveCartier projection := by
  letI := morphism.isIso_ker_subschemeι_comp_of_section projection section_eq
  exact ⟨IdealSheafData.isInvertible_of_isFinite_of_flat projection
    inferInstance inferInstance inferInstance, inferInstance⟩

/-- The categorical kernel ideal of a section of a smooth relative curve is invertible. -/
theorem isInvertible_kernel_unitToPushforwardObjUnit_of_section
    (morphism : baseScheme ⟶ source) (projection : source ⟶ baseScheme)
    [IsSeparated projection] [SmoothOfRelativeDimension 1 projection]
    (section_eq : morphism ≫ projection = 𝟙 _) :
    (kernel (SheafOfModules.unitToPushforwardObjUnit morphism.toRingCatSheafHom)).IsInvertible := by
  haveI : IsClosedImmersion morphism := by
    haveI : IsClosedImmersion (morphism ≫ projection) := by
      rw [section_eq]
      infer_instance
    exact IsClosedImmersion.of_comp morphism projection
  letI : morphism.ker.toModules.IsInvertible :=
    (morphism.isRelativeEffectiveCartier_ker_of_section projection section_eq).1.isInvertible_toModules
  exact SheafOfModules.IsInvertible.of_iso.{u, u, u} morphism.kerToModulesIso

end AlgebraicGeometry.Scheme.Hom
