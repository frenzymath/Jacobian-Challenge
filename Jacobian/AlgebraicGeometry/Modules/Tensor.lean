import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Jacobian.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-!
# Tensor products of module sheaves

The tensor product of module sheaves is the sheafification of the sectionwise
tensor product of their underlying presheaves. Localization gives the category
of module sheaves its symmetric monoidal structure and makes sheafification a
monoidal functor.

## References

* [The Stacks Project, Section 17.16: Tensor product](https://stacks.math.columbia.edu/tag/01CA)
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

open MonoidalCategory

variable {scheme : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise tensor product makes module presheaves a monoidal category. -/
noncomputable instance presheafMonoidalCategory : MonoidalCategory scheme.PresheafOfModules :=
  inferInstanceAs
    (MonoidalCategory
      (_root_.PresheafOfModules.{u} (scheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise tensor product of module presheaves is symmetric. -/
noncomputable instance presheafSymmetricCategory : SymmetricCategory scheme.PresheafOfModules :=
  inferInstanceAs
    (SymmetricCategory
      (_root_.PresheafOfModules.{u} (scheme.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

set_option backward.isDefEq.respectTransparency false in
/-- Tensor product over the structure sheaf makes module sheaves a monoidal category. -/
noncomputable instance monoidalCategory : MonoidalCategory scheme.Modules :=
  SheafOfModules.monoidalCategory scheme.sheaf

set_option backward.isDefEq.respectTransparency false in
/-- Tensor product of module sheaves is symmetric. -/
noncomputable instance symmetricCategory : SymmetricCategory scheme.Modules :=
  SheafOfModules.symmetricCategory scheme.sheaf

variable (scheme) in
/-- Sheafification of module presheaves on a scheme. -/
noncomputable def sheafification : scheme.PresheafOfModules ⥤ scheme.Modules :=
  _root_.PresheafOfModules.sheafification (𝟙 scheme.ringCatSheaf.obj)

set_option backward.isDefEq.respectTransparency false in
/-- Sheafification of module presheaves preserves the tensor product and its unit. -/
noncomputable instance sheafificationMonoidal : (sheafification scheme).Monoidal :=
  SheafOfModules.sheafificationMonoidal scheme.sheaf

end AlgebraicGeometry.Scheme.Modules
