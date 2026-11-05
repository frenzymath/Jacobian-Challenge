import Jacobian.AlgebraicGeometry.Modules.Sections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Kernels and sections of module sheaves

Evaluation preserves kernels, so the sections of a kernel sheaf are the kernel of the
map on sections. The comparison respects the kernel inclusion.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A monomorphism of module sheaves is injective on sections over every open. -/
lemma injective_app_of_mono (f : M ⟶ N) [Mono f] {U : X.Opens} :
    Function.Injective (f.app U) :=
  (ModuleCat.mono_iff_injective
    ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f)).mp inferInstance

local instance (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Evaluation identifies the categorical sheaf kernel with the kernel of the
actual linear map on sections. No quasicoherence hypothesis is needed. -/
def sectionsKernelIso {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj (kernel f) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op U))
        ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f).hom.ker :=
  PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (op U)) f ≪≫
    ModuleCat.kernelIsoKer ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f)

set_option backward.isDefEq.respectTransparency false in
/-- This isomorphism preserves the inclusion into sections of the source. -/
theorem sectionsKernelIso_hom_subtype {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) :
    (sectionsKernelIso f U).hom ≫
      ModuleCat.ofHom
        ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f).hom.ker.subtype =
      (SheafOfModules.evaluation X.ringCatSheaf (op U)).map (kernel.ι f) := by
  simp only [sectionsKernelIso, Iso.trans_hom, Category.assoc,
    ModuleCat.kernelIsoKer_hom_ker_subtype]
  rw [PreservesKernel.iso_hom]
  simp

/-- Evaluation of a kernel section preserves its inclusion in the source. -/
lemma sectionsKernelIso_val (f : M ⟶ N) (U : X.Opens)
    (s : Γ(kernel f, U)) :
    ((sectionsKernelIso f U).hom s).val =
      (kernel.ι f).app U s := by
  exact ConcreteCategory.congr_hom
    (sectionsKernelIso_hom_subtype f U) s

/-- The range of the kernel inclusion is the kernel of the map on sections. -/
lemma range_kernelι_app (f : M ⟶ N) (U : X.Opens) :
    Set.range ((kernel.ι f).app U) = {x | f.app U x = 0} := by
  let e := (sectionsKernelIso f U).toLinearEquiv
  have he (s : Γ(kernel f, U)) : (e s).val = (kernel.ι f).app U s :=
    sectionsKernelIso_val f U s
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    rw [← he]
    exact (e s).property
  · intro hx
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    rw [← he, e.apply_symm_apply]

/-- Kernel inclusions are injective on sections. -/
lemma injective_kernelι_app (f : M ⟶ N) (U : X.Opens) :
    Function.Injective ((kernel.ι f).app U) := by
  let e := (sectionsKernelIso f U).toLinearEquiv
  intro a b h
  apply e.injective
  apply Subtype.ext
  exact (sectionsKernelIso_val f U a).trans
    (h.trans (sectionsKernelIso_val f U b).symm)

end AlgebraicGeometry.Scheme.Modules
