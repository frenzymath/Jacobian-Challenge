import Jacobian.AlgebraicGeometry.Modules.GlobalSection

/-!
# Degree-zero module Ext and global sections

Evaluation at one identifies morphisms from the structure sheaf with global
sections of any module sheaf. The degree-zero Ext/Hom equivalence therefore
identifies module Ext in degree zero with global sections, and hence with the
usual abelian-sheaf cohomology in degree zero. Both comparisons are additive
and natural in the coefficient sheaf; no geometric or finiteness hypothesis
is needed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Abelian Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{u}}

local instance : HasExt.{u + 1} scheme.Modules := HasExt.standard scheme.Modules

/-- Degree-zero module Ext is identified with global sections by evaluation at one. -/
def extZeroAddEquiv (moduleSheaf : scheme.Modules) :
    Ext.{u + 1} (unit scheme) moduleSheaf 0 ≃+
      Γ(moduleSheaf, ⊤) :=
  Ext.addEquiv₀.trans (unitHomAddEquiv moduleSheaf)

@[simp]
theorem extZeroAddEquiv_apply (moduleSheaf : scheme.Modules)
    (extension : Ext.{u + 1} (unit scheme) moduleSheaf 0) :
    extZeroAddEquiv moduleSheaf extension =
      (Ext.homEquiv₀ extension).app ⊤ (1 : Γ(scheme, ⊤)) := rfl

@[simp]
theorem extZeroAddEquiv_mk₀ (moduleSheaf : scheme.Modules)
    (morphism : unit scheme ⟶ moduleSheaf) :
    extZeroAddEquiv moduleSheaf (Ext.mk₀ morphism) =
      morphism.app ⊤ (1 : Γ(scheme, ⊤)) := by
  exact congrArg (unitHomAddEquiv moduleSheaf)
    ((Ext.addEquiv₀ (X := unit scheme) (Y := moduleSheaf)).apply_symm_apply morphism)

/-- The module-Ext and abelian-sheaf definitions of cohomology agree in degree zero. -/
def extZeroEquivH (moduleSheaf : scheme.Modules) :
    Ext.{u + 1} (unit scheme) moduleSheaf 0 ≃+
      moduleSheaf.H 0 :=
  (extZeroAddEquiv moduleSheaf).trans (H.zeroLinearEquiv moduleSheaf).toAddEquiv.symm

/-- Evaluation is natural under a morphism of coefficient sheaves. -/
theorem extZeroAddEquiv_naturality {moduleSheaf targetSheaf : scheme.Modules}
    (morphism : moduleSheaf ⟶ targetSheaf)
    (extension : Ext.{u + 1} (unit scheme) moduleSheaf 0) :
    extZeroAddEquiv targetSheaf (extension.comp (Ext.mk₀ morphism) (add_zero 0)) =
      morphism.app ⊤ (extZeroAddEquiv moduleSheaf extension) := by
  obtain ⟨sourceMorphism, rfl⟩ := (Ext.mk₀_bijective (unit scheme) moduleSheaf).2 extension
  exact (congrArg (extZeroAddEquiv targetSheaf)
    (Ext.mk₀_comp_mk₀ sourceMorphism morphism)).trans
      ((extZeroAddEquiv_mk₀ targetSheaf (sourceMorphism ≫ morphism)).trans
        (congrArg (morphism.app ⊤) (extZeroAddEquiv_mk₀ moduleSheaf sourceMorphism).symm))

end AlgebraicGeometry.Scheme.Modules
