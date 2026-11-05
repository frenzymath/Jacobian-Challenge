import Jacobian.AlgebraicGeometry.Modules.Dual
import Jacobian.AlgebraicGeometry.Modules.Quasicoherent
import Jacobian.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Tensoring with an invertible module sheaf

Tensoring with a line bundle is an equivalence, with inverse given by tensoring with its
dual. Consequently it preserves short exact sequences. Local triviality also shows that
tensoring with a line bundle preserves quasi-coherence and finite presentation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Tensoring a quasi-coherent module with an invertible module preserves quasi-coherence. -/
theorem isQuasicoherent_tensorObj_of_isInvertible
    {scheme : Scheme.{u}} (moduleSheaf lineBundle : scheme.Modules)
    [moduleSheaf.IsQuasicoherent] [invertible : lineBundle.IsInvertible] :
    (moduleSheaf ⊗ lineBundle).IsQuasicoherent := by
  classical
  let tensorModule : scheme.Modules := moduleSheaf ⊗ lineBundle
  change tensorModule.IsQuasicoherent
  choose openSubset membership trivialization using
    fun point : scheme ↦ invertible.exists_isoUnit point
  letI (point : scheme) :
      (tensorModule.over (openSubset point)).IsQuasicoherent := by
    let comparison : tensorModule.over (openSubset point) ≅
        moduleSheaf.over (openSubset point) :=
      (overEquiv (openSubset point)).functor.preimageIso
        (overEquivObjOverIso tensorModule (openSubset point) ≪≫
          pullbackTensorObjIso (openSubset point).ι moduleSheaf lineBundle ≪≫
          (Iso.refl _ ⊗ᵢ (trivialization point).some) ≪≫ ρ_ _ ≪≫
          (overEquivObjOverIso moduleSheaf (openSubset point)).symm)
    exact (SheafOfModules.isQuasicoherent (scheme.ringCatSheaf.over (openSubset point))).prop_of_iso
      comparison.symm (SheafOfModules.isQuasicoherent_over moduleSheaf (openSubset point))
  refine SheafOfModules.IsQuasicoherent.of_coversTop tensorModule openSubset ?_
  rw [_root_.Opens.coversTop_iff]
  exact TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun point _ ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨point, membership point⟩)

/-- Tensoring with a line bundle preserves finite presentation without a
Noetherian hypothesis. -/
theorem isFinitePresentation_tensorObj_of_isInvertible
    {scheme : Scheme.{u}} (moduleSheaf lineBundle : scheme.Modules)
    [moduleSheaf.IsFinitePresentation] [invertible : lineBundle.IsInvertible] :
    (moduleSheaf ⊗ lineBundle).IsFinitePresentation := by
  classical
  let tensorModule : scheme.Modules := moduleSheaf ⊗ lineBundle
  change tensorModule.IsFinitePresentation
  choose openSubset membership trivialization using
    fun point : scheme ↦ invertible.exists_isoUnit point
  letI (point : scheme) : (moduleSheaf.over (openSubset point)).IsFinitePresentation :=
    SheafOfModules.isFinitePresentation_pushforward_of_isLeftAdjoint
      (Over.forget (openSubset point)) (𝟙 _) (Iso.refl _)
  letI (point : scheme) : (tensorModule.over (openSubset point)).IsFinitePresentation := by
    let comparison : tensorModule.over (openSubset point) ≅
        moduleSheaf.over (openSubset point) :=
      (overEquiv (openSubset point)).functor.preimageIso
        (overEquivObjOverIso tensorModule (openSubset point) ≪≫
          pullbackTensorObjIso (openSubset point).ι moduleSheaf lineBundle ≪≫
          (Iso.refl _ ⊗ᵢ (trivialization point).some) ≪≫ ρ_ _ ≪≫
          (overEquivObjOverIso moduleSheaf (openSubset point)).symm)
    exact (SheafOfModules.isFinitePresentation
      (scheme.ringCatSheaf.over (openSubset point))).prop_of_iso comparison.symm inferInstance
  refine SheafOfModules.IsFinitePresentation.of_coversTop tensorModule openSubset ?_
  rw [_root_.Opens.coversTop_iff]
  exact TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun point _ ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨point, membership point⟩)

/-- Tensoring by an invertible sheaf is an equivalence with inverse tensoring by its dual. -/
def tensorLeftEquivalence (L : X.Modules) [L.IsInvertible] : X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (tensorLeft L) (tensorLeft Lᵛ)
    ((tensorLeftTensor _ _).symm ≪≫
      (tensoringLeft X.Modules).mapIso
        ((β_ _ _) ≪≫ tensorObjDualIsoUnit L) ≪≫ leftUnitorNatIso X.Modules).symm
    ((tensorLeftTensor _ _).symm ≪≫
      (tensoringLeft X.Modules).mapIso (tensorObjDualIsoUnit L) ≪≫
        leftUnitorNatIso X.Modules)

instance tensorLeft_isEquivalence (L : X.Modules) [L.IsInvertible] :
    (tensorLeft L).IsEquivalence :=
  inferInstanceAs (tensorLeftEquivalence L).functor.IsEquivalence

/-- Right tensoring by a line bundle has inverse right tensoring by its dual. -/
def tensorRightEquivalence (L : X.Modules) [L.IsInvertible] : X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (tensorRight L) (tensorRight Lᵛ)
    ((tensorRightTensor L Lᵛ).symm ≪≫
      (tensoringRight X.Modules).mapIso (tensorObjDualIsoUnit L) ≪≫
        rightUnitorNatIso X.Modules).symm
    ((tensorRightTensor Lᵛ L).symm ≪≫
      (tensoringRight X.Modules).mapIso ((β_ _ _) ≪≫ tensorObjDualIsoUnit L) ≪≫
        rightUnitorNatIso X.Modules)

instance tensorRight_isEquivalence (L : X.Modules) [L.IsInvertible] :
    (tensorRight L).IsEquivalence :=
  inferInstanceAs (tensorRightEquivalence L).functor.IsEquivalence

/-- Tensoring a short exact sequence by an invertible sheaf preserves exactness. -/
theorem tensorLeft_shortExact (L : X.Modules) [L.IsInvertible]
    {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (tensorLeft L)).ShortExact :=
  hS.map_of_exact (tensorLeft L)

/-- The right tensor functor by a line bundle also preserves short exact sequences. -/
theorem tensorRight_shortExact (L : X.Modules) [L.IsInvertible]
    {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (tensorRight L)).ShortExact :=
  hS.map_of_exact (tensorRight L)

end AlgebraicGeometry.Scheme.Modules
