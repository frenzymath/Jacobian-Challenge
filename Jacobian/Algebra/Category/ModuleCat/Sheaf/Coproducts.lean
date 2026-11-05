import Jacobian.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
import Jacobian.Algebra.Category.ModuleCat.Sheaf.Colimits
import Jacobian.CategoryTheory.Limits.Shapes.Coproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Presentations of coproducts of module sheaves

A coproduct of presentations presents the coproduct. Its generators and
relations are the disjoint unions of those of the given presentations. Finite
coproducts of finite presentations are finite presentations.
-/

noncomputable section
universe u v₁ u₁
open CategoryTheory Limits
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SheafOfModules
section Sigma

variable {categoryType : Type u₁} [Category.{v₁} categoryType] {topology : GrothendieckTopology categoryType} {ringSheaf : Sheaf topology RingCat.{u}}
  [HasSheafify topology AddCommGrpCat.{u}] [topology.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A presentation of a coproduct.** Presentations of the sheaves of modules `M i` give a
presentation of `∐ M`, with generators and relations the disjoint unions of those of the `M i`:
the cokernel of `∐ free (relations i) ⟶ ∐ free (generators i)` is `∐ M`. -/
noncomputable def Presentation.sigma {indexType : Type u} (family : indexType → SheafOfModules.{u} ringSheaf)
    (presentations : ∀ index, (family index).Presentation) : (∐ family).Presentation :=
  letI eI := (freeFunctor (R := ringSheaf)).mapIso (Types.coproductIso fun index ↦ (presentations index).generators.I).symm ≪≫
    PreservesCoproduct.iso (freeFunctor (R := ringSheaf)) fun index ↦ (presentations index).generators.I
  letI eJ := (freeFunctor (R := ringSheaf)).mapIso (Types.coproductIso fun index ↦ (presentations index).relations.I).symm ≪≫
    PreservesCoproduct.iso (freeFunctor (R := ringSheaf)) fun index ↦ (presentations index).relations.I
  presentationOfIsCokernelFree
    (eJ.hom ≫ Limits.Sigma.map (fun index ↦ (freeHomEquiv _).symm (presentations index).relations.s ≫ kernel.ι _) ≫
      eI.inv)
    (eI.hom ≫ Limits.Sigma.map fun index ↦ (presentations index).generators.π) (by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [Sigma.map_comp_map]
      convert comp_zero
      exact Sigma.hom_ext _ _ fun index ↦ by simp)
    (IsCokernel.ofIso _ (isColimitCokernelCoforkSigmaMap _ _ _ fun index ↦ (presentations index).isColimit) _ eJ.symm
      eI.symm (Iso.refl _) (by simp) (by simp))

instance Presentation.isFinite_sigma {indexType : Type u} [Finite indexType] (family : indexType → SheafOfModules.{u} ringSheaf)
    (presentations : ∀ index, (family index).Presentation) [∀ index, (presentations index).IsFinite] : (Presentation.sigma family presentations).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite (Σ index, (presentations index).generators.I))⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite (Σ index, (presentations index).relations.I))⟩

end Sigma
end SheafOfModules
