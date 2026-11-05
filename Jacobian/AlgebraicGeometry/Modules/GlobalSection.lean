import Jacobian.AlgebraicGeometry.Modules.Sections
import Jacobian.AlgebraicGeometry.Modules.LocallyFree

/-!
# Global sections as structure-module morphisms

A global section of a module sheaf determines a morphism from the structure module sending one to that section.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}}

/-- The morphism `𝒪_X ⟶ M` corresponding to a global section `u` of `M`. -/
noncomputable def homOfGlobalSection (M : X.Modules) (u : Γ(M, ⊤)) :
    Modules.unit X ⟶ M :=
  (SheafOfModules.unitHomEquiv M).symm (_root_.PresheafOfModules.sectionsMk
    (fun W ↦ M.presheaf.map (homOfLE (le_top : W.unop ≤ ⊤)).op u)
    (fun _ _ f ↦ (presheaf_map_map_apply _ f.unop _).trans rfl))

/-- The morphism `𝒪_X ⟶ M` corresponding to a global section `u` sends `1` to `u`. -/
lemma homOfGlobalSection_app_one (M : X.Modules) (u : Γ(M, ⊤)) (U : X.Opens) :
    (homOfGlobalSection M u).app U (1 : Γ(X, U)) = M.presheaf.map (homOfLE le_top).op u :=
  congrArg (fun σ : M.sections ↦ σ.val (op U)) ((SheafOfModules.unitHomEquiv M).apply_symm_apply _)

/-- The morphism determined by a global section multiplies its restriction by the input. -/
lemma homOfGlobalSection_app (M : X.Modules) (sectionValue : Γ(M, ⊤))
    (openSubset : X.Opens) (scalar : Γ(X, openSubset)) :
    (homOfGlobalSection M sectionValue).app openSubset scalar =
      scalar • M.presheaf.map (homOfLE (le_top : openSubset ≤ ⊤)).op sectionValue := by
  have scalar_one : scalar = scalar • (1 : Γ(X, openSubset)) := (mul_one scalar).symm
  conv_lhs => rw [scalar_one]
  rw [Hom.app_smul, homOfGlobalSection_app_one]

/-- Evaluation at one identifies morphisms from the structure sheaf with global sections. -/
def unitHomAddEquiv (moduleSheaf : X.Modules) :
    (unit X ⟶ moduleSheaf) ≃+ Γ(moduleSheaf, ⊤) where
  toFun morphism := morphism.app ⊤ (1 : Γ(X, ⊤))
  invFun := homOfGlobalSection moduleSheaf
  left_inv morphism := by
    apply moduleSheaf.unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro openSubset
    change (homOfGlobalSection moduleSheaf
      (morphism.app ⊤ (1 : Γ(X, ⊤)))).app openSubset.unop
          (1 : Γ(X, openSubset.unop)) =
        morphism.app openSubset.unop (1 : Γ(X, openSubset.unop))
    refine (homOfGlobalSection_app_one moduleSheaf _ openSubset.unop).trans ?_
    have naturality := Hom.app_presheaf_map morphism
      (homOfLE (le_top (a := openSubset.unop))) (1 : Γ(X, ⊤))
    change morphism.app openSubset.unop
      (X.presheaf.map (homOfLE le_top).op (1 : Γ(X, ⊤))) = _ at naturality
    rw [map_one] at naturality
    exact naturality.symm
  right_inv sectionValue := by
    refine (homOfGlobalSection_app_one moduleSheaf sectionValue ⊤).trans ?_
    change moduleSheaf.presheaf.map (𝟙 (op ⊤)) sectionValue = sectionValue
    simp
  map_add' _ _ := rfl

@[simp]
theorem unitHomAddEquiv_apply (moduleSheaf : X.Modules)
    (morphism : unit X ⟶ moduleSheaf) :
    unitHomAddEquiv moduleSheaf morphism = morphism.app ⊤ (1 : Γ(X, ⊤)) := rfl

@[simp]
theorem unitHomAddEquiv_symm_apply (moduleSheaf : X.Modules)
    (sectionValue : Γ(moduleSheaf, ⊤)) :
    (unitHomAddEquiv moduleSheaf).symm sectionValue =
      homOfGlobalSection moduleSheaf sectionValue := rfl

end AlgebraicGeometry.Scheme.Modules
