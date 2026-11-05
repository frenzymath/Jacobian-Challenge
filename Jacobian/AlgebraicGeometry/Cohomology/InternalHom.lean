import Jacobian.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Jacobian.AlgebraicGeometry.Cohomology.Basic

/-!
# Cohomology of the internal hom

Global sections of the internal hom of module sheaves identify additively
with morphisms. The identification with degree-zero cohomology is natural
in the source and compatible with the action of global functions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{schemeUniverse}}

/-- A morphism `sourceModule ⟶ targetModule` of `𝒪_X`-modules, as a global section of the internal hom `Hom(sourceModule, targetModule)`. -/
def homToΓHomObj (sourceModule targetModule : scheme.Modules) :
    (sourceModule ⟶ targetModule) →+ Γ(SheafOfModules.homObj (R := scheme.sheaf) sourceModule targetModule, ⊤) where
  toFun morphism := (PresheafOfModules.restrictOver _ ⊤).map morphism.val
  map_zero' := rfl
  map_add' _ _ := rfl

lemma homToΓHomObj_injective (sourceModule targetModule : scheme.Modules) : Function.Injective (homToΓHomObj sourceModule targetModule) := by
  intro morphism otherMorphism equality
  ext sourceOpen element
  exact congr(($equality).app (op (Over.mk (homOfLE (le_top : sourceOpen ≤ ⊤)))) element)

/-- The compatible family of restrictions of a global section of the internal hom. -/
def ΓHomObjSections {sourceModule targetModule : scheme.Modules} (sectionValue : Γ(SheafOfModules.homObj (R := scheme.sheaf) sourceModule targetModule, ⊤)) :
    (SheafOfModules.homObj (R := scheme.sheaf) sourceModule targetModule).sections :=
  PresheafOfModules.sectionsMk
    (fun sourceOpen ↦ PresheafOfModules.restrictOverMap (homOfLE (le_top : sourceOpen.unop ≤ ⊤)) sectionValue)
    fun sourceOpen targetOpen restrictionMap ↦ by
      change PresheafOfModules.restrictOverMap restrictionMap.unop _ = _
      rw [← PresheafOfModules.restrictOverMap_comp]
      rfl

lemma homToΓHomObj_surjective (sourceModule targetModule : scheme.Modules) : Function.Surjective (homToΓHomObj sourceModule targetModule) := by
  intro sectionValue
  refine ⟨SheafOfModules.homObjSectionsEquiv sourceModule targetModule (ΓHomObjSections sectionValue), ?_⟩
  refine PresheafOfModules.hom_ext fun testOpen ↦ ?_
  ext element
  exact PresheafOfModules.restrictOver_hom_app_congr sectionValue (Subsingleton.elim _ _) element

/-- **Global sections of the internal hom**: `Γ(scheme, Hom(sourceModule, targetModule)) ≃ Hom(sourceModule, targetModule)`. -/
def ΓHomObjAddEquiv (sourceModule targetModule : scheme.Modules) :
    Γ(SheafOfModules.homObj (R := scheme.sheaf) sourceModule targetModule, ⊤) ≃+ (sourceModule ⟶ targetModule) :=
  (AddEquiv.ofBijective (homToΓHomObj sourceModule targetModule)
    ⟨homToΓHomObj_injective sourceModule targetModule, homToΓHomObj_surjective sourceModule targetModule⟩).symm

@[simp]
lemma homToΓHomObj_ΓHomObjAddEquiv {sourceModule targetModule : scheme.Modules}
    (sectionValue : Γ(SheafOfModules.homObj (R := scheme.sheaf) sourceModule targetModule, ⊤)) :
    homToΓHomObj sourceModule targetModule (ΓHomObjAddEquiv sourceModule targetModule sectionValue) = sectionValue :=
  (AddEquiv.ofBijective (homToΓHomObj sourceModule targetModule)
    ⟨homToΓHomObj_injective sourceModule targetModule, homToΓHomObj_surjective sourceModule targetModule⟩).apply_symm_apply sectionValue

lemma homToΓHomObj_comp {otherModule sourceModule targetModule : scheme.Modules} (restrictionMap : otherModule ⟶ sourceModule) (morphism : sourceModule ⟶ targetModule) :
    homToΓHomObj otherModule targetModule (restrictionMap ≫ morphism) =
      Hom.app (SheafOfModules.homObjMap (R := scheme.sheaf) restrictionMap (𝟙 targetModule)) ⊤ (homToΓHomObj sourceModule targetModule morphism) := by
  refine PresheafOfModules.hom_ext fun testOpen ↦ ?_
  ext element
  rfl

lemma homToΓHomObj_comp_smulHom {sourceModule targetModule : scheme.Modules} (morphism : sourceModule ⟶ targetModule) (scalar : Γ(scheme, ⊤)) :
    homToΓHomObj sourceModule targetModule (morphism ≫ targetModule.smulHom scalar) = scalar • homToΓHomObj sourceModule targetModule morphism := by
  refine PresheafOfModules.hom_ext fun testOpen ↦ ?_
  ext element
  rfl

lemma H.zeroLinearEquiv_map_homObj {sourceModule targetModule : scheme.Modules} (morphism : sourceModule ⟶ targetModule) (element : sourceModule.H 0) :
    H.zeroLinearEquiv targetModule (H.map morphism 0 element) = morphism.app ⊤ (H.zeroLinearEquiv sourceModule element) :=
  (Sheaf.H.equiv₀_naturality (hT := isTerminalTop)
    ((SheafOfModules.toSheaf scheme.ringCatSheaf).map morphism) element).symm

/-- **`H⁰` of the internal hom**: `H⁰(scheme, Hom(sourceModule, targetModule)) ≃ Hom(sourceModule, targetModule)`. -/
def homObjHZeroAddEquiv (sourceModule targetModule : scheme.Modules) :
    H (X := scheme) (SheafOfModules.homObj (R := scheme.sheaf) sourceModule targetModule) 0 ≃+ (sourceModule ⟶ targetModule) :=
  (H.zeroLinearEquiv _).toAddEquiv.trans (ΓHomObjAddEquiv sourceModule targetModule)

lemma homToΓHomObj_homObjHZeroAddEquiv {sourceModule targetModule : scheme.Modules}
    (element : H (X := scheme) (SheafOfModules.homObj (R := scheme.sheaf) sourceModule targetModule) 0) :
    homToΓHomObj sourceModule targetModule (homObjHZeroAddEquiv sourceModule targetModule element) = H.zeroLinearEquiv _ element :=
  homToΓHomObj_ΓHomObjAddEquiv _

/-- `homObjHZeroAddEquiv` is natural in the source. -/
lemma homObjHZeroAddEquiv_map {otherModule sourceModule targetModule : scheme.Modules} (restrictionMap : otherModule ⟶ sourceModule)
    (element : H (X := scheme) (SheafOfModules.homObj (R := scheme.sheaf) sourceModule targetModule) 0) :
    homObjHZeroAddEquiv otherModule targetModule (H.map (SheafOfModules.homObjMap (R := scheme.sheaf) restrictionMap (𝟙 targetModule)) 0 element) =
      restrictionMap ≫ homObjHZeroAddEquiv sourceModule targetModule element := by
  apply homToΓHomObj_injective
  rw [homToΓHomObj_homObjHZeroAddEquiv, homToΓHomObj_comp, homToΓHomObj_homObjHZeroAddEquiv,
    H.zeroLinearEquiv_map_homObj]

/-- `homObjHZeroAddEquiv` turns multiplication by a global function into composition with the
multiplication on the target. -/
lemma homObjHZeroAddEquiv_smul {sourceModule targetModule : scheme.Modules} (scalar : Γ(scheme, ⊤))
    (element : H (X := scheme) (SheafOfModules.homObj (R := scheme.sheaf) sourceModule targetModule) 0) :
    homObjHZeroAddEquiv sourceModule targetModule (scalar • element) = homObjHZeroAddEquiv sourceModule targetModule element ≫ targetModule.smulHom scalar := by
  apply homToΓHomObj_injective
  rw [homToΓHomObj_homObjHZeroAddEquiv, homToΓHomObj_comp_smulHom,
    homToΓHomObj_homObjHZeroAddEquiv, LinearEquiv.map_smul]

end AlgebraicGeometry.Scheme.Modules
