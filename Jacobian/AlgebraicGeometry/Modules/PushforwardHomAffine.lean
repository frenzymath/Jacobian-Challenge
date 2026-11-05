import Jacobian.AlgebraicGeometry.Modules.PushforwardHom

/-!
# Affine determination of morphisms from a pushforward

When an affine open and its preimage are affine, a morphism out of the
pushforward of the structure sheaf is determined by sections on that open.
Localization determines its values on basic opens, and sheaf locality
then determines it on every smaller open.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


universe moduleMorphism

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {sourceScheme targetScheme : Scheme.{moduleMorphism}} (morphism : sourceScheme ⟶ targetScheme) {summandSheaf : targetScheme.Modules}

/-- The sections of a pushforward `f_* M` over `V` are a `Γ(Y, V)`-module through `f^♯`. -/
lemma pushforward_smul_def (moduleSheaf : sourceScheme.Modules) (openSubset : targetScheme.Opens) (scalar : Γ(targetScheme, openSubset))
    (generators : Γ((pushforward morphism).obj moduleSheaf, openSubset)) :
    scalar • generators = (show Γ(moduleSheaf, morphism ⁻¹ᵁ openSubset) from (morphism.app openSubset scalar) • (show Γ(moduleSheaf, morphism ⁻¹ᵁ openSubset) from generators)) :=
  rfl

/-- A morphism `(f_* 𝒪_X)|_V ⟶ N|_V`, for `f⁻¹V` affine, is determined over a basic open `D(r)` of
`V` by its value on the sections over `V`: the sections of `f_* 𝒪_X` over `D(r)` are the
localization of `Γ(X, f⁻¹V)` at `f^♯ r`, and `r` is a unit over `D(r)`. -/
lemma restrictOver_pushforward_unit_hom_app_basicOpen_eq {openSubset : targetScheme.Opens}
    (hV' : IsAffineOpen (morphism ⁻¹ᵁ openSubset))
    {χ₁ χ₂ : (PresheafOfModules.restrictOver targetScheme.sheaf.obj openSubset).obj
        ((pushforward morphism).obj (SheafOfModules.unit sourceScheme.ringCatSheaf)).val ⟶
      (PresheafOfModules.restrictOver targetScheme.sheaf.obj openSubset).obj summandSheaf.val}
    (splitting : χ₁.app (op (Over.mk (𝟙 openSubset))) = χ₂.app (op (Over.mk (𝟙 openSubset)))) (scalar : Γ(targetScheme, openSubset)) :
    χ₁.app (op (Over.mk (homOfLE (targetScheme.basicOpen_le scalar)))) =
      χ₂.app (op (Over.mk (homOfLE (targetScheme.basicOpen_le scalar)))) := by
  let index : morphism ⁻¹ᵁ targetScheme.basicOpen scalar ⟶ morphism ⁻¹ᵁ openSubset :=
    (TopologicalSpace.Opens.map morphism.base).map (homOfLE (targetScheme.basicOpen_le scalar))
  let := (sourceScheme.presheaf.map index.op).hom.toAlgebra
  have hloc := hV'.isLocalization_of_eq_basicOpen (morphism.app openSubset scalar) index (Scheme.preimage_basicOpen morphism scalar)
  let restrictionMap : Over.mk (homOfLE (targetScheme.basicOpen_le scalar)) ⟶ Over.mk (𝟙 openSubset) :=
    Over.homMk (homOfLE (targetScheme.basicOpen_le scalar)) (Subsingleton.elim _ _)
  let restrictedScalar : Γ(targetScheme, targetScheme.basicOpen scalar) := targetScheme.presheaf.map (homOfLE (targetScheme.basicOpen_le scalar)).op scalar
  ext (sectionValue : Γ(sourceScheme, morphism ⁻¹ᵁ targetScheme.basicOpen scalar))
  obtain ⟨⟨b₀, _, rank, rfl⟩, hb⟩ := IsLocalization.surj (S := Γ(sourceScheme, morphism ⁻¹ᵁ targetScheme.basicOpen scalar))
    (Submonoid.powers (morphism.app openSubset scalar)) sectionValue
  have hρ : morphism.app _ restrictedScalar = sourceScheme.presheaf.map index.op (morphism.app openSubset scalar) :=
    ConcreteCategory.congr_hom (morphism.naturality (homOfLE (targetScheme.basicOpen_le scalar)).op) scalar
  have hmid : (morphism.app _ (restrictedScalar ^ rank) * sectionValue : Γ(sourceScheme, morphism ⁻¹ᵁ targetScheme.basicOpen scalar)) = sourceScheme.presheaf.map index.op b₀ := by
    rw [map_pow, hρ, ← map_pow, mul_comm]
    exact hb
  have key (targetHomomorphism : (PresheafOfModules.restrictOver targetScheme.sheaf.obj openSubset).obj
        ((pushforward morphism).obj (SheafOfModules.unit sourceScheme.ringCatSheaf)).val ⟶
      (PresheafOfModules.restrictOver targetScheme.sheaf.obj openSubset).obj summandSheaf.val) :
      restrictedScalar ^ rank • targetHomomorphism.app (op (Over.mk (homOfLE (targetScheme.basicOpen_le scalar)))) sectionValue =
        summandSheaf.val.map restrictionMap.op.unop.left.op (targetHomomorphism.app (op (Over.mk (𝟙 openSubset))) b₀) :=
    ((targetHomomorphism.app (op (Over.mk (homOfLE (targetScheme.basicOpen_le scalar))))).hom.map_smul (restrictedScalar ^ rank) sectionValue).symm.trans
      ((congrArg (targetHomomorphism.app _).hom hmid).trans (PresheafOfModules.naturality_apply targetHomomorphism restrictionMap.op b₀))
  exact ((targetScheme.toRingedSpace.isUnit_res_basicOpen scalar).pow rank).smul_left_cancel.1
    ((key χ₁).trans (splitting ▸ (key χ₂).symm))

/-- A morphism `(f_* 𝒪_X)|_V ⟶ N|_V`, for `V` and `f⁻¹V` affine, is determined by its value on
the sections over `V`. -/
lemma restrictOver_pushforward_unit_hom_ext {openSubset : targetScheme.Opens} (hV : IsAffineOpen openSubset)
    (hV' : IsAffineOpen (morphism ⁻¹ᵁ openSubset))
    {χ₁ χ₂ : (PresheafOfModules.restrictOver targetScheme.sheaf.obj openSubset).obj
        ((pushforward morphism).obj (SheafOfModules.unit sourceScheme.ringCatSheaf)).val ⟶
      (PresheafOfModules.restrictOver targetScheme.sheaf.obj openSubset).obj summandSheaf.val}
    (splitting : χ₁.app (op (Over.mk (𝟙 openSubset))) = χ₂.app (op (Over.mk (𝟙 openSubset)))) : χ₁ = χ₂ := by
  refine PresheafOfModules.hom_ext fun overOpen ↦ ?_
  ext sectionValue
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨summandSheaf.presheaf, summandSheaf.isSheaf⟩
    (fun scalar : {scalar : Γ(targetScheme, openSubset) // targetScheme.basicOpen scalar ≤ overOpen.unop.left} ↦ targetScheme.basicOpen scalar.1) overOpen.unop.left
    (fun scalar ↦ homOfLE scalar.2) (fun sectionValue hx ↦ ?_) _ _ fun scalar ↦ ?_
  · obtain ⟨scalar, hr, hxr⟩ := hV.exists_basicOpen_le ⟨sectionValue, hx⟩ (overOpen.unop.hom.le hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨scalar, hr⟩, hxr⟩
  · let restrictionMap : Over.mk (homOfLE (targetScheme.basicOpen_le scalar.1)) ⟶ overOpen.unop :=
      Over.homMk (homOfLE scalar.2) (Subsingleton.elim _ _)
    refine (PresheafOfModules.naturality_apply χ₁ restrictionMap.op sectionValue).symm.trans ?_
    rw [restrictOver_pushforward_unit_hom_app_basicOpen_eq morphism hV' splitting scalar.1]
    exact PresheafOfModules.naturality_apply χ₂ restrictionMap.op sectionValue

end AlgebraicGeometry.Scheme.Modules
