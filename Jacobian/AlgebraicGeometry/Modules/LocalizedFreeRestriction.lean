import Jacobian.AlgebraicGeometry.Modules.Localization

/-!
# Free restrictions from localized sections

A free localization of global sections yields a free restriction of a quasi-coherent module on an affine scheme.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

open Opposite in
/-- **A quasi-coherent module which is free after inverting `r` is free on `D(r)`.** Let `M` be a
quasi-coherent module on `Spec R` and `r ∈ R` such that the localization `Γ(M, ⊤)_r` is a free
`R_r`-module with basis indexed by `ι`. Then the restriction of `M` to the basic open
`D(r) = Spec R_r` is the free module on `ι`: it is `Γ(M, D(r))^~`, and `Γ(M, D(r)) = Γ(M, ⊤)_r`
since `M` is quasi-coherent. -/
theorem nonempty_restrict_iso_free_of_localizedModule {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] (r : R) {ι : Type u}
    (e : LocalizedModule.Away r Γ(M, ⊤) ≃ₗ[Localization.Away r] (ι →₀ Localization.Away r)) :
    Nonempty (M.restrict (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) ≅
      SheafOfModules.free ι) := by
  let S : CommRingCat.{u} := .of (Localization.Away r)
  let φ : R ⟶ S := CommRingCat.ofHom (algebraMap R (Localization.Away r))
  let j := Spec.map φ
  let N := M.restrict j
  have hU : j ''ᵁ ⊤ = PrimeSpectrum.basicOpen r := by
    rw [Hom.image_top_eq_opensRange, Hom.opensRange_localizationAway]
  have hloc := (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance
  have key : ∀ U : (Spec R).Opens, U = PrimeSpectrum.basicOpen r →
      IsLocalizedModule (.powers r)
        ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top : U ⟶ ⊤).op).hom := by
    rintro U rfl
    exact hloc r
  let X : ModuleCat S := (modulesSpecToSheaf.obj N).presheaf.obj (op ⊤)
  let : Module (Localization.Away r) X := X.isModule
  let : Module R X := Module.compHom X φ.hom
  have : IsScalarTower R (Localization.Away r) X := ⟨fun a s x ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let ι₀ : Γ(M, j ''ᵁ ⊤) ≃ₗ[R] X :=
    { toFun x := x
      invFun x := x
      map_add' _ _ := rfl
      map_smul' a x := (restrictAppIso_smul_Spec (M := M) φ a (x : Γ(N, ⊤))).symm
      left_inv _ := rfl
      right_inv _ := rfl }
  let ρ := ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top : j ''ᵁ ⊤ ⟶ ⊤).op).hom
  have : IsLocalizedModule (.powers r) (ι₀.toLinearMap ∘ₗ ρ) :=
    IsLocalizedModule.of_linearEquiv (.powers r) _ ι₀ (hf := key _ hU)
  let e₁ := IsLocalizedModule.iso (.powers r) (ι₀.toLinearMap ∘ₗ ρ)
  let e₂ := e₁.extendScalarsOfIsLocalization (.powers r) (Localization.Away r)
  let e₃ : X ≃ₗ[S] (ι →₀ S) := e₂.symm ≪≫ₗ e
  have : N.IsQuasicoherent := isQuasicoherent_restrictFunctor j M
  have : IsIso (fromTildeΓ (R := S) N) := isIso_fromTildeΓ_of_isQuasicoherent (R := S) N
  let i₁ : N ≅ tilde X := (asIso (fromTildeΓ (R := S) N)).symm
  exact ⟨i₁ ≪≫ (tilde.functor S).mapIso (show X ≅ ModuleCat.of S (ι →₀ S) from e₃.toModuleIso) ≪≫
    tildeFinsupp ι⟩

/-- On global sections of an `𝒪_{Spec R}`-module, `r ∈ R` acts as its image in `Γ(Spec R, ⊤)`. -/
lemma smul_top_eq {R : CommRingCat.{u}} (M : (Spec R).Modules) (r : R) (x : Γ(M, ⊤)) :
    r • x = (Scheme.ΓSpecIso R).inv r • x := by
  rw [smul_Spec_def]
  congr 1

end AlgebraicGeometry.Scheme.Modules
