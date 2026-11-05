import Jacobian.Algebra.Category.ModuleCat.ChangeOfRings
import Jacobian.AlgebraicGeometry.Modules.PullbackUnit
import Jacobian.AlgebraicGeometry.Modules.Localization
import Jacobian.AlgebraicGeometry.Modules.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Affine pullback of quasi-coherent modules
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe schemeUniverse

open CategoryTheory Opposite TensorProduct

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {baseRing extensionRing : CommRingCat.{schemeUniverse}} (ringMap : baseRing ⟶ extensionRing)

set_option backward.isDefEq.respectTransparency false in
/-- The global sections over `Spec R` of the pushforward along `Spec.map φ` are the global
sections over `Spec S`, viewed as an `R`-module. -/
noncomputable def pushforwardSpecMapCompΓIso :
    pushforward (Spec.map ringMap) ⋙ moduleSpecΓFunctor (R := baseRing) ≅
      moduleSpecΓFunctor (R := extensionRing) ⋙ ModuleCat.restrictScalars ringMap.hom :=
  NatIso.ofComponents (fun sheaf ↦ LinearEquiv.toModuleIso
    (X₁ := (pushforward (Spec.map ringMap) ⋙ moduleSpecΓFunctor (R := baseRing)).obj sheaf)
    (X₂ := (moduleSpecΓFunctor (R := extensionRing) ⋙ ModuleCat.restrictScalars ringMap.hom).obj sheaf)
    { toFun element := element
      invFun element := element
      map_add' _ _ := rfl
      map_smul' scalar element := by
        let otherElement : Γ(sheaf, ⊤) := element
        change (Spec.map ringMap).appTop ((ΓSpecIso baseRing).inv scalar) • otherElement = (ΓSpecIso extensionRing).inv (ringMap scalar) • otherElement
        rw [← CommRingCat.comp_apply, ← ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
      left_inv _ := rfl
      right_inv _ := rfl }) (fun _ ↦ rfl)

/-- The adjunction `(tilde ⋙ f^*) ⊣ (Γ ⋙ restrictScalars φ)`. -/
noncomputable def tildePullbackAdjunction :
    tilde.functor baseRing ⋙ pullback (Spec.map ringMap) ⊣
      moduleSpecΓFunctor (R := extensionRing) ⋙ ModuleCat.restrictScalars ringMap.hom :=
  (tilde.adjunction.comp (pullbackPushforwardAdjunction (Spec.map ringMap))).ofNatIsoRight
    (pushforwardSpecMapCompΓIso ringMap)

/-- **Pullback of `M^~` along `Spec S ⟶ Spec R` is `(S ⊗[R] M)^~`.** -/
noncomputable def tildePullbackIso :
    tilde.functor baseRing ⋙ pullback (Spec.map ringMap) ≅ ModuleCat.extendScalars ringMap.hom ⋙ tilde.functor extensionRing :=
  (tildePullbackAdjunction ringMap).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj ringMap.hom).comp tilde.adjunction)

lemma tildePullbackIso_hom_app_pullbackUnit (moduleSheaf : ModuleCat.{schemeUniverse} baseRing) (sectionValue : moduleSheaf) :
    ((tildePullbackIso ringMap).hom.app moduleSheaf).app ⊤
      ((pullbackUnit (Spec.map ringMap) (tilde moduleSheaf)).app ⊤ (tilde.toOpen moduleSheaf ⊤ sectionValue)) =
      tilde.toOpen ((ModuleCat.extendScalars ringMap.hom).obj moduleSheaf) ⊤ ((1 : extensionRing) ⊗ₜ sectionValue) := by
  have := congr($((tildePullbackAdjunction ringMap).unit_leftAdjointUniq_hom_app
    ((ModuleCat.extendRestrictScalarsAdj ringMap.hom).comp tilde.adjunction) moduleSheaf) sectionValue)
  exact this

variable {ringMap} in
/-- On sections, a morphism of `𝒪_{Spec R}`-modules is `R`-linear. -/
lemma Hom.app_smul_Spec {sheaf otherSheaf : (Spec baseRing).Modules} (secondMorphism : sheaf ⟶ otherSheaf) (openSubset : (Spec baseRing).Opens) (scalar : baseRing)
    (element : Γ(sheaf, openSubset)) : secondMorphism.app openSubset (scalar • element) = scalar • secondMorphism.app openSubset element := by
  rw [smul_Spec_def, smul_Spec_def, Hom.app_smul]

variable {ringMap} in
/-- On sections, a morphism of `𝒪_{Spec R}`-modules as an `R`-linear map. -/
noncomputable def Hom.appSpecₗ {sheaf otherSheaf : (Spec baseRing).Modules} (secondMorphism : sheaf ⟶ otherSheaf) (openSubset : (Spec baseRing).Opens) :
    Γ(sheaf, openSubset) →ₗ[baseRing] Γ(otherSheaf, openSubset) where
  toFun := secondMorphism.app openSubset
  map_add' := (secondMorphism.app openSubset).hom.map_add
  map_smul' := secondMorphism.app_smul_Spec openSubset

/-- The global sections of `f^* M^~` are `S ⊗[R] M`, for `f : Spec S ⟶ Spec R`. -/
noncomputable def tildePullbackΓEquiv (moduleSheaf : ModuleCat.{schemeUniverse} baseRing) :
    (ModuleCat.extendScalars ringMap.hom).obj moduleSheaf ≃ₗ[extensionRing]
      Γ((pullback (Spec.map ringMap)).obj (tilde moduleSheaf), ⊤) :=
  (LinearEquiv.ofBijective (tilde.toOpen ((ModuleCat.extendScalars ringMap.hom).obj moduleSheaf) ⊤).hom
    (ConcreteCategory.bijective_of_isIso _)) ≪≫ₗ
    (LinearEquiv.ofBijective (Hom.appSpecₗ ((tildePullbackIso ringMap).hom.app moduleSheaf) ⊤)
      (ConcreteCategory.bijective_of_isIso (((tildePullbackIso ringMap).hom.app moduleSheaf).app ⊤))).symm

lemma tildePullbackΓEquiv_one_tmul (moduleSheaf : ModuleCat.{schemeUniverse} baseRing) (sectionValue : moduleSheaf) :
    tildePullbackΓEquiv ringMap moduleSheaf ((1 : extensionRing) ⊗ₜ sectionValue) =
      (pullbackUnit (Spec.map ringMap) (tilde moduleSheaf)).app ⊤ (tilde.toOpen moduleSheaf ⊤ sectionValue) := by
  dsimp only [tildePullbackΓEquiv, LinearEquiv.trans_apply]
  exact (LinearEquiv.symm_apply_eq _).mpr (tildePullbackIso_hom_app_pullbackUnit ringMap moduleSheaf sectionValue).symm

lemma fromTildeΓ_app_toOpen (moduleSheaf : (Spec baseRing).Modules) (sectionValue : Γ(moduleSheaf, ⊤)) :
    moduleSheaf.fromTildeΓ.app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj moduleSheaf) ⊤ sectionValue) = sectionValue := by
  have := congr($(toOpen_fromTildeΓ_app moduleSheaf ⊤) sectionValue)
  refine this.trans ?_
  change moduleSheaf.presheaf.map (homOfLE le_top).op sectionValue = sectionValue
  rw [show (homOfLE le_top : (⊤ : (Spec baseRing).Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- **Base change for quasi-coherent modules along `Spec S ⟶ Spec R`**: the global sections of
the pullback of a quasi-coherent `𝒪_{Spec R}`-module `M` are `S ⊗[R] Γ(M, ⊤)`. -/
noncomputable def pullbackSpecΓEquiv (moduleSheaf : (Spec baseRing).Modules) [moduleSheaf.IsQuasicoherent] :
    (ModuleCat.extendScalars ringMap.hom).obj (moduleSpecΓFunctor.obj moduleSheaf) ≃ₗ[extensionRing]
      Γ((pullback (Spec.map ringMap)).obj moduleSheaf, ⊤) :=
  haveI : IsIso moduleSheaf.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent moduleSheaf
  haveI : IsIso ((pullback (Spec.map ringMap)).map moduleSheaf.fromTildeΓ) := inferInstance
  tildePullbackΓEquiv ringMap _ ≪≫ₗ
    LinearEquiv.ofBijective (Hom.appSpecₗ ((pullback (Spec.map ringMap)).map moduleSheaf.fromTildeΓ) ⊤)
      (ConcreteCategory.bijective_of_isIso (((pullback (Spec.map ringMap)).map moduleSheaf.fromTildeΓ).app ⊤))

lemma pullbackSpecΓEquiv_one_tmul (moduleSheaf : (Spec baseRing).Modules) [moduleSheaf.IsQuasicoherent] (sectionValue : Γ(moduleSheaf, ⊤)) :
    pullbackSpecΓEquiv ringMap moduleSheaf ((1 : extensionRing) ⊗ₜ sectionValue) = (pullbackUnit (Spec.map ringMap) moduleSheaf).app ⊤ sectionValue := by
  change ((pullback (Spec.map ringMap)).map moduleSheaf.fromTildeΓ).app ⊤
    (tildePullbackΓEquiv ringMap (moduleSpecΓFunctor.obj moduleSheaf) ((1 : extensionRing) ⊗ₜ sectionValue)) = _
  refine (congr_arg (((pullback (Spec.map ringMap)).map moduleSheaf.fromTildeΓ).app ⊤)
    (tildePullbackΓEquiv_one_tmul ringMap (moduleSpecΓFunctor.obj moduleSheaf) sectionValue)).trans ?_
  have := congr($(((pullbackPushforwardAdjunction (Spec.map ringMap)).unit.naturality
    moduleSheaf.fromTildeΓ)).app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj moduleSheaf) ⊤ sectionValue))
  refine this.symm.trans ?_
  exact congr_arg ((pullbackUnit (Spec.map ringMap) moduleSheaf).app ⊤) (fromTildeΓ_app_toOpen moduleSheaf sectionValue)

section Algebra

/-- The ring map `R → Γ(Spec R, U)`. -/
noncomputable abbrev toΓSpec (baseRing : Type schemeUniverse) [CommRing baseRing] (openSubset : (Spec (.of baseRing)).Opens) :
    baseRing →+* Γ(Spec (.of baseRing), openSubset) :=
  ((ΓSpecIso (.of baseRing)).inv ≫ (Spec (.of baseRing)).presheaf.map (homOfLE le_top).op).hom

/-- Sections of an `𝒪_{Spec R}`-module are `R`-modules, for `R` a commutative ring, through
`R → Γ(Spec R, U)`. (This agrees with the instance for `R : CommRingCat`, but is defined directly
through the `Γ(Spec R, U)`-module structure.) -/
noncomputable scoped instance moduleOf {baseRing : Type schemeUniverse} [CommRing baseRing] (moduleSheaf : (Spec (.of baseRing)).Modules)
    (openSubset : (Spec (.of baseRing)).Opens) : Module baseRing Γ(moduleSheaf, openSubset) :=
  Module.compHom Γ(moduleSheaf, openSubset) (toΓSpec baseRing openSubset)

lemma smul_of_def {baseRing : Type schemeUniverse} [CommRing baseRing] {moduleSheaf : (Spec (.of baseRing)).Modules}
    {openSubset : (Spec (.of baseRing)).Opens} (scalar : baseRing) (element : Γ(moduleSheaf, openSubset)) : scalar • element = toΓSpec baseRing openSubset scalar • element :=
  rfl

/-- On sections, morphisms of `𝒪_{Spec R}`-modules are `R`-linear. -/
lemma Hom.app_smul_of {baseRing : Type schemeUniverse} [CommRing baseRing] {sheaf otherSheaf : (Spec (.of baseRing)).Modules} (secondMorphism : sheaf ⟶ otherSheaf)
    (openSubset : (Spec (.of baseRing)).Opens) (scalar : baseRing) (element : Γ(sheaf, openSubset)) : secondMorphism.app openSubset (scalar • element) = scalar • secondMorphism.app openSubset element :=
  Hom.app_smul secondMorphism _ element

variable {baseAlgebra extensionAlgebra : Type schemeUniverse} [CommRing baseAlgebra] [CommRing extensionAlgebra] [Algebra baseAlgebra extensionAlgebra]

/-- On global sections over `Spec A`, the unit of the adjunction for `Spec B ⟶ Spec A` is
semilinear along `algebraMap A B`. -/
lemma pullbackΓ_smul (sheaf : (Spec (.of baseAlgebra)).Modules) (baseScalar : baseAlgebra) (element : Γ(sheaf, ⊤)) :
    pullbackΓ (Spec.map (CommRingCat.ofHom (algebraMap baseAlgebra extensionAlgebra))) sheaf (baseScalar • element) =
      algebraMap baseAlgebra extensionAlgebra baseScalar • pullbackΓ (Spec.map (CommRingCat.ofHom (algebraMap baseAlgebra extensionAlgebra))) sheaf element := by
  set morphism := Spec.map (CommRingCat.ofHom (algebraMap baseAlgebra extensionAlgebra))
  rw [smul_of_def, smul_of_def, pullbackΓ_apply, pullbackΓ_apply]
  refine (Hom.app_smul (pullbackUnit morphism sheaf) (toΓSpec baseAlgebra ⊤ baseScalar) element).trans ?_
  have hr : morphism.app ⊤ (toΓSpec baseAlgebra ⊤ baseScalar) = toΓSpec extensionAlgebra ⊤ (algebraMap baseAlgebra extensionAlgebra baseScalar) := by
    simp only [toΓSpec, homOfLE_leOfHom, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply]
    rw [show (homOfLE le_top : (⊤ : (Spec (.of baseAlgebra)).Opens) ⟶ ⊤) = 𝟙 _ from rfl,
      show (homOfLE le_top : (⊤ : (Spec (.of extensionAlgebra)).Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id, op_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact (congr($(ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap baseAlgebra extensionAlgebra))) baseScalar)).symm
  exact congrArg (fun scalar : Γ(Spec (.of extensionAlgebra), morphism ⁻¹ᵁ ⊤) ↦ scalar • pullbackUnitApp morphism sheaf ⊤ element) hr

/-- **Base change for quasi-coherent modules along `Spec B ⟶ Spec A`**, for an `A`-algebra `B`:
the global sections of the pullback of a quasi-coherent `𝒪_{Spec A}`-module `M` are
`B ⊗[A] Γ(M, ⊤)`, with `1 ⊗ m` corresponding to the image of `m` under the unit. -/
theorem exists_linearEquiv_pullback_Spec (moduleSheaf : (Spec (.of baseAlgebra)).Modules) [moduleSheaf.IsQuasicoherent] :
    ∃ comparison : extensionAlgebra ⊗[baseAlgebra] Γ(moduleSheaf, ⊤) ≃ₗ[extensionAlgebra]
      Γ((pullback (Spec.map (CommRingCat.ofHom (algebraMap baseAlgebra extensionAlgebra)))).obj moduleSheaf, ⊤),
      ∀ sectionValue : Γ(moduleSheaf, ⊤), comparison (1 ⊗ₜ sectionValue) =
        pullbackΓ (Spec.map (CommRingCat.ofHom (algebraMap baseAlgebra extensionAlgebra))) moduleSheaf sectionValue := by
  let ringMap : CommRingCat.of baseAlgebra ⟶ CommRingCat.of extensionAlgebra := CommRingCat.ofHom (algebraMap baseAlgebra extensionAlgebra)
  let e₁ := pullbackSpecΓEquiv ringMap moduleSheaf

  let M₀ : ModuleCat (CommRingCat.of baseAlgebra) := @ModuleCat.of (CommRingCat.of baseAlgebra) _ Γ(moduleSheaf, ⊤) _
    (moduleOf moduleSheaf ⊤)
  let inclusion : M₀ ≅ (moduleSpecΓFunctor (R := .of baseAlgebra)).obj moduleSheaf := LinearEquiv.toModuleIso
    (X₁ := M₀) (X₂ := (moduleSpecΓFunctor (R := .of baseAlgebra)).obj moduleSheaf)
    { toFun element := element
      invFun element := element
      map_add' _ _ := rfl
      map_smul' scalar element := (smul_Spec_def (R := .of baseAlgebra) (M := moduleSheaf) (U := ⊤) scalar element).symm
      left_inv _ := rfl
      right_inv _ := rfl }
  let e₀ := ModuleCat.tensorEquivExtendScalars baseAlgebra extensionAlgebra M₀ ≪≫ₗ
    ((ModuleCat.extendScalars ringMap.hom).mapIso inclusion).toLinearEquiv
  let comparison : extensionAlgebra ⊗[baseAlgebra] Γ(moduleSheaf, ⊤) ≃ₗ[extensionAlgebra] Γ((pullback (Spec.map ringMap)).obj moduleSheaf, ⊤) :=
    { toFun tensorElement := e₁ (e₀ tensorElement)
      invFun otherElement := e₀.symm (e₁.symm otherElement)
      map_add' element otherElement := by rw [map_add, map_add]
      map_smul' extensionScalar tensorElement := by
        rw [LinearEquiv.map_smul]
        exact (e₁.map_smul extensionScalar (e₀ tensorElement)).trans
          (smul_Spec_def (R := .of extensionAlgebra) (M := (pullback (Spec.map ringMap)).obj moduleSheaf) (U := ⊤) extensionScalar _)
      left_inv tensorElement := by simp
      right_inv otherElement := by simp }
  exact ⟨comparison, fun sectionValue ↦ (pullbackSpecΓEquiv_one_tmul ringMap moduleSheaf sectionValue).trans (pullbackΓ_apply _ moduleSheaf sectionValue).symm⟩

end Algebra

end Scheme.Modules

end AlgebraicGeometry
