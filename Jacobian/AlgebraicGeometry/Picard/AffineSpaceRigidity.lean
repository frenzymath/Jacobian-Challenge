import Jacobian.AlgebraicGeometry.GlobalSections.FieldTensorProduct
import Jacobian.AlgebraicGeometry.Modules.InvertibleSections
import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Gluing
import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Pullback
import Jacobian.AlgebraicGeometry.Modules.PullbackSections
import Jacobian.RingTheory.TensorProduct.PolynomialLocalization
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Rigidity of line bundles along an open affine line

For an integral locally factorial scheme over an algebraically closed field, the pullbacks
of a line bundle along two rational points of an open affine line are isomorphic.
Local generators are compared using the units of a polynomial localization and then glued.
-/

set_option backward.isDefEq.respectTransparency false

section
universe schemeUniverse

open CategoryTheory Limits Polynomial
open scoped TensorProduct

namespace AlgebraicGeometry

variable {baseField : Type schemeUniverse} [Field baseField]

/-- A section `σ = (𝟙, g) : X ⟶ X ×_S T` of the first projection maps an open `W` into its
preimage `π⁻¹ W`. -/
private lemma le_preimage_lift_preimage_fst {scheme testOpen baseScheme : Scheme.{schemeUniverse}} {sX : scheme ⟶ baseScheme} {sT : testOpen ⟶ baseScheme} (secondMorphism : scheme ⟶ testOpen)
    (hg : 𝟙 scheme ≫ sX = secondMorphism ≫ sT) (openSubset : scheme.Opens) :
    openSubset ≤ pullback.lift (𝟙 scheme) secondMorphism hg ⁻¹ᵁ pullback.fst sX sT ⁻¹ᵁ openSubset := by
  rw [← Scheme.Hom.comp_preimage, pullback.lift_fst, Scheme.Hom.id_preimage]

/-- Elementwise form of `Scheme.Hom.appLE_comp_appLE`. -/
private lemma Scheme.Hom.appLE_appLE_apply {scheme familyScheme targetScheme : Scheme.{schemeUniverse}} (morphism : scheme ⟶ familyScheme) (secondMorphism : familyScheme ⟶ targetScheme) {sourceOpen : targetScheme.Opens}
    {targetOpen : familyScheme.Opens} {openSubset : scheme.Opens} (e₁ : targetOpen ≤ secondMorphism ⁻¹ᵁ sourceOpen) (e₂ : openSubset ≤ morphism ⁻¹ᵁ targetOpen) (comparison : openSubset ≤ (morphism ≫ secondMorphism) ⁻¹ᵁ sourceOpen)
    (coefficient : Γ(targetScheme, sourceOpen)) : morphism.appLE targetOpen openSubset e₂ (secondMorphism.appLE sourceOpen targetOpen e₁ coefficient) = (morphism ≫ secondMorphism).appLE sourceOpen openSubset comparison coefficient := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/-- `appLE` of equal morphisms agree. -/
private lemma Scheme.Hom.appLE_apply_of_eq {scheme familyScheme : Scheme.{schemeUniverse}} {morphism secondMorphism : scheme ⟶ familyScheme} (compatibility : morphism = secondMorphism) {sourceOpen : familyScheme.Opens}
    {targetOpen : scheme.Opens} (comparison : targetOpen ≤ morphism ⁻¹ᵁ sourceOpen) (e' : targetOpen ≤ secondMorphism ⁻¹ᵁ sourceOpen) (coefficient : Γ(familyScheme, sourceOpen)) :
    morphism.appLE sourceOpen targetOpen comparison coefficient = secondMorphism.appLE sourceOpen targetOpen e' coefficient := by
  subst compatibility
  rfl

/-- Pulling back a function from `X` along `X ⟶ X ×_S T ⟶ X` along a section of the first
projection gives back the function. -/
private lemma appLE_lift_app_fst {scheme testOpen baseScheme : Scheme.{schemeUniverse}} {sX : scheme ⟶ baseScheme} {sT : testOpen ⟶ baseScheme} (secondMorphism : scheme ⟶ testOpen)
    (hg : 𝟙 scheme ≫ sX = secondMorphism ≫ sT) (openSubset : scheme.Opens) (coefficient : Γ(scheme, openSubset)) :
    (pullback.lift (𝟙 scheme) secondMorphism hg).appLE _ openSubset (le_preimage_lift_preimage_fst secondMorphism hg openSubset)
      ((pullback.fst sX sT).app openSubset coefficient) = coefficient := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_appLE_apply _ _ _ _ (by simp)]
  refine (Scheme.Hom.appLE_apply_of_eq (pullback.lift_fst (𝟙 scheme) secondMorphism hg) _ le_rfl coefficient).trans ?_
  simp [Scheme.Hom.appLE]
  rfl

/-- Pulling back a function from `T` along `X ⟶ X ×_S T ⟶ T`. -/
private lemma appLE_lift_appLE_snd {scheme testOpen baseScheme : Scheme.{schemeUniverse}} {sX : scheme ⟶ baseScheme} {sT : testOpen ⟶ baseScheme} (secondMorphism : scheme ⟶ testOpen)
    (hg : 𝟙 scheme ≫ sX = secondMorphism ≫ sT) (openSubset : scheme.Opens) (scalar : Γ(testOpen, ⊤)) :
    (pullback.lift (𝟙 scheme) secondMorphism hg).appLE _ openSubset (le_preimage_lift_preimage_fst secondMorphism hg openSubset)
      ((pullback.snd sX sT).appLE ⊤ _ le_top scalar) = secondMorphism.appLE ⊤ openSubset le_top scalar := by
  rw [Scheme.Hom.appLE_appLE_apply _ _ _ _ (by simp)]
  exact Scheme.Hom.appLE_apply_of_eq (pullback.lift_snd (𝟙 scheme) secondMorphism hg) _ le_top scalar

/-- `appLE` of a composite over the top open, elementwise. -/
private lemma Scheme.Hom.comp_appLE_top_apply {scheme familyScheme targetScheme : Scheme.{schemeUniverse}} (morphism : scheme ⟶ familyScheme) (secondMorphism : familyScheme ⟶ targetScheme)
    (openSubset : scheme.Opens) (scalar : Γ(targetScheme, ⊤)) :
    (morphism ≫ secondMorphism).appLE ⊤ openSubset le_top scalar = morphism.appLE ⊤ openSubset le_top (secondMorphism.appTop scalar) := by
  rw [Scheme.Hom.comp_appLE]
  rfl

/-- **Local triviality over the base.** Let `X` be an integral `k`-scheme whose local rings are
unique factorization domains and `f ≠ 0`. Every invertible module `ℒ` on `X ×_k Spec k[t]_f` is
trivial over `π⁻¹ V` for an affine open neighbourhood `V` of any given point of `X`, where `π` is
the first projection. -/
theorem exists_isFreeGenerator_preimage_fst {scheme : Scheme.{schemeUniverse}} [IsIntegral scheme]
    (hX : ∀ point : scheme, UniqueFactorizationMonoid (scheme.presheaf.stalk point)) (sX : scheme ⟶ Spec (.of baseField))
    {morphism : baseField[X]} (hf : morphism ≠ 0)
    (lineBundle : (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away morphism))))).Modules)
    [lineBundle.IsInvertible] (point : scheme) :
    ∃ targetOpen : scheme.Opens, IsAffineOpen targetOpen ∧ point ∈ targetOpen ∧
      ∃ comparison : Γ(lineBundle, pullback.fst sX (Spec.map (CommRingCat.ofHom
        (algebraMap baseField (Localization.Away morphism)))) ⁻¹ᵁ targetOpen), Scheme.Modules.IsFreeGenerator comparison := by
  obtain ⟨openSubset, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := point) (U := ⊤) trivial
  have : IsAffineHom (pullback.fst sX (Spec.map (CommRingCat.ofHom
      (algebraMap baseField (Localization.Away morphism))))) := MorphismProperty.pullback_fst _ _ inferInstance
  let : Algebra baseField Γ(scheme, openSubset) :=
    ((sX.appLE ⊤ openSubset le_top).hom.comp (Scheme.ΓSpecIso (.of baseField)).inv.hom).toAlgebra
  obtain ⟨comparison, he1, -⟩ := exists_ringEquiv_tensor_app_preimage_fst (baseAlgebra := Localization.Away morphism) sX hW
  let : Algebra Γ(scheme, openSubset) Γ(pullback sX (Spec.map (CommRingCat.ofHom
      (algebraMap baseField (Localization.Away morphism)))), pullback.fst sX (Spec.map (CommRingCat.ofHom
      (algebraMap baseField (Localization.Away morphism)))) ⁻¹ᵁ openSubset) :=
    ((pullback.fst sX _).app openSubset).hom.toAlgebra
  let e' := AlgEquiv.ofRingEquiv (R := Γ(scheme, openSubset)) (f := comparison) fun coefficient ↦ he1 coefficient
  let := TopCat.Presheaf.algebra_section_stalk scheme.presheaf ⟨point, hxW⟩
  have := hW.isLocalization_stalk ⟨point, hxW⟩
  have := hX point
  let : Algebra baseField (scheme.presheaf.stalk point) :=
    ((algebraMap Γ(scheme, openSubset) (scheme.presheaf.stalk point)).comp (algebraMap baseField Γ(scheme, openSubset))).toAlgebra
  have : IsScalarTower baseField Γ(scheme, openSubset) (scheme.presheaf.stalk point) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨_, _⟩ := TensorProduct.uniqueFactorizationMonoid_localization_atPrime
    (coefficientRing := scheme.presheaf.stalk point) (hW.primeIdealOf ⟨point, hxW⟩).asIdeal hf e'
  obtain ⟨_, ⟨coefficient, ha, rfl⟩, secondMorphism, hg⟩ :=
    Scheme.Modules.exists_mem_isFreeGenerator_basicOpen lineBundle (hW.preimage (pullback.fst sX _))
      (Algebra.algebraMapSubmonoid _ (hW.primeIdealOf ⟨point, hxW⟩).asIdeal.primeCompl)
  refine ⟨scheme.basicOpen coefficient, hW.basicOpen coefficient, (scheme.mem_basicOpen coefficient point hxW).mpr
    (IsLocalization.map_units (scheme.presheaf.stalk point)
      (M := (hW.primeIdealOf ⟨point, hxW⟩).asIdeal.primeCompl) ⟨coefficient, ha⟩), ?_⟩
  rw [Scheme.preimage_basicOpen]
  exact ⟨secondMorphism, hg⟩

/-- **Units over `π⁻¹ W` are constant along the fibres up to a unit of the base.** Let `k` be
algebraically closed, `X` an integral `k`-scheme, `f ≠ 0`, and `p`, `q` two `k`-points of
`Spec k[t]_f`. For an affine open `W ⊆ X` and a unit `u` of `Γ(X ×_k Spec k[t]_f, π⁻¹ W)`, the
pullbacks of `u` along the sections `X ⟶ X ×_k Spec k[t]_f` at `p` and `q` differ by a constant
`c ∈ k`: as `u = a ⊗ r` with `a ∈ Γ(X, W)ˣ` and `r ∈ k[t]_fˣ`, one has `c = r(p) / r(q)`. -/
theorem exists_appLE_lift_eq_mul [IsAlgClosed baseField] {scheme : Scheme.{schemeUniverse}} [IsIntegral scheme]
    (sX : scheme ⟶ Spec (.of baseField)) {morphism : baseField[X]} (hf : morphism ≠ 0)
    (firstPoint secondPoint : Spec (.of baseField) ⟶ Spec (.of (Localization.Away morphism)))
    (hp : firstPoint ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away morphism))) = 𝟙 _)
    (hq : secondPoint ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away morphism))) = 𝟙 _)
    {openSubset : scheme.Opens} (hW : IsAffineOpen openSubset)
    (transitionUnit : Γ(pullback sX (Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away morphism)))),
      pullback.fst sX (Spec.map (CommRingCat.ofHom
        (algebraMap baseField (Localization.Away morphism)))) ⁻¹ᵁ openSubset)ˣ) :
    ∃ constant : Γ(Spec (.of baseField), ⊤),
      (pullback.lift (𝟙 scheme) (sX ≫ firstPoint) (by simp [hp])).appLE _ openSubset
          (le_preimage_lift_preimage_fst _ _ openSubset) transitionUnit.1 =
        sX.appLE ⊤ openSubset le_top constant * (pullback.lift (𝟙 scheme) (sX ≫ secondPoint) (by simp [hq])).appLE _ openSubset
          (le_preimage_lift_preimage_fst _ _ openSubset) transitionUnit.1 := by
  by_cases hne : Nonempty openSubset
  swap
  · have : Subsingleton Γ(scheme, openSubset) := CommRingCat.subsingleton_of_isTerminal
      (scheme.sheaf.isTerminalOfEqEmpty (eq_bot_iff.mpr fun point hx ↦ hne ⟨⟨point, hx⟩⟩))
    exact ⟨0, Subsingleton.elim _ _⟩
  have := IsIntegral.component_integral (X := scheme) openSubset
  let : Algebra baseField Γ(scheme, openSubset) :=
    ((sX.appLE ⊤ openSubset le_top).hom.comp (Scheme.ΓSpecIso (.of baseField)).inv.hom).toAlgebra
  obtain ⟨comparison, he1, he2⟩ := exists_ringEquiv_tensor_app_preimage_fst (baseAlgebra := Localization.Away morphism) sX hW
  let comparisonMap :
      Γ(pullback sX (Spec.map (CommRingCat.ofHom
        (algebraMap baseField (Localization.Away morphism)))),
        pullback.fst sX (Spec.map (CommRingCat.ofHom
          (algebraMap baseField (Localization.Away morphism)))) ⁻¹ᵁ openSubset) →*
        Γ(scheme, openSubset) ⊗[baseField] Localization.Away morphism :=
    comparison.symm.toMulEquiv.toMonoidHom
  let tensorUnit : (Γ(scheme, openSubset) ⊗[baseField] Localization.Away morphism)ˣ :=
    Units.map comparisonMap transitionUnit
  obtain ⟨coefficient, parameterValue, har⟩ := TensorProduct.exists_units_eq_tmul
    (baseField := baseField) Γ(scheme, openSubset) hf tensorUnit
  have tensorEquation : comparison.symm transitionUnit.1 =
      (coefficient : Γ(scheme, openSubset)) ⊗ₜ[baseField]
        (parameterValue : Localization.Away morphism) := har
  have hu : transitionUnit.1 =
      (pullback.fst sX (Spec.map (CommRingCat.ofHom
        (algebraMap baseField (Localization.Away morphism))))).app openSubset coefficient *
      (pullback.snd sX (Spec.map (CommRingCat.ofHom
        (algebraMap baseField (Localization.Away morphism))))).appLE ⊤ _ le_top
        ((Scheme.ΓSpecIso (.of (Localization.Away morphism))).inv parameterValue) :=
    (comparison.symm_apply_eq.mp tensorEquation).trans (by
    rw [← mul_one (coefficient : Γ(scheme, openSubset)), ← one_mul (parameterValue : Localization.Away morphism),
      ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, he1, he2, mul_one, one_mul])
  let scalar (localizingElement : (Localization.Away morphism)ˣ) := (Scheme.ΓSpecIso (.of (Localization.Away morphism))).inv localizingElement.1
  refine ⟨firstPoint.appTop (scalar parameterValue) * secondPoint.appTop (scalar parameterValue⁻¹), ?_⟩
  have hQ : sX.appLE ⊤ openSubset le_top (secondPoint.appTop (scalar parameterValue⁻¹)) * sX.appLE ⊤ openSubset le_top (secondPoint.appTop (scalar parameterValue)) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one,
      map_one, map_one]
  simp only [hu, map_mul]
  rw [appLE_lift_app_fst, appLE_lift_app_fst, appLE_lift_appLE_snd,
    appLE_lift_appLE_snd, Scheme.Hom.comp_appLE_top_apply, Scheme.Hom.comp_appLE_top_apply]
  rw [mul_mul_mul_comm, hQ, mul_one, mul_comm]

/-- Elementwise form of `Scheme.Hom.appLE_map`. -/
private lemma Scheme.Hom.appLE_map_apply {scheme familyScheme : Scheme.{schemeUniverse}} (morphism : scheme ⟶ familyScheme) {sourceOpen : familyScheme.Opens} {targetOpen V' : scheme.Opens}
    (comparison : targetOpen ≤ morphism ⁻¹ᵁ sourceOpen) (compatibility : V' ≤ targetOpen) (coefficient : Γ(familyScheme, sourceOpen)) :
    scheme.presheaf.map (homOfLE compatibility).op (morphism.appLE sourceOpen targetOpen comparison coefficient) = morphism.appLE sourceOpen V' (compatibility.trans comparison) coefficient := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-- Elementwise form of `Scheme.Hom.map_appLE`. -/
private lemma Scheme.Hom.map_appLE_apply {scheme familyScheme : Scheme.{schemeUniverse}} (morphism : scheme ⟶ familyScheme) {sourceOpen U' : familyScheme.Opens} {targetOpen : scheme.Opens}
    (comparison : targetOpen ≤ morphism ⁻¹ᵁ sourceOpen) (compatibility : sourceOpen ≤ U') (coefficient : Γ(familyScheme, U')) :
    morphism.appLE sourceOpen targetOpen comparison (familyScheme.presheaf.map (homOfLE compatibility).op coefficient) =
      morphism.appLE U' targetOpen (comparison.trans (morphism.preimage_mono compatibility)) coefficient := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- A section `σ` of `π` maps an open `W` into `π⁻¹ W`. -/
private lemma le_preimage_preimage_of_comp_eq_id {scheme familyScheme : Scheme.{schemeUniverse}} {projection : familyScheme ⟶ scheme} {sectionMap : scheme ⟶ familyScheme}
    (hσ : sectionMap ≫ projection = 𝟙 scheme) (openSubset : scheme.Opens) : openSubset ≤ sectionMap ⁻¹ᵁ projection ⁻¹ᵁ openSubset := by
  rw [← Scheme.Hom.comp_preimage, hσ, Scheme.Hom.id_preimage]

namespace Scheme.Modules

/-- A relation `m|_V = ρ • m'|_V` between sections over `U` and `U'` restricts to `W ⊆ V`. -/
private lemma presheaf_map_homOfLE_eq_smul_of_le {scheme : Scheme.{schemeUniverse}} {lineBundle : scheme.Modules} {sourceOpen U' targetOpen openSubset : scheme.Opens}
    (compatibility : targetOpen ≤ sourceOpen) (h' : targetOpen ≤ U') (hW : openSubset ≤ targetOpen) {m : Γ(lineBundle, sourceOpen)} {m' : Γ(lineBundle, U')} {transitionScalar : Γ(scheme, targetOpen)}
    (sectionEquation : lineBundle.presheaf.map (homOfLE compatibility).op m = transitionScalar • lineBundle.presheaf.map (homOfLE h').op m') :
    lineBundle.presheaf.map (homOfLE (hW.trans compatibility)).op m =
      scheme.presheaf.map (homOfLE hW).op transitionScalar • lineBundle.presheaf.map (homOfLE (hW.trans h')).op m' := by
  rw [← presheaf_map_homOfLE_map_homOfLE compatibility hW, sectionEquation, map_smul, presheaf_map_homOfLE_map_homOfLE]

/-- **Cocycle relation.** If `m₁ = a • m₃`, `m₂ = b • m₃` and `m₁ = d • m₂` on suitable opens,
then `a = d * b` on any smaller open `T` on which `m₃` is a free generator. -/
private lemma presheaf_map_eq_mul_of_smul_eq {scheme : Scheme.{schemeUniverse}} {lineBundle : scheme.Modules}
    {U₁ U₂ U₃ firstOverlap secondOverlap thirdOverlap testOpen : scheme.Opens} {m₁ : Γ(lineBundle, U₁)} {m₂ : Γ(lineBundle, U₂)} {m₃ : Γ(lineBundle, U₃)}
    (hA₁ : firstOverlap ≤ U₁) (hA₃ : firstOverlap ≤ U₃) (hB₂ : secondOverlap ≤ U₂) (hB₃ : secondOverlap ≤ U₃) (hD₁ : thirdOverlap ≤ U₁) (hD₂ : thirdOverlap ≤ U₂)
    {coefficient : Γ(scheme, firstOverlap)} {secondCoefficient : Γ(scheme, secondOverlap)} {thirdCoefficient : Γ(scheme, thirdOverlap)}
    (ha : lineBundle.presheaf.map (homOfLE hA₁).op m₁ = coefficient • lineBundle.presheaf.map (homOfLE hA₃).op m₃)
    (hb : lineBundle.presheaf.map (homOfLE hB₂).op m₂ = secondCoefficient • lineBundle.presheaf.map (homOfLE hB₃).op m₃)
    (hd : lineBundle.presheaf.map (homOfLE hD₁).op m₁ = thirdCoefficient • lineBundle.presheaf.map (homOfLE hD₂).op m₂)
    (hTA : testOpen ≤ firstOverlap) (hTB : testOpen ≤ secondOverlap) (hTD : testOpen ≤ thirdOverlap)
    (hm₃ : IsFreeGenerator (lineBundle.presheaf.map (homOfLE (hTA.trans hA₃)).op m₃)) :
    scheme.presheaf.map (homOfLE hTA).op coefficient =
      scheme.presheaf.map (homOfLE hTD).op thirdCoefficient * scheme.presheaf.map (homOfLE hTB).op secondCoefficient := by
  refine hm₃.smul_left_injective ?_
  dsimp only
  rw [← presheaf_map_homOfLE_eq_smul_of_le hA₁ hA₃ hTA ha, mul_smul,
    ← presheaf_map_homOfLE_eq_smul_of_le hB₂ hB₃ hTB hb,
    ← presheaf_map_homOfLE_eq_smul_of_le hD₁ hD₂ hTD hd]

/-- A relation `m|_{U''} = ρ • m'|_{U''}` pulls back along `g` to the relation
`g^* m = g^♯ ρ • g^* m'` on any open `V ⊆ g⁻¹ U''`. -/
private lemma pullbackSection_map_eq_appLE_smul {scheme familyScheme : Scheme.{schemeUniverse}} (secondMorphism : scheme ⟶ familyScheme) {lineBundle : familyScheme.Modules}
    {sourceOpen U' U'' : familyScheme.Opens} (compatibility : U'' ≤ sourceOpen) (h' : U'' ≤ U') {m : Γ(lineBundle, sourceOpen)} {m' : Γ(lineBundle, U')}
    {transitionScalar : Γ(familyScheme, U'')}
    (sectionEquation : lineBundle.presheaf.map (homOfLE compatibility).op m = transitionScalar • lineBundle.presheaf.map (homOfLE h').op m')
    {targetOpen : scheme.Opens} (hV : targetOpen ≤ secondMorphism ⁻¹ᵁ U'') :
    ((pullback secondMorphism).obj lineBundle).presheaf.map (homOfLE (hV.trans (secondMorphism.preimage_mono compatibility))).op
        (pullbackSection secondMorphism m) =
      secondMorphism.appLE U'' targetOpen hV transitionScalar • ((pullback secondMorphism).obj lineBundle).presheaf.map
        (homOfLE (hV.trans (secondMorphism.preimage_mono h'))).op (pullbackSection secondMorphism m') := by
  have H' := congrArg (pullbackSection secondMorphism) sectionEquation
  rw [pullbackSection_map, pullbackSection_smul, pullbackSection_map] at H'
  have H'' := congrArg (((pullback secondMorphism).obj lineBundle).presheaf.map (homOfLE hV).op) H'
  rw [map_smul, presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE] at H''
  exact H''

end Scheme.Modules

open Scheme.Modules in
/-- **Gluing rigidified pullbacks.** Let `X` be an integral scheme over `S` with `Γ(S, ⊤)` a
field, `π : Y ⟶ X` with two sections `σp`, `σq`, and `M` an `𝒪_Y`-module which is trivial over
`π⁻¹ V` for the members `V` of an open cover of `X`. If for every affine open `W ⊆ X` the
pullbacks along `σp` and `σq` of every unit over `π⁻¹ W` differ by a constant of `Γ(S, ⊤)`, then
`σp^* M ≅ σq^* M`. -/
private theorem nonempty_iso_pullback_of_appLE_eq_mul {scheme familyScheme baseScheme : Scheme.{schemeUniverse}} [IsIntegral scheme] (projection : familyScheme ⟶ scheme)
    {σp σq : scheme ⟶ familyScheme} (hp : σp ≫ projection = 𝟙 scheme) (hq : σq ≫ projection = 𝟙 scheme) (sX : scheme ⟶ baseScheme)
    (hS : IsField Γ(baseScheme, ⊤)) (lineBundle : familyScheme.Modules)
    (hM : ∀ point : scheme, ∃ targetOpen : scheme.Opens, point ∈ targetOpen ∧ ∃ comparison : Γ(lineBundle, projection ⁻¹ᵁ targetOpen), IsFreeGenerator comparison)
    (hu : ∀ openSubset : scheme.Opens, IsAffineOpen openSubset → ∀ transitionUnit : Γ(familyScheme, projection ⁻¹ᵁ openSubset)ˣ, ∃ constant : Γ(baseScheme, ⊤),
      σp.appLE _ openSubset (le_preimage_preimage_of_comp_eq_id hp openSubset) transitionUnit.1 =
        sX.appLE ⊤ openSubset le_top constant * σq.appLE _ openSubset (le_preimage_preimage_of_comp_eq_id hq openSubset) transitionUnit.1) :
    Nonempty ((Scheme.Modules.pullback σp).obj lineBundle ≅ (Scheme.Modules.pullback σq).obj lineBundle) := by
  have hle := le_preimage_preimage_of_comp_eq_id hp
  have hle' := le_preimage_preimage_of_comp_eq_id hq
  choose targetOpen hxV generators hE using hM
  obtain ⟨x₀⟩ : Nonempty scheme := inferInstance
  have hW (point : scheme) : ∃ openSubset : scheme.Opens, IsAffineOpen openSubset ∧ (openSubset : Set scheme).Nonempty ∧ openSubset ≤ targetOpen point ⊓ targetOpen x₀ := by
    obtain ⟨overlapPoint, hz, hz₀⟩ := nonempty_preirreducible_inter (targetOpen point).isOpen (targetOpen x₀).isOpen
      ⟨point, hxV point⟩ ⟨x₀, hxV x₀⟩
    obtain ⟨openSubset, hW, hzW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := overlapPoint)
      (U := targetOpen point ⊓ targetOpen x₀) ⟨hz, hz₀⟩
    exact ⟨openSubset, hW, ⟨overlapPoint, hzW⟩, hWV⟩
  choose openSubset hWa hWne hWV using hW
  choose transitionUnit hu' using fun point ↦ ((hE x₀).map (projection.preimage_mono ((hWV point).trans inf_le_right)))
    |>.exists_unit_smul_eq ((hE point).map (projection.preimage_mono ((hWV point).trans inf_le_left)))
  choose constant hc using fun point ↦ hu (openSubset point) (hWa point) (transitionUnit point)
  have hcu (point : scheme) : IsUnit (constant point) := by
    have h1 : IsUnit (sX.appLE ⊤ (openSubset point) le_top (constant point)) :=
      isUnit_of_mul_isUnit_left (hc point ▸ (transitionUnit point).isUnit.map _)
    have := (hWne point).to_subtype
    have h0 : constant point ≠ 0 := by
      rintro h0
      rw [h0, map_zero] at h1
      exact not_isUnit_zero h1
    obtain ⟨thirdCoefficient, hd⟩ := hS.mul_inv_cancel h0
    exact IsUnit.of_mul_eq_one _ hd
  choose transitionFunctions hw using fun firstIndex secondIndex ↦ ((hE secondIndex).map (projection.preimage_mono (inf_le_right : targetOpen firstIndex ⊓ targetOpen secondIndex ≤ _)))
    |>.exists_unit_smul_eq ((hE firstIndex).map (projection.preimage_mono (inf_le_left : targetOpen firstIndex ⊓ targetOpen secondIndex ≤ _)))
  have key (firstIndex secondIndex : scheme) (overlap : scheme.Opens) (hO : overlap ≤ targetOpen firstIndex ⊓ targetOpen secondIndex) :
      sX.appLE ⊤ overlap le_top (constant firstIndex) * σq.appLE _ overlap (hO.trans (hle' _)) (transitionFunctions firstIndex secondIndex).1 =
        σp.appLE _ overlap (hO.trans (hle _)) (transitionFunctions firstIndex secondIndex).1 * sX.appLE ⊤ overlap le_top (constant secondIndex) := by
    by_cases hne : (overlap : Set scheme).Nonempty
    swap
    · have : Subsingleton Γ(scheme, overlap) := CommRingCat.subsingleton_of_isTerminal
        (scheme.sheaf.isTerminalOfEqEmpty (eq_bot_iff.mpr fun point hx ↦ hne ⟨point, hx⟩))
      exact Subsingleton.elim _ _
    obtain ⟨overlapPoint, hz⟩ := nonempty_preirreducible_inter overlap.isOpen (openSubset firstIndex).isOpen hne (hWne firstIndex)
    have hT : ((overlap ⊓ openSubset firstIndex ⊓ openSubset secondIndex : scheme.Opens) : Set scheme).Nonempty :=
      nonempty_preirreducible_inter (overlap ⊓ openSubset firstIndex).isOpen (openSubset secondIndex).isOpen ⟨overlapPoint, hz⟩ (hWne secondIndex)
    have hTO : overlap ⊓ openSubset firstIndex ⊓ openSubset secondIndex ≤ overlap := inf_le_left.trans inf_le_left
    have hTi : overlap ⊓ openSubset firstIndex ⊓ openSubset secondIndex ≤ openSubset firstIndex := inf_le_left.trans inf_le_right
    have hTj : overlap ⊓ openSubset firstIndex ⊓ openSubset secondIndex ≤ openSubset secondIndex := inf_le_right
    refine map_injective_of_isIntegral scheme (homOfLE hTO) (H := ⟨⟨hT.some, hT.some_mem⟩⟩) ?_
    simp only [map_mul, Scheme.Hom.appLE_map_apply]
    have hcoc := presheaf_map_eq_mul_of_smul_eq (ha := hu' firstIndex) (hb := hu' secondIndex) (hd := hw firstIndex secondIndex)
      (hTA := projection.preimage_mono hTi) (hTB := projection.preimage_mono hTj)
      (hTD := projection.preimage_mono (hTO.trans hO)) (hm₃ := (hE x₀).map _)
    have hP := congrArg (σp.appLE _ _ (hle (overlap ⊓ openSubset firstIndex ⊓ openSubset secondIndex))) hcoc
    have hQ := congrArg (σq.appLE _ _ (hle' (overlap ⊓ openSubset firstIndex ⊓ openSubset secondIndex))) hcoc
    have hci := congrArg (scheme.presheaf.map (homOfLE hTi).op) (hc firstIndex)
    have hcj := congrArg (scheme.presheaf.map (homOfLE hTj).op) (hc secondIndex)
    simp only [map_mul, Scheme.Hom.map_appLE_apply, Scheme.Hom.appLE_map_apply] at hP hQ hci hcj
    refine ((transitionUnit secondIndex).isUnit.map (σq.appLE _ _ (hTj.trans (hle' _))).hom).mul_right_cancel ?_
    linear_combination (-sX.appLE ⊤ _ le_top (constant firstIndex)) * hQ - hci + hP +
      σp.appLE _ _ (hTO.trans (hO.trans (hle _))) (transitionFunctions firstIndex secondIndex).1 * hcj
  let comparison (firstIndex : scheme) : Γ((Scheme.Modules.pullback σp).obj lineBundle, targetOpen firstIndex) :=
    ((Scheme.Modules.pullback σp).obj lineBundle).presheaf.map (homOfLE (hle (targetOpen firstIndex))).op
      (pullbackSection σp (generators firstIndex))
  let secondMorphism (firstIndex : scheme) : Γ((Scheme.Modules.pullback σq).obj lineBundle, targetOpen firstIndex) :=
    sX.appLE ⊤ (targetOpen firstIndex) le_top (constant firstIndex) • ((Scheme.Modules.pullback σq).obj lineBundle).presheaf.map
      (homOfLE (hle' (targetOpen firstIndex))).op (pullbackSection σq (generators firstIndex))
  refine nonempty_iso_of_isFreeGenerator (firstGenerators := comparison) (secondGenerators := secondMorphism)
    (eq_top_iff.mpr fun point _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨point, hxV point⟩)
    (fun firstIndex ↦ ((hE firstIndex).pullbackSection σp).map _) (fun firstIndex secondIndex overlap hi hj coefficient secondCoefficient hab ↦ ?_)
    fun firstIndex ↦ (((hE firstIndex).pullbackSection σq).map _).units_smul
      ((hcu firstIndex).map (sX.appLE ⊤ (targetOpen firstIndex) le_top).hom).unit
  have hO := le_inf hi hj
  simp only [comparison, secondMorphism, Scheme.Modules.map_smul, presheaf_map_homOfLE_map_homOfLE,
    Scheme.Hom.appLE_map_apply] at hab ⊢
  rw [pullbackSection_map_eq_appLE_smul σp (projection.preimage_mono inf_le_left)
    (projection.preimage_mono inf_le_right) (hw firstIndex secondIndex) (hO.trans (hle _))] at hab
  rw [pullbackSection_map_eq_appLE_smul σq (projection.preimage_mono inf_le_left)
    (projection.preimage_mono inf_le_right) (hw firstIndex secondIndex) (hO.trans (hle' _))]
  have hab' : coefficient * σp.appLE _ overlap (hO.trans (hle _)) (transitionFunctions firstIndex secondIndex).1 = secondCoefficient := by
    refine Scheme.Modules.IsFreeGenerator.smul_left_injective
      (Scheme.Modules.IsFreeGenerator.map
        (Scheme.Modules.IsFreeGenerator.pullbackSection σp (hE secondIndex))
        (hj.trans (hle _))) ?_
    dsimp only
    rw [mul_smul]
    exact hab
  rw [← hab']
  simp only [smul_smul]
  congr 1
  linear_combination coefficient * key firstIndex secondIndex overlap hO

/-- **Rigidity of invertible modules over an open of the affine line** (Stacks 0BEH, for a basic
open `D(f)` of the affine line). Let `k` be an algebraically closed field, `X` an integral
`k`-scheme whose local rings are unique factorization domains, and `p`, `q` two `k`-points of
`D(f) = Spec k[t]_f`. For every invertible module `ℒ` on `X ×_k D(f)`, the pullbacks of `ℒ` along
the sections `X ⟶ X ×_k D(f)` at `p` and at `q` are isomorphic. -/
@[stacks 0BEH]
theorem nonempty_iso_pullback_lift_of_isAlgClosed [IsAlgClosed baseField] (scheme : Scheme.{schemeUniverse}) [IsIntegral scheme]
    (hX : ∀ point : scheme, UniqueFactorizationMonoid (scheme.presheaf.stalk point)) (sX : scheme ⟶ Spec (.of baseField))
    (morphism : baseField[X]) (firstPoint secondPoint : Spec (.of baseField) ⟶ Spec (.of (Localization.Away morphism)))
    (hp : firstPoint ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away morphism))) = 𝟙 _)
    (hq : secondPoint ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away morphism))) = 𝟙 _)
    (lineBundle : (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away morphism))))).Modules)
    [lineBundle.IsInvertible] :
    Nonempty ((Scheme.Modules.pullback (pullback.lift (𝟙 scheme) (sX ≫ firstPoint) (by simp [hp]))).obj lineBundle ≅
      (Scheme.Modules.pullback (pullback.lift (𝟙 scheme) (sX ≫ secondPoint) (by simp [hq]))).obj lineBundle) := by
  have hf : morphism ≠ 0 := by
    have h0 := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away morphism) morphism
    rintro rfl
    rw [map_zero, isUnit_zero_iff] at h0
    have := subsingleton_of_zero_eq_one h0
    obtain ⟨pt⟩ : Nonempty (Spec (.of baseField)) := inferInstance
    exact (PrimeSpectrum.isEmpty_iff_subsingleton.mpr this).false (firstPoint pt)
  refine nonempty_iso_pullback_of_appLE_eq_mul (pullback.fst _ _) (pullback.lift_fst _ _ _)
    (pullback.lift_fst _ _ _) sX
    ((Scheme.ΓSpecIso (.of baseField)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField baseField))
    lineBundle (fun point ↦ ?_)
    fun openSubset hW transitionUnit ↦ exists_appLE_lift_eq_mul sX hf firstPoint secondPoint hp hq hW transitionUnit
  obtain ⟨targetOpen, -, hx, comparison, he⟩ := exists_isFreeGenerator_preimage_fst hX sX hf lineBundle point
  exact ⟨targetOpen, hx, comparison, he⟩

end AlgebraicGeometry
