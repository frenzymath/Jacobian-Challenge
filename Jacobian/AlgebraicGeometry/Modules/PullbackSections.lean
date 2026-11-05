import Jacobian.AlgebraicGeometry.Modules.Endomorphism
import Mathlib.Tactic.IrreducibleDef

/-!
# Pullback of sections and its adjunction coherence
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe schemeUniverse
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
variable {scheme source thirdScheme : Scheme.{schemeUniverse}}

/-- The unit of `pullback f ⊣ pushforward f`, on sections. -/
noncomputable abbrev pullbackUnit (morphism : source ⟶ scheme) (moduleSheaf : scheme.Modules) :
    moduleSheaf ⟶ (pushforward morphism).obj ((pullback morphism).obj moduleSheaf) :=
  (pullbackPushforwardAdjunction morphism).unit.app moduleSheaf

/-- The unit of `pullback f ⊣ pushforward f` on sections over `U`, with its codomain written as
sections of `f^* M`. -/
noncomputable abbrev pullbackUnitApp (morphism : source ⟶ scheme) (moduleSheaf : scheme.Modules) (openSubset : scheme.Opens) :
    Γ(moduleSheaf, openSubset) ⟶ Γ((pullback morphism).obj moduleSheaf, morphism ⁻¹ᵁ openSubset) :=
  (pullbackUnit morphism moduleSheaf).app openSubset

set_option backward.isDefEq.respectTransparency.types false in
/-- The units of the pullback-pushforward adjunctions compose, up to `pullbackComp`:

```
  Γ(M, U) ───── η_f ─────▶ Γ(f^* M, f⁻¹ U)
     │                            │
  η_(g ≫ f)                      η_g
     ▼                            ▼
  Γ((g ≫ f)^* M, ⋯) ──(pullbackComp g f).inv──▶ Γ(g^* f^* M, g⁻¹ f⁻¹ U)
``` -/
lemma pullbackUnit_comp_app (secondMorphism : thirdScheme ⟶ source) (morphism : source ⟶ scheme) (moduleSheaf : scheme.Modules) (openSubset : scheme.Opens) :
    (pullbackUnit (secondMorphism ≫ morphism) moduleSheaf).app openSubset ≫ ((pullbackComp secondMorphism morphism).inv.app moduleSheaf).app ((secondMorphism ≫ morphism) ⁻¹ᵁ openSubset) =
      (pullbackUnit morphism moduleSheaf).app openSubset ≫ (pullbackUnit secondMorphism ((pullback morphism).obj moduleSheaf)).app (morphism ⁻¹ᵁ openSubset) := by
  have compatibility := unit_conjugateEquiv ((pullbackPushforwardAdjunction morphism).comp
    (pullbackPushforwardAdjunction secondMorphism)) (pullbackPushforwardAdjunction (secondMorphism ≫ morphism))
    (pullbackComp secondMorphism morphism).inv moduleSheaf
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at compatibility
  have := congr_arg (fun ringMap ↦ Hom.app ringMap openSubset) compatibility
  simpa using this.symm

lemma pullbackUnit_comp_app_apply (secondMorphism : thirdScheme ⟶ source) (morphism : source ⟶ scheme) (moduleSheaf : scheme.Modules) (openSubset : scheme.Opens)
    (sectionValue : Γ(moduleSheaf, openSubset)) :
    ((pullbackComp secondMorphism morphism).inv.app moduleSheaf).app ((secondMorphism ≫ morphism) ⁻¹ᵁ openSubset) ((pullbackUnit (secondMorphism ≫ morphism) moduleSheaf).app openSubset sectionValue) =
      (pullbackUnit secondMorphism ((pullback morphism).obj moduleSheaf)).app (morphism ⁻¹ᵁ openSubset) ((pullbackUnit morphism moduleSheaf).app openSubset sectionValue) :=
  congr($(pullbackUnit_comp_app secondMorphism morphism moduleSheaf openSubset) sectionValue)

/-- Naturality of the unit on sections. -/
lemma pullbackUnit_naturality_apply (morphism : source ⟶ scheme) {moduleSheaf targetSheaf : scheme.Modules} (ringMap : moduleSheaf ⟶ targetSheaf) (openSubset : scheme.Opens)
    (sectionValue : Γ(moduleSheaf, openSubset)) :
    ((pullback morphism).map ringMap).app (morphism ⁻¹ᵁ openSubset) ((pullbackUnit morphism moduleSheaf).app openSubset sectionValue) =
      (pullbackUnit morphism targetSheaf).app openSubset (ringMap.app openSubset sectionValue) :=
  congr($(((pullbackPushforwardAdjunction morphism).unit.naturality ringMap).symm).app openSubset sectionValue)

/-- Two morphisms out of `f^* M` agree if they agree on the image of the unit. -/
lemma pullback_hom_ext (morphism : source ⟶ scheme) {moduleSheaf : scheme.Modules} {sheaf : source.Modules}
    {ringMap secondMap : (pullback morphism).obj moduleSheaf ⟶ sheaf}
    (compatibility : ∀ (openSubset : scheme.Opens) (sectionValue : Γ(moduleSheaf, openSubset)),
      ringMap.app (morphism ⁻¹ᵁ openSubset) ((pullbackUnit morphism moduleSheaf).app openSubset sectionValue) = secondMap.app (morphism ⁻¹ᵁ openSubset) ((pullbackUnit morphism moduleSheaf).app openSubset sectionValue)) :
    ringMap = secondMap := by
  apply ((pullbackPushforwardAdjunction morphism).homEquiv _ _).injective
  ext openSubset sectionValue
  simp only [Adjunction.homEquiv_unit, Hom.comp_app, pushforward_map_app]
  exact compatibility openSubset sectionValue

section OpenImmersion

variable (openImmersion : source ⟶ scheme) [IsOpenImmersion openImmersion]

set_option backward.isDefEq.respectTransparency.types false in
/-- Along an open immersion, the unit of the pullback-pushforward adjunction is the unit of the
restriction adjunction followed by the comparison `restrictFunctorIsoPullback`. -/
lemma pullbackUnit_eq_of_isOpenImmersion (moduleSheaf : scheme.Modules) :
    pullbackUnit openImmersion moduleSheaf = (restrictAdjunction openImmersion).unit.app moduleSheaf ≫
      (pushforward openImmersion).map ((restrictFunctorIsoPullback openImmersion).hom.app moduleSheaf) :=
  ((restrictAdjunction openImmersion).unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction openImmersion) moduleSheaf).symm

/-- Along an open immersion, the unit of the pullback-pushforward adjunction is bijective on
sections over opens contained in the range. -/
lemma bijective_pullbackUnit_app_of_isOpenImmersion (moduleSheaf : scheme.Modules) {openSubset : scheme.Opens}
    (hU : openSubset ≤ openImmersion.opensRange) : Function.Bijective ((pullbackUnit openImmersion moduleSheaf).app openSubset) := by
  rw [pullbackUnit_eq_of_isOpenImmersion, Hom.comp_app, restrictAdjunction_unit_app_app]
  have : openImmersion ''ᵁ (openImmersion ⁻¹ᵁ openSubset) = openSubset := le_antisymm (openImmersion.image_preimage_le openSubset) (by
    intro element hx
    obtain ⟨otherElement, rfl⟩ := hU hx
    exact ⟨otherElement, hx, rfl⟩)
  have : IsIso (homOfLE (openImmersion.image_preimage_le openSubset)) :=
    ⟨homOfLE (by rw [this]), Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  exact (ConcreteCategory.bijective_of_isIso
    (((pushforward openImmersion).map ((restrictFunctorIsoPullback openImmersion).hom.app moduleSheaf)).app openSubset)).comp
    (ConcreteCategory.bijective_of_isIso (moduleSheaf.presheaf.map (homOfLE (openImmersion.image_preimage_le openSubset)).op))

end OpenImmersion

/-- Pullback of a section is the adjunction unit on that open. -/
def pullbackSection (morphism : source ⟶ scheme) {M : scheme.Modules} {U : scheme.Opens}
    (sectionValue : Γ(M, U)) : Γ((pullback morphism).obj M, morphism ⁻¹ᵁ U) :=
  (pullbackUnit morphism M).app U sectionValue

/-- Pullback of sections commutes with restriction to a smaller open. -/
lemma pullbackSection_map (f : source ⟶ scheme) {M : scheme.Modules}
    {U V : scheme.Opens} (h : V ≤ U) (x : Γ(M, U)) :
    pullbackSection f (M.presheaf.map (homOfLE h).op x) =
      ((pullback f).obj M).presheaf.map (homOfLE (f.preimage_mono h)).op
        (pullbackSection f x) :=
  Hom.app_presheaf_map (pullbackUnit f M) (homOfLE h) x

lemma pullbackSection_add (morphism : source ⟶ scheme) {moduleSheaf : scheme.Modules}
    {openSubset : scheme.Opens} (s t : Γ(moduleSheaf, openSubset)) :
    pullbackSection morphism (s + t) = pullbackSection morphism s + pullbackSection morphism t :=
  ((pullbackUnit morphism moduleSheaf).app openSubset).hom.map_add s t

lemma pullbackSection_smul (morphism : source ⟶ scheme) {moduleSheaf : scheme.Modules} {openSubset : scheme.Opens}
    (scalar : Γ(scheme, openSubset)) (sectionValue : Γ(moduleSheaf, openSubset)) :
    pullbackSection morphism (scalar • sectionValue) = morphism.app openSubset scalar • pullbackSection morphism sectionValue :=
  Hom.app_smul _ scalar sectionValue

/-- The unit on global sections. Keeping this irreducible avoids repeatedly comparing
preimages of the maximal open when computing with concrete scheme morphisms. -/
irreducible_def pullbackΓ (morphism : source ⟶ scheme) (moduleSheaf : scheme.Modules) :
    Γ(moduleSheaf, ⊤) ⟶ Γ((pullback morphism).obj moduleSheaf, ⊤) :=
  (pullbackUnit morphism moduleSheaf).app ⊤

lemma pullbackΓ_apply (morphism : source ⟶ scheme) (moduleSheaf : scheme.Modules)
    (sectionValue : Γ(moduleSheaf, ⊤)) :
    pullbackΓ morphism moduleSheaf sectionValue =
      pullbackUnitApp morphism moduleSheaf ⊤ sectionValue := by
  rw [pullbackΓ_def]
  rfl

end AlgebraicGeometry.Scheme.Modules
