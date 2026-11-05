import Jacobian.AlgebraicGeometry.Modules.Localization
import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Local
import Jacobian.AlgebraicGeometry.Modules.TensorPower
import Jacobian.AlgebraicGeometry.Modules.TensorSection
import Jacobian.AlgebraicGeometry.Modules.ZeroLocus
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Clearing denominators for an invertible sheaf

On a quasi-compact scheme separated over an affine scheme, a section of a
quasi-coherent sheaf over the nonvanishing locus of an invertible-sheaf section
extends globally after multiplying by a sufficiently high tensor power of that
section. If the section generates there, the extension gives a map from the
inverse tensor power whose image contains the original local section.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{u}}

/-- The `m`-th power `s^{⊗ m} : 𝒪_X ⟶ ℒ^{⊗ m}` of a global section `s : 𝒪_X ⟶ ℒ`:
`s^{⊗ 0} = 𝟙` and `s^{⊗ (m + 1)} = s ⊗ s^{⊗ m}`, precomposed with `𝒪_X ≅ 𝒪_X ⊗ 𝒪_X`. -/
noncomputable def tensorPowSection {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) :
    (exponent : ℕ) → (𝟙_ scheme.Modules ⟶ lineBundle.tensorPow exponent)
  | 0 => 𝟙 _
  | exponent + 1 => (λ_ (𝟙_ scheme.Modules)).inv ≫ (lineSection ⊗ₘ tensorPowSection lineSection exponent)

@[simp]
lemma tensorPowSection_zero {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) :
    tensorPowSection lineSection 0 = 𝟙 _ :=
  rfl

lemma tensorPowSection_succ {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) (exponent : ℕ) :
    tensorPowSection lineSection (exponent + 1) = (λ_ (𝟙_ scheme.Modules)).inv ≫ (lineSection ⊗ₘ tensorPowSection lineSection exponent) :=
  rfl

/-- The power `s^{⊗ m}` evaluated at the section `1` over `U`. -/
noncomputable abbrev tensorPowSectionOne {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) (exponent : ℕ)
    (openSubset : scheme.Opens) : Γ(lineBundle.tensorPow exponent, openSubset) :=
  (tensorPowSection lineSection exponent).app openSubset (unitSectionsEquiv openSubset 1)

/-- `s^{⊗ 0}(1) = 1`. -/
lemma tensorPowSectionOne_zero {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) (openSubset : scheme.Opens) :
    tensorPowSectionOne lineSection 0 openSubset = unitSectionsEquiv openSubset 1 :=
  rfl

/-- `s^{⊗ (m + 1)}(1) = s(1) ⊗ s^{⊗ m}(1)`. -/
lemma tensorPowSectionOne_succ {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) (exponent : ℕ) (openSubset : scheme.Opens) :
    tensorPowSectionOne lineSection (exponent + 1) openSubset =
      tmulSection (lineSection.app openSubset (unitSectionsEquiv openSubset 1)) (tensorPowSectionOne lineSection exponent openSubset) := by
  rw [tensorPowSectionOne, tensorPowSection_succ, Hom.comp_app, ConcreteCategory.comp_apply,
    leftUnitor_inv_app]
  exact tensorHom_app_tmulSection _ _ _ _

/-- `s^{⊗ m}(1)` is compatible with restriction. -/
lemma presheaf_map_tensorPowSectionOne {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) (exponent : ℕ)
    {openSubset smallerOpen : scheme.Opens} (index : smallerOpen ⟶ openSubset) :
    (lineBundle.tensorPow exponent).presheaf.map index.op (tensorPowSectionOne lineSection exponent openSubset) = tensorPowSectionOne lineSection exponent smallerOpen := by
  rw [tensorPowSectionOne, ← Hom.app_presheaf_map, presheaf_map_unitSectionsEquiv, map_one]

/-- If `s(1) = f • e` on `U`, then `s^{⊗ m}(1) = f ^ m • e^{⊗ m}` on `U`, for some section
`e^{⊗ m}` which is a free generator if `e` is. -/
lemma exists_tensorPowSectionOne_eq_pow_smul {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle)
    {openSubset : scheme.Opens} {generator : Γ(lineBundle, openSubset)} (he : IsFreeGenerator generator) {structureMap : Γ(scheme, openSubset)}
    (hf : lineSection.app openSubset (unitSectionsEquiv openSubset 1) = structureMap • generator) (exponent : ℕ) :
    ∃ E : Γ(lineBundle.tensorPow exponent, openSubset), IsFreeGenerator E ∧ tensorPowSectionOne lineSection exponent openSubset = structureMap ^ exponent • E := by
  induction exponent with
  | zero => exact ⟨_, isFreeGenerator_one openSubset, by rw [pow_zero, one_smul]; rfl⟩
  | succ exponent ih =>
    obtain ⟨E, hE, hE'⟩ := ih
    refine ⟨tmulSection generator E, he.tmulSection hE, ?_⟩
    rw [tensorPowSectionOne_succ, hf, hE', smul_tmulSection, tmulSection_smul, smul_smul, pow_succ']

/-- If `s(1)` is a free generator on `U`, so is `s^{⊗ m}(1)`. -/
lemma isFreeGenerator_tensorPowSectionOne {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle)
    {openSubset : scheme.Opens} (hs : IsFreeGenerator (lineSection.app openSubset (unitSectionsEquiv openSubset 1))) (exponent : ℕ) :
    IsFreeGenerator (tensorPowSectionOne lineSection exponent openSubset) := by
  induction exponent with
  | zero => exact isFreeGenerator_one openSubset
  | succ exponent ih =>
    rw [tensorPowSectionOne_succ]
    exact hs.tmulSection ih

/-- Transport of `s^{⊗ m}(1)` along an equality of exponents. -/
lemma eqToHom_app_tensorPowSectionOne {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) {exponent otherExponent : ℕ}
    (compatibility : exponent = otherExponent) (openSubset : scheme.Opens) :
    (eqToHom (congrArg lineBundle.tensorPow compatibility)).app openSubset (tensorPowSectionOne lineSection exponent openSubset) =
      tensorPowSectionOne lineSection otherExponent openSubset := by
  subst compatibility
  rfl

/-- `s^{⊗ (a + b)}(1)` corresponds to `s^{⊗ a}(1) ⊗ s^{⊗ b}(1)` under `ℒ^{⊗ (a + b)} ≅
ℒ^{⊗ a} ⊗ ℒ^{⊗ b}`. -/
lemma tensorPowAddIso_inv_app_tmulSection {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) (firstExponent secondExponent : ℕ)
    (openSubset : scheme.Opens) :
    (lineBundle.tensorPowAddIso firstExponent secondExponent).inv.app openSubset
        (tmulSection (tensorPowSectionOne lineSection firstExponent openSubset) (tensorPowSectionOne lineSection secondExponent openSubset)) =
      tensorPowSectionOne lineSection (firstExponent + secondExponent) openSubset := by
  induction firstExponent with
  | zero =>
    rw [tensorPowAddIso, Iso.trans_inv, Iso.symm_inv, eqToIso.inv, Hom.comp_app,
      ConcreteCategory.comp_apply]
    exact (congrArg _ ((leftUnitor_hom_app_tmulSection _ _).trans (one_smul _ _))).trans
      (eqToHom_app_tensorPowSectionOne lineSection (Nat.zero_add secondExponent).symm openSubset)
  | succ firstExponent ih =>
    rw [tensorPowAddIso, Iso.trans_inv, Iso.trans_inv, Iso.symm_inv, eqToIso.inv, Hom.comp_app,
      Hom.comp_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      tensorPowSectionOne_succ]
    have h2 : (Iso.refl lineBundle ⊗ᵢ lineBundle.tensorPowAddIso firstExponent secondExponent).inv.app openSubset
        (tmulSection (lineSection.app openSubset (unitSectionsEquiv openSubset 1))
          (tmulSection (tensorPowSectionOne lineSection firstExponent openSubset) (tensorPowSectionOne lineSection secondExponent openSubset))) =
        tmulSection (lineSection.app openSubset (unitSectionsEquiv openSubset 1)) (tensorPowSectionOne lineSection (firstExponent + secondExponent) openSubset) := by
      rw [tensorIso_inv, Iso.refl_inv, tensorHom_app_tmulSection, ih, Hom.id_app]
      rfl
    exact (congrArg _ ((congrArg _ (associator_hom_app_tmulSection _ _ _)).trans h2)).trans
      ((congrArg _ (tensorPowSectionOne_succ lineSection (firstExponent + secondExponent) openSubset).symm).trans
        (eqToHom_app_tensorPowSectionOne lineSection (Nat.succ_add firstExponent secondExponent).symm openSubset))

/-- The section `t ⊗ s^m` of `F ⊗ ℒ^{⊗ m}`. -/
lemma rightUnitor_inv_comp_whiskerLeft_app {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) (exponent : ℕ)
    (moduleSheaf : scheme.Modules) (openSubset : scheme.Opens) (localSection : Γ(moduleSheaf, openSubset)) :
    ((ρ_ moduleSheaf).inv ≫ moduleSheaf ◁ tensorPowSection lineSection exponent).app openSubset localSection =
      tmulSection localSection (tensorPowSectionOne lineSection exponent openSubset) := by
  rw [Hom.comp_app, ConcreteCategory.comp_apply, rightUnitor_inv_app,
    whiskerLeft_app_tmulSection]

/-- Multiplication by `s^{⊗ b}`, as a morphism `F ⊗ ℒ^{⊗ a} ⟶ F ⊗ ℒ^{⊗ (a + b)}`. -/
noncomputable def mulTensorPowSection {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) (moduleSheaf : scheme.Modules)
    (firstExponent secondExponent : ℕ) : moduleSheaf ⊗ lineBundle.tensorPow firstExponent ⟶ moduleSheaf ⊗ lineBundle.tensorPow (firstExponent + secondExponent) :=
  (ρ_ _).inv ≫ (moduleSheaf ⊗ lineBundle.tensorPow firstExponent) ◁ tensorPowSection lineSection secondExponent ≫ (α_ _ _ _).hom ≫
    moduleSheaf ◁ (lineBundle.tensorPowAddIso firstExponent secondExponent).inv

/-- Multiplication by `s^{⊗ b}` on sections. -/
lemma mulTensorPowSection_app {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) (moduleSheaf : scheme.Modules)
    (firstExponent secondExponent : ℕ) (openSubset : scheme.Opens) (sectionValue : Γ(moduleSheaf ⊗ lineBundle.tensorPow firstExponent, openSubset)) :
    (mulTensorPowSection lineSection moduleSheaf firstExponent secondExponent).app openSubset sectionValue = (moduleSheaf ◁ (lineBundle.tensorPowAddIso firstExponent secondExponent).inv).app openSubset
      ((α_ moduleSheaf (lineBundle.tensorPow firstExponent) (lineBundle.tensorPow secondExponent)).hom.app openSubset
        (tmulSection sectionValue (tensorPowSectionOne lineSection secondExponent openSubset))) := by
  rw [mulTensorPowSection, Hom.comp_app, Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, rightUnitor_inv_app,
    whiskerLeft_app_tmulSection]

/-- Multiplication by `s^{⊗ b}` sends `x ⊗ s^{⊗ a}` to `x ⊗ s^{⊗ (a + b)}`. -/
lemma mulTensorPowSection_app_tmulSection {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle)
    (moduleSheaf : scheme.Modules) (firstExponent secondExponent : ℕ) (openSubset : scheme.Opens) (point : Γ(moduleSheaf, openSubset)) :
    (mulTensorPowSection lineSection moduleSheaf firstExponent secondExponent).app openSubset (tmulSection point (tensorPowSectionOne lineSection firstExponent openSubset)) =
      tmulSection point (tensorPowSectionOne lineSection (firstExponent + secondExponent) openSubset) := by
  rw [mulTensorPowSection_app, associator_hom_app_tmulSection, whiskerLeft_app_tmulSection,
    tensorPowAddIso_inv_app_tmulSection]

/-- Multiplication by `s^{⊗ b}` kills sections killed by `g` if `s^{⊗ b}(1)` is a multiple
of `g`. -/
lemma mulTensorPowSection_app_eq_zero {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) (moduleSheaf : scheme.Modules)
    (firstExponent secondExponent : ℕ) {openSubset : scheme.Opens} {otherMorphism : Γ(scheme, openSubset)} {E : Γ(lineBundle.tensorPow secondExponent, openSubset)}
    (hE : tensorPowSectionOne lineSection secondExponent openSubset = otherMorphism • E) {sectionValue : Γ(moduleSheaf ⊗ lineBundle.tensorPow firstExponent, openSubset)} (hy : otherMorphism • sectionValue = 0) :
    (mulTensorPowSection lineSection moduleSheaf firstExponent secondExponent).app openSubset sectionValue = 0 := by
  rw [mulTensorPowSection_app, hE, tmulSection_smul, ← smul_tmulSection, hy, zero_tmulSection,
    map_zero, map_zero]

/-- On an affine open `V` on which `ℒ` has a free generator `e`, with `s(1) = f • e`, the
non-vanishing locus `X_s` of `s` meets `V` in `D(f)`. -/
lemma basicOpen_coeff_eq {lineBundle : scheme.Modules} [SheafOfModules.IsInvertible.{u, u, u} lineBundle]
    (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) (smallerOpen : scheme.affineOpens) {generator : Γ(lineBundle, smallerOpen.1)} (he : IsFreeGenerator generator) :
    scheme.basicOpen (he.coeff (lineSection.app smallerOpen.1 (unitSectionsEquiv _ 1))) =
      smallerOpen.1 ⊓ (Hom.zeroLocus lineSection).support.compl := by
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ scheme.Modules) :=
    inferInstanceAs (SheafOfModules.IsInvertible.{u, u, u} (SheafOfModules.unit scheme.ringCatSheaf))
  ext point
  have key (hx : point ∈ smallerOpen.1) : point ∈ (Hom.zeroLocus lineSection).support ↔
      point ∉ scheme.basicOpen (he.coeff (lineSection.app smallerOpen.1 (unitSectionsEquiv _ 1))) := by
    rw [IdealSheafData.mem_support_iff_of_mem hx,
      Hom.ideal_zeroLocus lineSection smallerOpen (isFreeGenerator_one _) he
        (he.coeff_smul _).symm, zeroLocus_span, mem_zeroLocus_iff]
    simp
    rfl
  constructor
  · intro hx
    have hxV : point ∈ smallerOpen.1 := scheme.basicOpen_le _ hx
    exact ⟨hxV, fun hs ↦ (key hxV).1 hs hx⟩
  · rintro ⟨hxV, hxs⟩
    by_contra compatibility
    exact hxs ((key hxV).2 compatibility)

/-- **A section is a free generator where it does not vanish.** If `U` does not meet the zero
scheme of `s : 𝒪_X ⟶ ℒ`, then `s(1)` is a free generator of `ℒ` on `U`. -/
lemma isFreeGenerator_app_one_of_le {lineBundle : scheme.Modules} [SheafOfModules.IsInvertible.{u, u, u} lineBundle]
    (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) {openSubset : scheme.Opens} (hU : openSubset ≤ (Hom.zeroLocus lineSection).support.compl) :
    IsFreeGenerator (lineSection.app openSubset (unitSectionsEquiv openSubset 1)) := by
  let baseScheme : Sieve openSubset := {
    arrows otherSmallerOpen _ := ∃ (smallerOpen : scheme.affineOpens) (generator : Γ(lineBundle, smallerOpen.1)), IsFreeGenerator generator ∧ otherSmallerOpen ≤ smallerOpen.1
    downward_closed := fun ⟨smallerOpen, generator, he, compatibility⟩ otherMorphism ↦ ⟨smallerOpen, generator, he, (leOfHom otherMorphism).trans compatibility⟩ }
  refine isFreeGenerator_of_mem _ (coveringSieve := baseScheme) (fun point hx ↦ ?_) fun otherSmallerOpen index ⟨smallerOpen, generator, he, hV'smallerOpen⟩ ↦ ?_
  · obtain ⟨smallerOpen, hxV, hVU, generator, he⟩ := exists_isFreeGenerator lineBundle hx
    exact ⟨smallerOpen.1, homOfLE hVU, ⟨smallerOpen, generator, he, le_rfl⟩, hxV⟩
  · set comparison := he.coeff (lineSection.app smallerOpen.1 (unitSectionsEquiv _ 1))
    have hV'targetCategory : otherSmallerOpen ≤ scheme.basicOpen comparison := by
      rw [basicOpen_coeff_eq lineSection smallerOpen he]
      exact le_inf hV'smallerOpen ((leOfHom index).trans hU)
    have hc : IsUnit (scheme.presheaf.map (homOfLE hV'smallerOpen).op comparison) := by
      have h2 : scheme.presheaf.map (homOfLE hV'targetCategory).op
          (scheme.presheaf.map (homOfLE (scheme.basicOpen_le comparison)).op comparison) =
          scheme.presheaf.map (homOfLE hV'smallerOpen).op comparison :=
        Scheme.presheaf_map_map_apply _ _ _
      rw [← h2]
      exact (scheme.toRingedSpace.isUnit_res_basicOpen comparison).map (scheme.presheaf.map (homOfLE hV'targetCategory).op).hom
    rw [← Hom.app_presheaf_map, presheaf_map_unitSectionsEquiv, map_one,
      ← map_one (scheme.presheaf.map (homOfLE hV'smallerOpen).op).hom, ← presheaf_map_unitSectionsEquiv,
      Hom.app_presheaf_map, ← he.coeff_smul (lineSection.app smallerOpen.1 (unitSectionsEquiv _ 1)), map_smul]
    obtain ⟨otherMorphism, hg⟩ := hc
    rw [← hg]
    exact (he.map hV'smallerOpen).units_smul otherMorphism

/-- **Clearing denominators for a section of an invertible module.** Let `X` be a quasi-compact
scheme, separated over an affine scheme `S`, let `ℒ` be an invertible `𝒪_X`-module and
`s : 𝒪_X ⟶ ℒ` a global section of `ℒ`, and let `X_s` be the complement of the zero scheme
`Z(s)`. For every quasi-coherent `𝒪_X`-module `ℱ` and every `t ∈ Γ(X_s, ℱ)` there are `m ≥ 0`
and `u ∈ Γ(X, ℱ ⊗ ℒ^{⊗ m})` with `u|_{X_s} = t ⊗ s^m`.

Here `t ⊗ s^m` is the image of `t` under `ℱ ≅ ℱ ⊗ 𝒪_X ⟶ ℱ ⊗ ℒ^{⊗ m}`, the second map being
`ℱ ◁ s^{⊗ m}`.

On a finite affine cover `Vⱼ` of `X` on which `ℒ` has a basis `eⱼ`, with `s = fⱼ eⱼ`, one has
`X_s ∩ Vⱼ = D(fⱼ)`, so `fⱼ^a t` lifts to `tⱼ ∈ Γ(Vⱼ, ℱ)` for one `a`. The sections
`tⱼ ⊗ eⱼ^a` agree on `X_s ∩ Vⱼ ∩ Vₖ`; the overlaps `Vⱼ ∩ Vₖ` being affine, a further power
`s^b` makes them agree on the whole overlaps, and they glue to `u` with `m = a + b`.
 -/
@[stacks 01PW]
theorem exists_tensorPowSection_eq_restrict {baseScheme : Scheme.{u}} (structureMap : scheme ⟶ baseScheme) [IsSeparated structureMap]
    [IsAffine baseScheme] [CompactSpace scheme] (lineBundle : scheme.Modules) [SheafOfModules.IsInvertible.{u, u, u} lineBundle]
    (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle) (moduleSheaf : scheme.Modules)
    [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) moduleSheaf]
    (localSection : Γ(moduleSheaf, (Hom.zeroLocus lineSection).support.compl)) :
    ∃ (exponent : ℕ) (u : Γ(moduleSheaf ⊗ lineBundle.tensorPow exponent, ⊤)),
      (moduleSheaf ⊗ lineBundle.tensorPow exponent).presheaf.map (homOfLE le_top).op u =
        ((ρ_ moduleSheaf).inv ≫ moduleSheaf ◁ tensorPowSection lineSection exponent).app _ localSection := by
  classical
  have : IsSeparated (terminal.from scheme) := by
    rw [← terminal.comp_from structureMap]
    infer_instance
  generalize hXs : (Hom.zeroLocus lineSection).support.compl = Xs at localSection ⊢
  have hcov (point : scheme) : ∃ smallerOpen : scheme.affineOpens, point ∈ smallerOpen.1 ∧ ∃ generator : Γ(lineBundle, smallerOpen.1), IsFreeGenerator generator := by
    obtain ⟨smallerOpen, hx, -, he⟩ := exists_isFreeGenerator lineBundle (x := point) (W := ⊤) trivial
    exact ⟨smallerOpen, hx, he⟩
  choose smallerOpen hxV generator he using hcov
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun point ↦ ((smallerOpen point).1 : Set scheme))
    (fun point ↦ (smallerOpen point).1.isOpen) (fun point _ ↦ Set.mem_iUnion.2 ⟨point, hxV point⟩)
  let indexType := {point // point ∈ T}
  let smallestOpen : indexType → scheme.Opens := fun otherIndex ↦ (smallerOpen otherIndex.1).1
  have hW (otherIndex : indexType) : IsAffineOpen (smallestOpen otherIndex) := (smallerOpen otherIndex.1).2
  have hcover : ⊤ ≤ iSup smallestOpen := by
    intro point _
    obtain ⟨index, hi, hxi⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ point))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨index, hi⟩, hxi⟩
  let fc : ∀ otherIndex : indexType, Γ(scheme, smallestOpen otherIndex) := fun otherIndex ↦ (he otherIndex.1).coeff (lineSection.app (smallestOpen otherIndex) (unitSectionsEquiv _ 1))
  have hfc (otherIndex : indexType) : lineSection.app (smallestOpen otherIndex) (unitSectionsEquiv _ 1) = fc otherIndex • generator otherIndex.1 :=
    ((he otherIndex.1).coeff_smul _).symm
  have hD (otherIndex : indexType) : scheme.basicOpen (fc otherIndex) = smallestOpen otherIndex ⊓ Xs := by
    rw [← hXs]
    exact basicOpen_coeff_eq lineSection (smallerOpen otherIndex.1) (he otherIndex.1)
  have hDle (otherIndex : indexType) : scheme.basicOpen (fc otherIndex) ≤ Xs := (hD otherIndex).le.trans inf_le_right
  have hlift (otherIndex : indexType) := exists_map_eq_pow_smul_of_isAffineOpen moduleSheaf (hW otherIndex) (fc otherIndex)
    (moduleSheaf.presheaf.map (homOfLE (hDle otherIndex)).op localSection)
  choose otherExponent t₀ ht₀ using hlift
  let firstExponent := Finset.univ.sup otherExponent
  have hna (otherIndex : indexType) : otherExponent otherIndex ≤ firstExponent := Finset.le_sup (Finset.mem_univ otherIndex)
  let t₁ : ∀ otherIndex : indexType, Γ(moduleSheaf, smallestOpen otherIndex) := fun otherIndex ↦ fc otherIndex ^ (firstExponent - otherExponent otherIndex) • t₀ otherIndex
  have ht₁ (otherIndex : indexType) : moduleSheaf.presheaf.map (homOfLE (scheme.basicOpen_le (fc otherIndex))).op (t₁ otherIndex) =
      scheme.presheaf.map (homOfLE (scheme.basicOpen_le (fc otherIndex))).op (fc otherIndex) ^ firstExponent •
        moduleSheaf.presheaf.map (homOfLE (hDle otherIndex)).op localSection := by
    rw [map_smul, ht₀, smul_smul, map_pow, ← pow_add, Nat.sub_add_cancel (hna otherIndex)]
  choose E hE hE' using fun (otherIndex : indexType) (exponent : ℕ) ↦
    exists_tensorPowSectionOne_eq_pow_smul lineSection (he otherIndex.1) (hfc otherIndex) exponent
  let u₁ : ∀ otherIndex : indexType, Γ(moduleSheaf ⊗ lineBundle.tensorPow firstExponent, smallestOpen otherIndex) := fun otherIndex ↦ tmulSection (t₁ otherIndex) (E otherIndex firstExponent)
  have hu₁ (otherIndex : indexType) {thirdSheaf : scheme.Opens} (hP : thirdSheaf ≤ scheme.basicOpen (fc otherIndex)) :
      (moduleSheaf ⊗ lineBundle.tensorPow firstExponent).presheaf.map (homOfLE (hP.trans (scheme.basicOpen_le _))).op (u₁ otherIndex) =
        tmulSection (moduleSheaf.presheaf.map (homOfLE (hP.trans (hDle otherIndex))).op localSection)
          (tensorPowSectionOne lineSection firstExponent thirdSheaf) := by
    rw [tmulSection_map, ← presheaf_map_homOfLE_map_homOfLE (scheme.basicOpen_le (fc otherIndex)) hP (t₁ otherIndex), ht₁,
      map_smul, map_pow, presheaf_map_homOfLE_map_homOfLE,
      ← presheaf_map_tensorPowSectionOne lineSection firstExponent (homOfLE (hP.trans (scheme.basicOpen_le _))), hE',
      map_smul, map_pow, tmulSection_smul, smul_tmulSection, Scheme.presheaf_map_map_apply]
    rfl
  have hover (otherIndex power : indexType) : ∃ secondExponent : ℕ,
      scheme.presheaf.map (homOfLE (inf_le_left : smallestOpen otherIndex ⊓ smallestOpen power ≤ smallestOpen otherIndex)).op (fc otherIndex) ^ secondExponent •
        ((moduleSheaf ⊗ lineBundle.tensorPow firstExponent).presheaf.map (homOfLE inf_le_left).op (u₁ otherIndex) -
          (moduleSheaf ⊗ lineBundle.tensorPow firstExponent).presheaf.map (homOfLE inf_le_right).op (u₁ power)) = 0 := by
    set otherMorphism := scheme.presheaf.map (homOfLE (inf_le_left : smallestOpen otherIndex ⊓ smallestOpen power ≤ smallestOpen otherIndex)).op (fc otherIndex)
    set degree := (moduleSheaf ⊗ lineBundle.tensorPow firstExponent).presheaf.map (homOfLE inf_le_left).op (u₁ otherIndex) -
      (moduleSheaf ⊗ lineBundle.tensorPow firstExponent).presheaf.map (homOfLE inf_le_right).op (u₁ power)
    have hg : scheme.basicOpen otherMorphism = (smallestOpen otherIndex ⊓ smallestOpen power) ⊓ scheme.basicOpen (fc otherIndex) := scheme.basicOpen_res _ _
    have hPj : scheme.basicOpen otherMorphism ≤ scheme.basicOpen (fc otherIndex) := hg.le.trans inf_le_right
    have hPk : scheme.basicOpen otherMorphism ≤ scheme.basicOpen (fc power) := by
      rw [hD power]
      refine le_inf ((scheme.basicOpen_le otherMorphism).trans inf_le_right) (hPj.trans (hDle otherIndex))
    have hd0 : (moduleSheaf ⊗ lineBundle.tensorPow firstExponent).presheaf.map (homOfLE (scheme.basicOpen_le otherMorphism)).op degree = 0 := by
      rw [map_sub, presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE, hu₁ otherIndex hPj,
        hu₁ power hPk]
      exact sub_self _
    obtain ⟨otherDegree, hd'⟩ := ((hE otherIndex firstExponent).bijective_tmulSection_right
      (inf_le_left : smallestOpen otherIndex ⊓ smallestOpen power ≤ smallestOpen otherIndex)).2 degree
    dsimp only at hd'
    have hd'0 : moduleSheaf.presheaf.map (homOfLE (scheme.basicOpen_le otherMorphism)).op otherDegree = 0 := by
      apply ((hE otherIndex firstExponent).bijective_tmulSection_right ((scheme.basicOpen_le otherMorphism).trans inf_le_left)).1
      dsimp only
      rw [zero_tmulSection, ← presheaf_map_homOfLE_map_homOfLE inf_le_left (scheme.basicOpen_le otherMorphism),
        ← tmulSection_map, hd', hd0]
    obtain ⟨secondExponent, hb⟩ := exists_pow_smul_eq_zero_of_isAffineOpen moduleSheaf ((hW otherIndex).inf (hW power)) otherMorphism otherDegree hd'0
    refine ⟨secondExponent, ?_⟩
    rw [← hd', ← smul_tmulSection, hb, zero_tmulSection]
  choose secondExponent hb using hover
  let otherSecondExponent := Finset.univ.sup fun point : indexType × indexType ↦ secondExponent point.1 point.2
  have hbb (otherIndex power : indexType) : secondExponent otherIndex power ≤ otherSecondExponent := Finset.le_sup (f := fun point : indexType × indexType ↦ secondExponent point.1 point.2)
    (Finset.mem_univ (otherIndex, power))
  let ν := mulTensorPowSection lineSection moduleSheaf firstExponent otherSecondExponent
  let v : ∀ otherIndex : indexType, Γ(moduleSheaf ⊗ lineBundle.tensorPow (firstExponent + otherSecondExponent), smallestOpen otherIndex) := fun otherIndex ↦ ν.app (smallestOpen otherIndex) (u₁ otherIndex)
  let 𝓕 : TopCat.Sheaf Ab scheme :=
    ⟨(moduleSheaf ⊗ lineBundle.tensorPow (firstExponent + otherSecondExponent)).presheaf, (moduleSheaf ⊗ lineBundle.tensorPow (firstExponent + otherSecondExponent)).isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible 𝓕.1 smallestOpen v := by
    intro otherIndex power
    rw [← sub_eq_zero]
    have key : ν.app (smallestOpen otherIndex ⊓ smallestOpen power)
        ((moduleSheaf ⊗ lineBundle.tensorPow firstExponent).presheaf.map (homOfLE inf_le_left).op (u₁ otherIndex) -
          (moduleSheaf ⊗ lineBundle.tensorPow firstExponent).presheaf.map (homOfLE inf_le_right).op (u₁ power)) = 0 := by
      refine mulTensorPowSection_app_eq_zero lineSection moduleSheaf firstExponent otherSecondExponent
        (otherMorphism := scheme.presheaf.map (homOfLE (inf_le_left : smallestOpen otherIndex ⊓ smallestOpen power ≤ smallestOpen otherIndex)).op (fc otherIndex) ^ otherSecondExponent)
        (E := (lineBundle.tensorPow otherSecondExponent).presheaf.map (homOfLE (inf_le_left : smallestOpen otherIndex ⊓ smallestOpen power ≤ smallestOpen otherIndex)).op
          (E otherIndex otherSecondExponent)) ?_ ?_
      · rw [← presheaf_map_tensorPowSectionOne lineSection otherSecondExponent (homOfLE inf_le_left), hE', map_smul,
          map_pow]
      · rw [← Nat.sub_add_cancel (hbb otherIndex power), pow_add, mul_smul, hb, smul_zero]
    rw [map_sub, Hom.app_presheaf_map, Hom.app_presheaf_map] at key
    exact key
  obtain ⟨u, hu, -⟩ := 𝓕.existsUnique_gluing' smallestOpen ⊤ (fun otherIndex ↦ homOfLE le_top) hcover v hcompat
  refine ⟨firstExponent + otherSecondExponent, u, ?_⟩
  rw [rightUnitor_inv_comp_whiskerLeft_app]
  refine 𝓕.eq_of_locally_eq' (fun otherIndex ↦ smallestOpen otherIndex ⊓ Xs) Xs (fun otherIndex ↦ homOfLE inf_le_right) ?_ _ _
    fun otherIndex ↦ ?_
  · intro point hx
    obtain ⟨otherIndex, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcover (Set.mem_univ point))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨otherIndex, hj, hx⟩
  · have hu' : (moduleSheaf ⊗ lineBundle.tensorPow (firstExponent + otherSecondExponent)).presheaf.map (homOfLE (le_top : smallestOpen otherIndex ≤ ⊤)).op u =
        v otherIndex := hu otherIndex
    refine (presheaf_map_homOfLE_map_homOfLE _ _ _).trans
      ((presheaf_map_homOfLE_map_homOfLE le_top inf_le_left u).symm.trans ?_)
    rw [hu', ← Hom.app_presheaf_map, hu₁ otherIndex (hD otherIndex).ge, mulTensorPowSection_app_tmulSection,
      tmulSection_map, presheaf_map_tensorPowSectionOne]

/-- Let `s` be a section of `ℒ` which generates `ℒ` on `U`, and let `ℒ^{⊗ m} ⊗ D ≅ 𝒪_X`. If a
section `t` of `F` over `U` is such that `t ⊗ s^m` extends to a global section `u` of
`F ⊗ ℒ^{⊗ m}`, then `t` is in the image of a morphism `D ⟶ F` on sections over `U`: namely of
`D ≅ 𝒪_X ⊗ D ⟶ (F ⊗ ℒ^{⊗ m}) ⊗ D ≅ F ⊗ (ℒ^{⊗ m} ⊗ D) ≅ F`, the middle map being `u`. -/
theorem exists_hom_app_eq_of_tensorPowSection {lineBundle : scheme.Modules} (lineSection : 𝟙_ scheme.Modules ⟶ lineBundle)
    {openSubset : scheme.Opens} (hs : IsFreeGenerator (lineSection.app openSubset (unitSectionsEquiv openSubset 1))) (exponent : ℕ)
    {targetCategory moduleSheaf : scheme.Modules} (comparison : lineBundle.tensorPow exponent ⊗ targetCategory ≅ 𝟙_ scheme.Modules) (localSection : Γ(moduleSheaf, openSubset))
    (u : Γ(moduleSheaf ⊗ lineBundle.tensorPow exponent, ⊤))
    (hu : (moduleSheaf ⊗ lineBundle.tensorPow exponent).presheaf.map (homOfLE le_top).op u =
      ((ρ_ moduleSheaf).inv ≫ moduleSheaf ◁ tensorPowSection lineSection exponent).app openSubset localSection) :
    ∃ (φ : targetCategory ⟶ moduleSheaf) (w : Γ(targetCategory, openSubset)), φ.app openSubset w = localSection := by
  obtain ⟨w, hw⟩ := ((bijective_app_of_iso comparison openSubset).comp
    ((isFreeGenerator_tensorPowSectionOne lineSection hs exponent).bijective_tmulSection_left
      (otherSheaf := targetCategory) le_rfl)).2
      (unitSectionsEquiv openSubset 1)
  have identityRestriction : homOfLE (le_rfl : openSubset ≤ openSubset) = 𝟙 openSubset :=
    Subsingleton.elim _ _
  rw [Function.comp_apply, identityRestriction, presheaf_map_id_apply] at hw
  have h₁ : (homOfGlobalSection _ u ▷ targetCategory).app openSubset (tmulSection (unitSectionsEquiv openSubset 1) w) =
      tmulSection ((moduleSheaf ⊗ lineBundle.tensorPow exponent).presheaf.map (homOfLE le_top).op u) w :=
    (whiskerRight_app_tmulSection _ _ _).trans
      (congrArg (tmulSection · w) (homOfGlobalSection_app_one _ u openSubset))
  refine ⟨(λ_ targetCategory).inv ≫ homOfGlobalSection _ u ▷ targetCategory ≫ (α_ moduleSheaf (lineBundle.tensorPow exponent) targetCategory).hom ≫
    moduleSheaf ◁ comparison.hom ≫ (ρ_ moduleSheaf).hom, w, ?_⟩
  rw [Hom.comp_app, Hom.comp_app, Hom.comp_app, Hom.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    leftUnitor_inv_app]
  refine (congrArg (fun otherSectionValue ↦ (ρ_ moduleSheaf).hom.app openSubset ((moduleSheaf ◁ comparison.hom).app openSubset
    ((α_ moduleSheaf (lineBundle.tensorPow exponent) targetCategory).hom.app openSubset otherSectionValue))) h₁).trans ?_
  rw [hu, rightUnitor_inv_comp_whiskerLeft_app, associator_hom_app_tmulSection,
    whiskerLeft_app_tmulSection, hw, rightUnitor_hom_app_tmulSection',
    LinearEquiv.symm_apply_apply, one_smul]

end AlgebraicGeometry.Scheme.Modules
