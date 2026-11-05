import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Clearing denominators and detecting zero sections on basic opens of affine schemes.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe coefficientUniverse
open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

variable {scheme : Scheme.{coefficientUniverse}}

/-- The image of any open of `Spec Γ(X, W)` under `fromSpec` lies in the affine open `W`. -/
lemma IsAffineOpen.fromSpec_image_le {smallerOpen : scheme.Opens} (hW : IsAffineOpen smallerOpen)
    (cover : (Spec Γ(scheme, smallerOpen)).Opens) : hW.fromSpec ''ᵁ cover ≤ smallerOpen :=
  (hW.fromSpec.image_le_opensRange cover).trans hW.opensRange_fromSpec.le

/-- Transporting `r ∈ Γ(X, W)` to `Γ(Spec Γ(X, W), U)` and then back along `fromSpec.appIso U`
is the restriction of `r` to `fromSpec ''ᵁ U`. -/
lemma IsAffineOpen.ΓSpecIso_inv_map_appIso_inv {smallerOpen : scheme.Opens} (hW : IsAffineOpen smallerOpen)
    (cover : (Spec Γ(scheme, smallerOpen)).Opens) :
    (Scheme.ΓSpecIso Γ(scheme, smallerOpen)).inv ≫ (Spec Γ(scheme, smallerOpen)).presheaf.map cover.leTop.op ≫
      (hW.fromSpec.appIso cover).inv =
      scheme.presheaf.map (homOfLE (hW.fromSpec_image_le cover)).op := by
  rw [← cancel_mono (hW.fromSpec.appIso cover).hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Scheme.Hom.appIso_hom, hW.fromSpec.naturality_assoc, hW.fromSpec_app_self]
  simp only [Category.assoc, ← Functor.map_comp]
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{coefficientUniverse}}

/-- Under `restrictAppIso` along `fromSpec`, the `Γ(X, W)`-action on sections of the restricted
module over `U` corresponds to the action of the restriction to `fromSpec ''ᵁ U`. -/
lemma restrictAppIso_fromSpec_smul (moduleSheaf : scheme.Modules) {smallerOpen : scheme.Opens} (hW : IsAffineOpen smallerOpen)
    {cover : (Spec Γ(scheme, smallerOpen)).Opens} (otherScalar : Γ(scheme, smallerOpen)) (element : Γ(moduleSheaf.restrict hW.fromSpec, cover)) :
    dsimp% (moduleSheaf.restrictAppIso hW.fromSpec cover).hom (otherScalar • element) =
      scheme.presheaf.map (homOfLE (hW.fromSpec_image_le cover)).op otherScalar •
        (moduleSheaf.restrictAppIso hW.fromSpec cover).hom element := by
  rw [smul_Spec_def, smul_restrictAppIso_hom_apply, ← hW.ΓSpecIso_inv_map_appIso_inv cover]
  rfl

variable (moduleSheaf : scheme.Modules) [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) moduleSheaf]

/-- The restriction of a quasi-coherent module along `fromSpec` of an affine open is
localizing. -/
lemma isLocalizing_restrict_fromSpec {smallerOpen : scheme.Opens} (hW : IsAffineOpen smallerOpen) :
    IsLocalizing (modulesSpecToSheaf.obj (moduleSheaf.restrict hW.fromSpec)) :=
  (isIso_fromTildeΓ_iff_isLocalizing _).mp inferInstance

/-- Let `M` be quasi-coherent, `W` an affine open and `f ∈ Γ(X, W)`. Every section of `M` over
`D(f)` becomes the restriction of a section over `W` after multiplication by a power of `f`. -/
lemma exists_map_eq_pow_smul_of_isAffineOpen {smallerOpen : scheme.Opens} (hW : IsAffineOpen smallerOpen) (morphism : Γ(scheme, smallerOpen))
    (sectionValue : Γ(moduleSheaf, scheme.basicOpen morphism)) :
    ∃ (size : ℕ) (liftedSection : Γ(moduleSheaf, smallerOpen)), moduleSheaf.presheaf.map (homOfLE (scheme.basicOpen_le morphism)).op liftedSection =
      scheme.presheaf.map (homOfLE (scheme.basicOpen_le morphism)).op morphism ^ size • sectionValue := by
  have hW' : smallerOpen ≤ hW.fromSpec ''ᵁ ⊤ := by
    rw [Hom.image_top_eq_opensRange, hW.opensRange_fromSpec]
  have hD : hW.fromSpec ''ᵁ PrimeSpectrum.basicOpen morphism ≤ scheme.basicOpen morphism :=
    (hW.fromSpec_image_basicOpen morphism).le
  have hD' : scheme.basicOpen morphism ≤ hW.fromSpec ''ᵁ PrimeSpectrum.basicOpen morphism :=
    (hW.fromSpec_image_basicOpen morphism).ge
  have := isLocalizing_restrict_fromSpec moduleSheaf hW morphism
  obtain ⟨⟨liftedSection', _, hm⟩, compatibility⟩ := IsLocalizedModule.surj (.powers morphism)
    ((modulesSpecToSheaf.obj (moduleSheaf.restrict hW.fromSpec)).obj.map
      (PrimeSpectrum.basicOpen morphism).leTop.op).hom
    ((moduleSheaf.restrictAppIso hW.fromSpec _).inv (moduleSheaf.presheaf.map (homOfLE hD).op sectionValue))
  obtain ⟨size, rfl⟩ := hm
  refine ⟨size, moduleSheaf.presheaf.map (homOfLE hW').op ((moduleSheaf.restrictAppIso hW.fromSpec ⊤).hom liftedSection'), ?_⟩
  replace compatibility : morphism ^ size • (moduleSheaf.restrictAppIso hW.fromSpec _).inv (moduleSheaf.presheaf.map (homOfLE hD).op sectionValue) =
      (moduleSheaf.restrict hW.fromSpec).presheaf.map
        (homOfLE (le_top : (PrimeSpectrum.basicOpen morphism : (Spec Γ(scheme, smallerOpen)).Opens) ≤ ⊤)).op liftedSection' := compatibility
  have h1 := congr(moduleSheaf.presheaf.map (homOfLE hD').op
    ((moduleSheaf.restrictAppIso hW.fromSpec (PrimeSpectrum.basicOpen morphism)).hom $compatibility))
  rw [restrictAppIso_fromSpec_smul, map_smul, Iso.inv_hom_id_apply,
    map_restrictAppIso_hom_apply] at h1
  have e1 : (homOfLE hD).op ≫ (homOfLE hD').op = 𝟙 _ := Subsingleton.elim _ _
  have e2 : (homOfLE (hW.fromSpec_image_le (PrimeSpectrum.basicOpen morphism))).op ≫
      (homOfLE hD').op = (homOfLE (scheme.basicOpen_le morphism)).op := Subsingleton.elim _ _
  have e3 : (homOfLE (hW.fromSpec.image_mono (le_top :
      (PrimeSpectrum.basicOpen morphism : (Spec Γ(scheme, smallerOpen)).Opens) ≤ ⊤))).op ≫ (homOfLE hD').op =
      (homOfLE hW').op ≫ (homOfLE (scheme.basicOpen_le morphism)).op := Subsingleton.elim _ _
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← Functor.map_comp_apply, e1, e2, e3,
    CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, map_pow] at h1
  rw [← Functor.map_comp_apply]
  exact h1.symm

/-- Let `M` be quasi-coherent, `W` an affine open and `f ∈ Γ(X, W)`. A section of `M` over `W`
whose restriction to `D(f)` vanishes is killed by a power of `f`. -/
lemma exists_pow_smul_eq_zero_of_isAffineOpen {smallerOpen : scheme.Opens} (hW : IsAffineOpen smallerOpen) (morphism : Γ(scheme, smallerOpen))
    (liftedSection : Γ(moduleSheaf, smallerOpen)) (ht : moduleSheaf.presheaf.map (homOfLE (scheme.basicOpen_le morphism)).op liftedSection = 0) :
    ∃ size : ℕ, morphism ^ size • liftedSection = 0 := by
  have hW' : smallerOpen ≤ hW.fromSpec ''ᵁ ⊤ := by
    rw [Hom.image_top_eq_opensRange, hW.opensRange_fromSpec]
  have hD : hW.fromSpec ''ᵁ PrimeSpectrum.basicOpen morphism ≤ scheme.basicOpen morphism :=
    (hW.fromSpec_image_basicOpen morphism).le
  let liftedSection' := (moduleSheaf.restrictAppIso hW.fromSpec ⊤).inv
    (moduleSheaf.presheaf.map (homOfLE (hW.fromSpec_image_le ⊤)).op liftedSection)
  have h0 : (moduleSheaf.restrict hW.fromSpec).presheaf.map
      (homOfLE (le_top : (PrimeSpectrum.basicOpen morphism : (Spec Γ(scheme, smallerOpen)).Opens) ≤ ⊤)).op liftedSection' = 0 := by
    have := congr((moduleSheaf.restrictAppIso hW.fromSpec _).inv
      (moduleSheaf.presheaf.map (homOfLE hD).op $ht))
    rw [map_zero, map_zero, ← Functor.map_comp_apply] at this
    dsimp only [liftedSection']
    rw [restrictAppIso_inv_map_apply, ← Functor.map_comp_apply]
    convert this using 4
  have := isLocalizing_restrict_fromSpec moduleSheaf hW morphism
  have hz := (IsLocalizedModule.eq_zero_iff (.powers morphism)
    ((modulesSpecToSheaf.obj (moduleSheaf.restrict hW.fromSpec)).obj.map
      (PrimeSpectrum.basicOpen morphism).leTop.op).hom (m := liftedSection')).mp
  obtain ⟨⟨_, hm⟩, hn⟩ := hz h0
  obtain ⟨size, rfl⟩ := hm
  refine ⟨size, ?_⟩
  rw [Submonoid.smul_def] at hn
  have := congr(moduleSheaf.presheaf.map (homOfLE hW').op ((moduleSheaf.restrictAppIso hW.fromSpec ⊤).hom $hn))
  rw [restrictAppIso_fromSpec_smul, map_zero, map_zero, map_smul, Iso.inv_hom_id_apply] at this
  have hid : (homOfLE (hW.fromSpec_image_le ⊤)).op ≫ (homOfLE hW').op =
      𝟙 (Opposite.op smallerOpen) := Subsingleton.elim _ _
  simp only [← Functor.map_comp_apply, hid, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply] at this
  exact this

end AlgebraicGeometry.Scheme.Modules


namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{coefficientUniverse}}

/-- A variant of `exists_map_eq_pow_smul_of_isAffineOpen` for an open `O` equal to `D(g)`. -/
lemma exists_map_eq_pow_smul_of_basicOpen_eq (moduleSheaf : scheme.Modules)
    [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) moduleSheaf] {smallerOpen localizedOpen : scheme.Opens}
    (hW : IsAffineOpen smallerOpen) (sectionFamily : Γ(scheme, smallerOpen)) (hO : scheme.basicOpen sectionFamily = localizedOpen) (hOW : localizedOpen ≤ smallerOpen)
    (sectionValue : Γ(moduleSheaf, localizedOpen)) :
    ∃ (exponent : ℕ) (liftedSection : Γ(moduleSheaf, smallerOpen)), moduleSheaf.presheaf.map (homOfLE hOW).op liftedSection =
      scheme.presheaf.map (homOfLE hOW).op sectionFamily ^ exponent • sectionValue := by
  subst hO
  exact exists_map_eq_pow_smul_of_isAffineOpen moduleSheaf hW sectionFamily sectionValue

/-- A variant of `exists_pow_smul_eq_zero_of_isAffineOpen` for an open `O` equal to `D(g)`. -/
lemma exists_pow_smul_eq_zero_of_basicOpen_eq (moduleSheaf : scheme.Modules)
    [SheafOfModules.IsQuasicoherent (R := scheme.ringCatSheaf) moduleSheaf] {smallerOpen localizedOpen : scheme.Opens}
    (hW : IsAffineOpen smallerOpen) (sectionFamily : Γ(scheme, smallerOpen)) (hO : scheme.basicOpen sectionFamily = localizedOpen) (hOW : localizedOpen ≤ smallerOpen)
    (liftedSection : Γ(moduleSheaf, smallerOpen)) (ht : moduleSheaf.presheaf.map (homOfLE hOW).op liftedSection = 0) :
    ∃ exponent : ℕ, sectionFamily ^ exponent • liftedSection = 0 := by
  subst hO
  exact exists_pow_smul_eq_zero_of_isAffineOpen moduleSheaf hW sectionFamily liftedSection ht

end AlgebraicGeometry.Scheme.Modules


namespace AlgebraicGeometry.Scheme.Modules

open Opposite

variable {X : Scheme.{coefficientUniverse}}

/-- Let `M` be a quasi-coherent `𝒪_X`-module, `U` an affine open and `g ∈ Γ(X, U)`. Then the
restriction map `Γ(M, U) → Γ(M, D(g))` is a localization at the powers of `g`, the
`Γ(X, U)`-module structure on `Γ(M, D(g))` being restriction of scalars along
`Γ(X, U) → Γ(X, D(g))`. -/
lemma isLocalizedModule_basicOpen (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] {U : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) :
    letI : Module Γ(X, U) Γ(M, X.basicOpen g) :=
      Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen g))
    IsLocalizedModule.Away g
      { toFun := M.presheaf.map (homOfLE (X.basicOpen_le g)).op
        map_add' := map_add _
        map_smul' := map_smul M _ : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen g) } := by
  let : Module Γ(X, U) Γ(M, X.basicOpen g) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen g))
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun y ↦ ?_, fun {x₁ x₂} h ↦ ?_⟩
  · obtain ⟨n, rfl⟩ := hx
    have hu : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen g) (g ^ n)) := by
      rw [map_pow]
      exact (X.toRingedSpace.isUnit_res_basicOpen g).pow n
    rw [Module.End.isUnit_iff]
    refine ⟨fun a b hab ↦ ?_, fun m ↦ ⟨hu.unit⁻¹ • m, ?_⟩⟩
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply] at hab
      exact hu.smul_left_cancel.mp hab
    · rw [Module.algebraMap_end_apply]
      exact smul_inv_smul hu.unit m
  · obtain ⟨n, t, ht⟩ := exists_map_eq_pow_smul_of_isAffineOpen M hU g y
    rw [← map_pow] at ht
    exact ⟨⟨t, ⟨g ^ n, n, rfl⟩⟩, ht.symm⟩
  · obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isAffineOpen M hU g (x₁ - x₂)
      ((map_sub _ x₁ x₂).trans (sub_eq_zero.mpr h))
    exact ⟨⟨g ^ n, n, rfl⟩, sub_eq_zero.mp ((smul_sub _ _ _).symm.trans hn)⟩

/-- If the global sections of an `𝒪_{Spec R}`-module are finite over `Γ(Spec R, ⊤)`, they are
finite over `R`. -/
theorem finite_sections_top_of_finite {R : CommRingCat.{coefficientUniverse}} (M : (Spec R).Modules)
    [Module.Finite Γ(Spec R, ⊤) Γ(M, ⊤)] : Module.Finite R Γ(M, ⊤) := by
  have : Module.Finite R Γ(Spec R, ⊤) := by
    refine Module.Finite.of_surjective (Algebra.linearMap R Γ(Spec R, ⊤)) fun x ↦ ?_
    exact ⟨(Scheme.ΓSpecIso R).hom x, by simp⟩
  exact Module.Finite.trans Γ(Spec R, ⊤) Γ(M, ⊤)

end AlgebraicGeometry.Scheme.Modules
