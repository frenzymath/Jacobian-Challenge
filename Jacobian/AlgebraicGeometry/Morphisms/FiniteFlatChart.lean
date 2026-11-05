import Jacobian.RingTheory.Flat.Generic
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.TensorProduct.DirectLimitFG

/-!
# Finite flat charts over a field

An integral scheme locally of finite type over a field has a nonempty affine
open finite and flat over a localization of polynomial affine space. Noether
normalization supplies finiteness and generic freeness supplies flatness.
-/

set_option backward.isDefEq.respectTransparency false

section
universe schemeUniverse

open CategoryTheory

namespace AlgebraicGeometry

variable {baseField : Type schemeUniverse} [Field baseField] {dimension : ℕ}

theorem smooth_specMap_algebraMap_localizationAway (localizer : MvPolynomial (Fin dimension) baseField) :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away localizer)))) := by
  have : Algebra.Smooth baseField (Localization.Away localizer) :=
    ⟨Algebra.FormallySmooth.comp baseField (MvPolynomial (Fin dimension) baseField) _,
      .trans baseField (MvPolynomial (Fin dimension) baseField) _⟩
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr this)

private lemma surjective_of_nonempty_of_field {extensionField : Type schemeUniverse} [Field extensionField] {target : Scheme.{schemeUniverse}} [Nonempty target]
    (morphism : target ⟶ Spec (.of extensionField)) : Surjective morphism := by
  refine ⟨fun targetPoint ↦ ?_⟩
  obtain ⟨point⟩ := ‹Nonempty target›
  exact ⟨point, Subsingleton.elim (α := PrimeSpectrum extensionField) _ _⟩

theorem geometricallyIrreducible_specMap_algebraMap_localizationAway
    {localizer : MvPolynomial (Fin dimension) baseField} (hr : localizer ≠ 0) :
    GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away localizer)))) := by
  have : IsDomain (Localization.Away localizer) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
  have factorization : Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away localizer))) =
      (Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin dimension) baseField) (Localization.Away localizer))) ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.renameEquiv baseField (Equiv.ulift.{schemeUniverse} (α := Fin dimension))).toRingHom) ≫
        (AffineSpace.SpecIso (ULift (Fin dimension)) (.of baseField)).inv) ≫
        𝔸(ULift (Fin dimension); Spec (.of baseField)) ↘ Spec (.of baseField) := by
    rw [Category.assoc, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext numerator
    simp [IsScalarTower.algebraMap_apply baseField (MvPolynomial (Fin dimension) baseField) (Localization.Away localizer)]
  have hs := surjective_of_nonempty_of_field
    (Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away localizer))))
  have : IsIso (CommRingCat.ofHom
      (MvPolynomial.renameEquiv baseField (Equiv.ulift.{schemeUniverse} (α := Fin dimension))).toRingHom) :=
    (MvPolynomial.renameEquiv baseField
      (Equiv.ulift.{schemeUniverse} (α := Fin dimension))).toRingEquiv.toCommRingCatIso.isIso_hom
  rw [factorization] at hs ⊢
  infer_instance

theorem exists_finite_flat_chart (scheme : Scheme.{schemeUniverse}) [IsIntegral scheme]
    (structureMap : scheme ⟶ Spec (.of baseField)) [LocallyOfFiniteType structureMap] :
    ∃ (affineOpen : Scheme.{schemeUniverse}) (secondIndex : affineOpen ⟶ scheme) (dimension : ℕ) (localizer : MvPolynomial (Fin dimension) baseField)
      (primeElement : affineOpen ⟶ Spec (.of (Localization.Away localizer))),
      IsOpenImmersion secondIndex ∧ IsAffine affineOpen ∧ Nonempty affineOpen ∧ localizer ≠ 0 ∧ IsFinite primeElement ∧ Flat primeElement ∧
        LocallyOfFinitePresentation primeElement ∧
        secondIndex ≫ structureMap = primeElement ≫ Spec.map (CommRingCat.ofHom (algebraMap baseField (Localization.Away localizer))) := by
  obtain ⟨point⟩ := (inferInstance : Nonempty scheme)
  obtain ⟨affineOpen, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := point) (U := ⊤) trivial
  have : Nonempty affineOpen := ⟨⟨point, hxU⟩⟩
  let : Algebra baseField Γ(scheme, affineOpen) :=
    ((structureMap.appLE ⊤ affineOpen le_top).hom.comp (Scheme.ΓSpecIso (.of baseField)).inv.hom).toAlgebra
  have : Algebra.FiniteType baseField Γ(scheme, affineOpen) :=
    RingHom.FiniteType.comp (HasRingHomProperty.appLE @LocallyOfFiniteType structureMap ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨affineOpen, hU⟩ le_top) (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of baseField)).commRingCatIsoToRingEquiv.symm.surjective)
  obtain ⟨dimension, normalizationMap, hg, hfin⟩ := exists_finite_inj_algHom_of_fg baseField Γ(scheme, affineOpen)
  let : Algebra (MvPolynomial (Fin dimension) baseField) Γ(scheme, affineOpen) := normalizationMap.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin dimension) baseField) Γ(scheme, affineOpen) := hfin
  obtain ⟨localizer, hr, hfree, -⟩ :=
    Module.Finite.exists_free_localizedModule_powers_of_isDomain
      (baseAlgebra := MvPolynomial (Fin dimension) baseField) (moduleType := Γ(scheme, affineOpen))
  let localizedAlgebra := Localization (Algebra.algebraMapSubmonoid Γ(scheme, affineOpen) (.powers localizer))
  have hfin' : Module.Finite (Localization.Away localizer) localizedAlgebra :=
    Module.Finite.of_isLocalizedModule (.powers localizer)
      (IsScalarTower.toAlgHom (MvPolynomial (Fin dimension) baseField) Γ(scheme, affineOpen) localizedAlgebra).toLinearMap
  have hflat : Module.Flat (Localization.Away localizer) localizedAlgebra :=
    Module.Flat.of_linearEquiv ((IsLocalizedModule.linearEquiv (.powers localizer)
      (LocalizedModule.mkLinearMap (.powers localizer) Γ(scheme, affineOpen))
      (IsScalarTower.toAlgHom (MvPolynomial (Fin dimension) baseField) Γ(scheme, affineOpen) localizedAlgebra).toLinearMap
      ).extendScalarsOfIsLocalization (.powers localizer) (Localization.Away localizer)).symm
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin dimension) baseField) Γ(scheme, affineOpen) localizer) localizedAlgebra := by
    simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
    infer_instance
  have hgr : algebraMap (MvPolynomial (Fin dimension) baseField) Γ(scheme, affineOpen) localizer ≠ 0 :=
    fun otherPoint ↦ hr (hg (otherPoint.trans (map_zero normalizationMap).symm))
  have : IsDomain localizedAlgebra := IsLocalization.isDomain_localization (by
    rw [Algebra.algebraMapSubmonoid_powers]
    exact powers_le_nonZeroDivisors_of_noZeroDivisors hgr)
  have := IsOpenImmersion.of_isLocalization (algebraMap (MvPolynomial (Fin dimension) baseField) Γ(scheme, affineOpen) localizer)
    (S := localizedAlgebra)
  refine ⟨Spec (.of localizedAlgebra), Spec.map (CommRingCat.ofHom (algebraMap Γ(scheme, affineOpen) localizedAlgebra)) ≫ hU.fromSpec,
    dimension, localizer, Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away localizer) localizedAlgebra)), inferInstance,
    inferInstance, inferInstance, hr, (IsFinite.SpecMap_iff _).mpr
      (RingHom.finite_algebraMap.mpr hfin'), Flat.SpecMap_iff.mpr
      (RingHom.flat_algebraMap_iff.mpr hflat), HasRingHomProperty.Spec_iff.mpr
      (RingHom.finitePresentation_algebraMap.mpr
        (Algebra.FinitePresentation.of_finiteType.mp inferInstance)), ?_⟩
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec structureMap (isAffineOpen_top _) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  ext numerator
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  rw [IsScalarTower.algebraMap_apply baseField (MvPolynomial (Fin dimension) baseField) (Localization.Away localizer),
    ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin dimension) baseField) (Localization.Away localizer) localizedAlgebra,
    IsScalarTower.algebraMap_apply (MvPolynomial (Fin dimension) baseField) Γ(scheme, affineOpen) localizedAlgebra]
  congr 1
  exact (normalizationMap.commutes numerator).symm

end AlgebraicGeometry
