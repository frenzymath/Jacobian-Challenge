import Jacobian.AlgebraicGeometry.Norm.BasicOpen
import Jacobian.Algebra.Category.Ring.Pushout
import Jacobian.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Localization.NormTrace

/-!
# Norms under finite extension of the ground field

Affine sections of a finite field base change form a finite free algebra. Their
norms commute with restriction to basic opens and detect fibres contained in
the nonvanishing locus. Affineness descends along the same faithfully flat map.
-/

set_option backward.isDefEq.respectTransparency false

section
universe schemeUniverse

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

def Scheme.Hom.normAt {base source : Scheme.{schemeUniverse}} (projection : source ⟶ base) (openSubset : base.Opens) :
    Γ(source, projection ⁻¹ᵁ openSubset) →* Γ(base, openSubset) :=
  letI := (projection.app openSubset).hom.toAlgebra
  Algebra.norm Γ(base, openSubset)

lemma surjective_specMap_algebraMap_of_field {baseField extensionField : Type schemeUniverse} [Field baseField] [Field extensionField] [Algebra baseField extensionField] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) := by
  have : Subsingleton (Spec (.of baseField)) := inferInstanceAs (Subsingleton (PrimeSpectrum baseField))
  have : Nonempty (Spec (.of extensionField)) := inferInstanceAs (Nonempty (PrimeSpectrum extensionField))
  exact ⟨fun point ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩

variable {baseField extensionField : Type schemeUniverse} [Field baseField] [Field extensionField] [Algebra baseField extensionField] [Module.Finite baseField extensionField]
  {base source : Scheme.{schemeUniverse}} {baseStructure : base ⟶ Spec (.of baseField)} {projection : source ⟶ base} {extensionStructure : source ⟶ Spec (.of extensionField)}
  (pullbackSquare : IsPullback projection extensionStructure baseStructure (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))

include pullbackSquare

lemma isFinite_of_isPullback_spec : IsFinite projection := by
  refine MorphismProperty.of_isPullback (P := @IsFinite) pullbackSquare.flip ?_
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

lemma flat_of_isPullback_spec : Flat projection := by
  refine MorphismProperty.of_isPullback (P := @Flat) pullbackSquare.flip ?_
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

omit [Module.Finite baseField extensionField] in
lemma surjective_of_isPullback_spec : Surjective projection :=
  MorphismProperty.of_isPullback (P := @Surjective) pullbackSquare.flip surjective_specMap_algebraMap_of_field

lemma free_finite_app {openSubset : base.Opens} (hU : IsAffineOpen openSubset) :
    letI := (projection.app openSubset).hom.toAlgebra
    Module.Free Γ(base, openSubset) Γ(source, projection ⁻¹ᵁ openSubset) ∧ Module.Finite Γ(base, openSubset) Γ(source, projection ⁻¹ᵁ openSubset) := by
  have hUY : projection ⁻¹ᵁ openSubset = projection ⁻¹ᵁ openSubset ⊓ extensionStructure ⁻¹ᵁ ⊤ := by simp
  have := isIso_pushoutSection_of_isAffineOpen pullbackSquare (US := ⊤) (UT := ⊤) (UX := openSubset)
    (by simp) (by simp) hUY (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hpo := (isIso_pushoutSection_iff ..).mp this
  set eA := Scheme.ΓSpecIso (.of baseField)
  set eB := Scheme.ΓSpecIso (.of extensionField)
  have happ : projection.appLE openSubset (projection ⁻¹ᵁ openSubset) (by simp) = projection.app openSubset := by
    rw [Scheme.Hom.app_eq_appLE]
  rw [happ] at hpo
  have hpo' := hpo.of_iso eA (Iso.refl _) eB (Iso.refl _) (f' := eA.inv ≫ baseStructure.appLE ⊤ openSubset (by simp))
    (g' := CommRingCat.ofHom (algebraMap baseField extensionField)) (inl' := projection.app openSubset)
    (inr' := eB.inv ≫ extensionStructure.appLE ⊤ (projection ⁻¹ᵁ openSubset) (by simp)) (by simp) (by
      rw [show (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))).appLE ⊤ ⊤ (by simp) =
        (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))).appTop by
          rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl,
        Scheme.ΓSpecIso_naturality]) (by simp) (by simp)
  let : Algebra baseField Γ(base, openSubset) := (eA.inv ≫ baseStructure.appLE ⊤ openSubset (by simp)).hom.toAlgebra
  let : Algebra extensionField Γ(source, projection ⁻¹ᵁ openSubset) := (eB.inv ≫ extensionStructure.appLE ⊤ (projection ⁻¹ᵁ openSubset) (by simp)).hom.toAlgebra
  let : Algebra Γ(base, openSubset) Γ(source, projection ⁻¹ᵁ openSubset) := (projection.app openSubset).hom.toAlgebra
  let : Algebra baseField Γ(source, projection ⁻¹ᵁ openSubset) :=
    ((eA.inv ≫ baseStructure.appLE ⊤ openSubset (by simp)) ≫ projection.app openSubset).hom.toAlgebra
  have : IsScalarTower baseField Γ(base, openSubset) Γ(source, projection ⁻¹ᵁ openSubset) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower baseField extensionField Γ(source, projection ⁻¹ᵁ openSubset) := IsScalarTower.of_algebraMap_eq' (by
    change ((eA.inv ≫ baseStructure.appLE ⊤ openSubset _) ≫ projection.app openSubset).hom = ((CommRingCat.ofHom (algebraMap baseField extensionField)) ≫
      (eB.inv ≫ extensionStructure.appLE ⊤ (projection ⁻¹ᵁ openSubset) _)).hom
    rw [hpo'.w])
  have hpush : Algebra.IsPushout baseField extensionField Γ(base, openSubset) Γ(source, projection ⁻¹ᵁ openSubset) :=
    (CommRingCat.isPushout_iff_isPushout).mp hpo'.flip
  have baseChangeEquivalence := (hpush.symm).equiv
  exact ⟨.of_equiv baseChangeEquivalence.toLinearEquiv, .equiv baseChangeEquivalence.toLinearEquiv⟩

lemma mem_basicOpen_normAt {openSubset : base.Opens} (hU : IsAffineOpen openSubset) (element : Γ(source, projection ⁻¹ᵁ openSubset)) {point : base}
    (hx : point ∈ openSubset) : point ∈ base.basicOpen (projection.normAt openSubset element) ↔ ∀ fiberPoint, projection fiberPoint = point → fiberPoint ∈ source.basicOpen element := by
  have := isFinite_of_isPullback_spec pullbackSquare
  exact mem_basicOpen_norm_of_free projection hU (free_finite_app pullbackSquare hU).1 element hx

lemma isAffineOpen_of_isAffineOpen_preimage {affineOpen : base.Opens} (hW : IsAffineOpen (projection ⁻¹ᵁ affineOpen)) :
    IsAffineOpen affineOpen := by
  have hsq := (isPullback_morphismRestrict projection affineOpen).paste_vert pullbackSquare
  have : IsAffine (projection ⁻¹ᵁ affineOpen).toScheme := hW
  have := IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasicompact
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : IsAffineHom (affineOpen.ι ≫ baseStructure) := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq.flip
    ⟨⟨surjective_specMap_algebraMap_of_field, hflat⟩, inferInstance⟩ inferInstance
  have : IsAffine affineOpen := isAffine_of_isAffineHom (affineOpen.ι ≫ baseStructure)
  exact this

lemma normAt_map_of_eq_basicOpen {openSubset smallerOpen : base.Opens} (hU : IsAffineOpen openSubset) (localizer : Γ(base, openSubset))
    (hV : smallerOpen = base.basicOpen localizer) (element : Γ(source, projection ⁻¹ᵁ openSubset)) :
    projection.normAt smallerOpen (source.presheaf.map (homOfLE (projection.preimage_mono
      (hV.le.trans (base.basicOpen_le localizer)))).op element) =
      base.presheaf.map (homOfLE (hV.le.trans (base.basicOpen_le localizer))).op (projection.normAt openSubset element) := by
  subst hV
  obtain ⟨hfree, hfin⟩ := free_finite_app pullbackSquare hU
  have := isFinite_of_isPullback_spec pullbackSquare
  have hU' : IsAffineOpen (projection ⁻¹ᵁ openSubset) := hU.preimage projection
  let : Algebra Γ(base, openSubset) Γ(source, projection ⁻¹ᵁ openSubset) := (projection.app openSubset).hom.toAlgebra
  let : Algebra Γ(source, projection ⁻¹ᵁ openSubset) Γ(source, projection ⁻¹ᵁ base.basicOpen localizer) :=
    (source.presheaf.map (homOfLE (projection.preimage_mono (base.basicOpen_le localizer))).op).hom.toAlgebra
  let : Algebra Γ(base, base.basicOpen localizer) Γ(source, projection ⁻¹ᵁ base.basicOpen localizer) :=
    (projection.app (base.basicOpen localizer)).hom.toAlgebra
  let : Algebra Γ(base, openSubset) Γ(source, projection ⁻¹ᵁ base.basicOpen localizer) :=
    (projection.app openSubset ≫ source.presheaf.map (homOfLE (projection.preimage_mono (base.basicOpen_le localizer))).op).hom.toAlgebra
  have : IsScalarTower Γ(base, openSubset) Γ(source, projection ⁻¹ᵁ openSubset) Γ(source, projection ⁻¹ᵁ base.basicOpen localizer) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(base, openSubset) Γ(base, base.basicOpen localizer) Γ(source, projection ⁻¹ᵁ base.basicOpen localizer) :=
    IsScalarTower.of_algebraMap_eq' (by
      change (projection.app openSubset ≫ source.presheaf.map _).hom = (base.presheaf.map _ ≫ projection.app _).hom
      rw [projection.naturality]
      rfl)
  have : IsLocalization.Away localizer Γ(base, base.basicOpen localizer) := hU.isLocalization_basicOpen localizer
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(source, projection ⁻¹ᵁ openSubset) (Submonoid.powers localizer))
      Γ(source, projection ⁻¹ᵁ base.basicOpen localizer) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    have baseChangeEquivalence : projection ⁻¹ᵁ base.basicOpen localizer = source.basicOpen (projection.app openSubset localizer) := Scheme.preimage_basicOpen projection localizer
    have := hU'.isLocalization_basicOpen (projection.app openSubset localizer)
    let ψ := (source.presheaf.mapIso (eqToIso baseChangeEquivalence).op).commRingCatIsoToRingEquiv
    refine IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (projection.app openSubset localizer))
      { ψ with commutes' := fun point ↦ ?_ }
    change (source.presheaf.map _ ≫ source.presheaf.map _) point = source.presheaf.map _ point
    rw [← Functor.map_comp]
    rfl
  exact Algebra.norm_localization (Rₘ := Γ(base, base.basicOpen localizer))
    (Sₘ := Γ(source, projection ⁻¹ᵁ base.basicOpen localizer)) Γ(base, openSubset) (Submonoid.powers localizer) element

end AlgebraicGeometry
