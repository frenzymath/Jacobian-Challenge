import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Quasicoherent
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Restrict
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Jacobian.AlgebraicGeometry.Modules.FinitePresentation
import Jacobian.AlgebraicGeometry.Modules.Localization
import Jacobian.AlgebraicGeometry.Modules.Vanishing

/-!
# Local finiteness and vanishing descent

This module contains the affine descent lemmas used by relative projective
cohomology. They turn vanishing on affine restrictions into vanishing on open
ranges and affine module sheaves, identify subsingleton affine higher direct
images with zero objects, and descend finite affine sections to finite
presentations.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Vanishing on an open subscheme implies vanishing on its open range. -/
lemma isZero_restrict_opensRange_of_isZero_restrict {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] {M : X.Modules} (h : IsZero (M.restrict f)) :
    IsZero (M.restrict f.opensRange.ι) := by
  rw [isZero_restrict_iff]
  intro V hV
  obtain ⟨V', rfl⟩ : ∃ V' : Y.Opens, f ''ᵁ V' = V :=
    ⟨f ⁻¹ᵁ V, by rw [Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hV]⟩
  exact (isZero_iff_forall_subsingleton _).1 h V'

/-- A quasi-coherent module on an affine scheme with subsingleton global sections is zero. -/
lemma isZero_of_subsingleton_sections_top {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] (h : Subsingleton Γ(M, ⊤)) : IsZero M := by
  have : Subsingleton ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) := h
  have h' : IsZero ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) :=
    ModuleCat.isZero_of_subsingleton _
  exact IsZero.of_iso ((tilde.functor R).map_isZero h') (asIso M.fromTildeΓ).symm

/-- Over an affine base, subsingleton source cohomology forces a higher direct image to vanish. -/
lemma isZero_higherDirectImage_of_subsingleton_H {R : CommRingCat.{u}} {P : Scheme.{u}}
    (f : P ⟶ Spec R) [QuasiCompact f] [IsSeparated f] [HasInjectiveResolutions P.Modules]
    (N : P.Modules) [SheafOfModules.IsQuasicoherent (R := P.ringCatSheaf) N] (q : ℕ)
    (h : Subsingleton (N.H q)) : IsZero ((higherDirectImage f q).obj N) := by
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H f N q
  have := isQuasicoherent_higherDirectImage f N q
  exact isZero_of_subsingleton_sections_top _ he.1.subsingleton

/-- Over an affine base, a higher direct image vanishes if and only if the
corresponding source cohomology group is subsingleton. -/
theorem isZero_higherDirectImage_iff_subsingleton_H
    {baseRing : CommRingCat.{u}} {sourceScheme : Scheme.{u}}
    (morphism : sourceScheme ⟶ Spec baseRing) [QuasiCompact morphism] [IsSeparated morphism]
    [HasInjectiveResolutions sourceScheme.Modules]
    (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsQuasicoherent] (degree : ℕ) :
    IsZero ((higherDirectImage morphism degree).obj moduleSheaf) ↔
      Subsingleton (moduleSheaf.H degree) := by
  refine ⟨?_, isZero_higherDirectImage_of_subsingleton_H morphism moduleSheaf degree⟩
  intro vanishing
  obtain ⟨comparison, bijective⟩ :=
    exists_bijective_semilinearMap_sections_higherDirectImage_H morphism moduleSheaf degree
  letI := (isZero_iff_forall_subsingleton _).mp vanishing ⊤
  exact bijective.2.subsingleton

/-- Vanishing on an affine base chart is detected by cohomology after base change. -/
theorem isZero_restrict_higherDirectImage_iff_subsingleton_H
    {sourceScheme targetScheme : Scheme.{u}} (morphism : sourceScheme ⟶ targetScheme)
    [QuasiCompact morphism] [IsSeparated morphism]
    [HasInjectiveResolutions sourceScheme.Modules]
    (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsQuasicoherent]
    {openSubset : targetScheme.Opens} (affine : IsAffineOpen openSubset) (degree : ℕ) :
    IsZero (((higherDirectImage morphism degree).obj moduleSheaf).restrict affine.fromSpec) ↔
      Subsingleton (((Modules.pullback (pullback.fst morphism affine.fromSpec)).obj
        moduleSheaf).H degree) := by
  letI := isGrothendieckAbelian (Limits.pullback morphism affine.fromSpec)
  let comparison := higherDirectImagePullbackIsoRestrict
    (IsPullback.of_hasPullback morphism affine.fromSpec) moduleSheaf degree
  constructor
  · intro vanishing
    exact (isZero_higherDirectImage_iff_subsingleton_H
      (pullback.snd morphism affine.fromSpec) _ degree).mp
      (IsZero.of_iso vanishing comparison)
  · intro vanishing
    exact IsZero.of_iso
      ((isZero_higherDirectImage_iff_subsingleton_H
        (pullback.snd morphism affine.fromSpec) _ degree).mpr vanishing) comparison.symm

/-- A finite affine section module gives a finite presentation of its sheaf. -/
theorem exists_presentation_isFinite_of_finite_sections
    {ring : CommRingCat.{u}} [IsNoetherianRing ring] (moduleSheaf : (Spec ring).Modules)
    [moduleSheaf.IsQuasicoherent] [Module.Finite ring Γ(moduleSheaf, ⊤)] :
    ∃ presentation : moduleSheaf.Presentation, presentation.IsFinite := by
  letI : Module.FinitePresentation ring Γ(moduleSheaf, ⊤) :=
    Module.finitePresentation_of_finite ring Γ(moduleSheaf, ⊤)
  exact exists_presentation_isFinite_of_finitePresentation_sections moduleSheaf

end AlgebraicGeometry.Scheme.Modules
