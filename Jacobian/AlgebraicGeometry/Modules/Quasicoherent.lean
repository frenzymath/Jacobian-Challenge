import Jacobian.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Jacobian.AlgebraicGeometry.Modules.Invertible
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Quasi-coherent modules on schemes

Presentations transport between the over-site of an open subset and its open
subscheme. Consequently, presentations on an open cover establish quasi-coherence,
and pullback along any scheme morphism preserves quasi-coherent modules.

On an affine scheme, a quasi-coherent module admits a global presentation.
More generally, quasi-coherence can be checked by asking that the canonical map
from the sheaf associated to sections be an isomorphism on every affine open.
The affine equivalence and the criterion
`AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ` are supplied by the
associated-sheaf construction.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme source target : Scheme.{schemeUniverse}}

/-- A presentation on an open subscheme gives a presentation on its over-site. -/
def presentationOverOfRestrict {moduleSheaf : scheme.Modules} (openSubset : scheme.Opens)
    (presentation : (moduleSheaf.restrict openSubset.ι).Presentation) :
    (moduleSheaf.over openSubset).Presentation :=
  letI functor : SheafOfModules.{schemeUniverse} openSubset.toScheme.ringCatSheaf ⥤
      SheafOfModules.{schemeUniverse} (scheme.ringCatSheaf.over openSubset) :=
    (overEquiv openSubset).inverse
  haveI : PreservesColimitsOfSize.{schemeUniverse, schemeUniverse} functor :=
    (overEquiv openSubset).symm.toAdjunction.leftAdjoint_preservesColimits
  letI restrictionIso : functor.obj (moduleSheaf.restrict openSubset.ι) ≅
      moduleSheaf.over openSubset :=
    (overEquiv openSubset).inverse.mapIso ((overFunctorEquiv openSubset).app moduleSheaf).symm ≪≫
      ((overEquiv openSubset).unitIso.app (moduleSheaf.over openSubset)).symm
  (presentation.map functor
    (openSubset.sheafOfModulesEquivOverInverseUnit scheme.ringCatSheaf).symm).ofIsIso
      restrictionIso.hom

/-- Pullback transports global presentations, since it preserves colimits and the unit. -/
def presentationPullback (morphism : source ⟶ target) {moduleSheaf : target.Modules}
    (presentation : moduleSheaf.Presentation) :
    ((pullback morphism).obj moduleSheaf).Presentation :=
  have : PreservesColimitsOfSize.{schemeUniverse, schemeUniverse} (pullback morphism) :=
    inferInstance
  presentation.map (pullback morphism) (pullbackObjUnitIso morphism).symm

/-- A presentation along an open immersion gives a presentation on its open image. -/
def presentationRestrictOpensRange (morphism : source ⟶ target) [IsOpenImmersion morphism]
    {moduleSheaf : target.Modules} (presentation : (moduleSheaf.restrict morphism).Presentation) :
    (moduleSheaf.restrict morphism.opensRange.ι).Presentation :=
  SheafOfModules.Presentation.ofIsIso.{schemeUniverse, schemeUniverse, schemeUniverse}
    (((restrictFunctorComp morphism.isoOpensRange.inv morphism).app moduleSheaf).inv ≫
      (restrictFunctorCongr morphism.isoOpensRange_inv_comp).hom.app moduleSheaf)
    (presentationRestrict morphism.isoOpensRange.inv presentation)

/-- Presentations on an open cover establish quasi-coherence. -/
theorem isQuasicoherent_of_isOpenCover (moduleSheaf : scheme.Modules)
    {indices : Type schemeUniverse} {openSubsets : indices → scheme.Opens}
    (cover : IsOpenCover openSubsets)
    (presentations : ∀ index, (moduleSheaf.restrict (openSubsets index).ι).Presentation) :
    moduleSheaf.IsQuasicoherent :=
  SheafOfModules.QuasicoherentData.isQuasicoherent (M := moduleSheaf)
    (SheafOfModules.QuasicoherentData.mk.{schemeUniverse, schemeUniverse, schemeUniverse,
      schemeUniverse} (I := indices) (X := openSubsets)
      ((Opens.coversTop_iff _ openSubsets).mpr cover)
      (fun index ↦ presentationOverOfRestrict (openSubsets index) (presentations index)))

/-- Presentations along open immersions whose images cover establish quasi-coherence. -/
theorem isQuasicoherent_of_iSup_opensRange_eq_top (moduleSheaf : scheme.Modules)
    {indices : Type schemeUniverse} {sources : indices → Scheme.{schemeUniverse}}
    (morphisms : ∀ index, sources index ⟶ scheme) [∀ index, IsOpenImmersion (morphisms index)]
    (cover : ⨆ index, (morphisms index).opensRange = ⊤)
    (presentations : ∀ index, (moduleSheaf.restrict (morphisms index)).Presentation) :
    moduleSheaf.IsQuasicoherent :=
  isQuasicoherent_of_isOpenCover moduleSheaf (openSubsets := fun index ↦
    (morphisms index).opensRange) cover
    (fun index ↦ presentationRestrictOpensRange (morphisms index) (presentations index))

/-- Pullback along an arbitrary scheme morphism preserves quasi-coherent modules. -/
instance isQuasicoherent_pullback (morphism : source ⟶ target) (moduleSheaf : target.Modules)
    [moduleSheaf.IsQuasicoherent] : ((pullback morphism).obj moduleSheaf).IsQuasicoherent := by
  obtain ⟨indices, openSubsets, presentations, cover, _⟩ :=
    moduleSheaf.exists_isOpenCover_presentation
  refine isQuasicoherent_of_isOpenCover ((pullback morphism).obj moduleSheaf)
    (openSubsets := fun index : indices ↦ morphism ⁻¹ᵁ openSubsets index) ?_ ?_
  · refine IsOpenCover.mk (eq_top_iff.mpr fun point _ ↦ ?_)
    obtain ⟨index, membership⟩ := cover.exists_mem (morphism.base point)
    exact Opens.mem_iSup.mpr ⟨index, membership⟩
  · intro index
    exact SheafOfModules.Presentation.ofIsIso.{schemeUniverse, schemeUniverse, schemeUniverse}
      ((restrictFunctorIsoPullback _).app _ ≪≫
        (pullbackComp (morphism ⁻¹ᵁ openSubsets index).ι morphism).app moduleSheaf ≪≫
        (pullbackCongr (morphismRestrict_ι morphism (openSubsets index)).symm).app moduleSheaf ≪≫
        ((pullbackComp (morphism ∣_ openSubsets index) (openSubsets index).ι).symm).app moduleSheaf ≪≫
        (pullback (morphism ∣_ openSubsets index)).mapIso
          ((restrictFunctorIsoPullback _).app moduleSheaf).symm).inv
      (presentationPullback (morphism ∣_ openSubsets index) (presentations index))

/-- A module on `Spec R` is globally presented when its associated-sections map is invertible. -/
def presentationOfIsIsoFromTildeΓ {ring : CommRingCat.{schemeUniverse}}
    (moduleSheaf : (Spec ring).Modules) [IsIso moduleSheaf.fromTildeΓ] : moduleSheaf.Presentation :=
  haveI : IsIso (C := SheafOfModules.{schemeUniverse} (Spec ring).ringCatSheaf)
    moduleSheaf.fromTildeΓ := ‹_›
  (presentationTilde ((modulesSpecToSheaf.obj moduleSheaf).presheaf.obj (.op ⊤))
    .univ (by simp) _ (Submodule.span_eq _)).ofIsIso moduleSheaf.fromTildeΓ

/-- On an affine scheme, quasi-coherence is equivalent to having a global presentation. -/
theorem isQuasicoherent_iff_nonempty_presentation {ring : CommRingCat.{schemeUniverse}}
    (moduleSheaf : (Spec ring).Modules) :
    moduleSheaf.IsQuasicoherent ↔ Nonempty moduleSheaf.Presentation := by
  constructor
  · intro quasicoherent
    letI : moduleSheaf.IsQuasicoherent := quasicoherent
    exact ⟨presentationOfIsIsoFromTildeΓ moduleSheaf⟩
  · rintro ⟨presentation⟩
    exact presentation.isQuasicoherent

/-- Quasi-coherence can be checked using the associated-sections map on every affine open. -/
theorem isQuasicoherent_iff_forall_isAffineOpen (moduleSheaf : scheme.Modules) :
    moduleSheaf.IsQuasicoherent ↔ ∀ (openSubset : scheme.Opens) (affine : IsAffineOpen openSubset),
      IsIso (moduleSheaf.restrict affine.fromSpec).fromTildeΓ := by
  constructor
  · intro quasicoherent openSubset affine
    letI : moduleSheaf.IsQuasicoherent := quasicoherent
    infer_instance
  · intro affineSections
    refine isQuasicoherent_of_iSup_opensRange_eq_top moduleSheaf
      (fun openSubset : scheme.affineOpens ↦ openSubset.2.fromSpec) ?_ ?_
    · simpa only [IsAffineOpen.opensRange_fromSpec] using iSup_affineOpens_eq_top scheme
    · intro openSubset
      letI : IsIso (moduleSheaf.restrict openSubset.2.fromSpec).fromTildeΓ :=
        affineSections openSubset.1 openSubset.2
      exact presentationOfIsIsoFromTildeΓ _

end AlgebraicGeometry.Scheme.Modules
