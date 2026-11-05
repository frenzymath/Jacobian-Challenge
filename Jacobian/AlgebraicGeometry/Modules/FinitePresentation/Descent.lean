import Jacobian.AlgebraicGeometry.Modules.FinitePresentation
import Jacobian.AlgebraicGeometry.Modules.DescentEffective

/-!
# Zariski descent of finitely presented module sheaves

Finite presentation is local for open immersions. Consequently the effective
descent of quasi-coherent modules on a Zariski cover realizes finitely presented
descent data by a finitely presented module, without an affine hypothesis on the
scheme being covered.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite presentation can be checked after pullback along an open cover. -/
theorem isFinitePresentation_of_isOpenImmersion
    {scheme : Scheme.{schemeUniverse}} (moduleSheaf : scheme.Modules)
    {Chart : Type schemeUniverse} {charts : Chart → Scheme.{schemeUniverse}}
    (chartMaps : ∀ chartIndex, charts chartIndex ⟶ scheme)
    [∀ chartIndex, IsOpenImmersion (chartMaps chartIndex)]
    (cover : ⨆ chartIndex, (chartMaps chartIndex).opensRange = ⊤)
    (finitePullbacks : ∀ chartIndex,
      ((pullback (chartMaps chartIndex)).obj moduleSheaf).IsFinitePresentation) :
    moduleSheaf.IsFinitePresentation := by
  have finiteRestrictions (chartIndex : Chart) :
      (moduleSheaf.restrict (chartMaps chartIndex)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (charts chartIndex).ringCatSheaf).prop_of_iso
      ((restrictFunctorIsoPullback (chartMaps chartIndex)).app moduleSheaf).symm
      (finitePullbacks chartIndex)
  choose localIndices localOpens presentations localCover finitePresentations using
    fun chartIndex ↦
      letI := finiteRestrictions chartIndex
      exists_isOpenCover_presentation_isFinite
        (moduleSheaf.restrict (chartMaps chartIndex))
  letI := finitePresentations
  refine isFinitePresentation_of_iSup_opensRange_eq_top moduleSheaf
    (fun localIndex : Σ chartIndex, localIndices chartIndex ↦
      (localOpens localIndex.1 localIndex.2).ι ≫ chartMaps localIndex.1) ?_
    (fun localIndex ↦ (presentations localIndex.1 localIndex.2).ofIsIso
      ((restrictFunctorComp (localOpens localIndex.1 localIndex.2).ι
        (chartMaps localIndex.1)).app moduleSheaf).inv)
  refine eq_top_iff.mpr fun point _ ↦ ?_
  obtain ⟨chartIndex, pointInChart⟩ := Opens.mem_iSup.mp
    (cover.ge (Set.mem_univ point) : point ∈ ⨆ chartIndex, (chartMaps chartIndex).opensRange)
  obtain ⟨chartPoint, rfl⟩ := pointInChart
  obtain ⟨localIndex, pointInOpen⟩ := (localCover chartIndex).exists_mem chartPoint
  exact Opens.mem_iSup.mpr ⟨⟨chartIndex, localIndex⟩,
    ⟨⟨chartPoint, pointInOpen⟩, rfl⟩⟩

/-- Finitely presented descent data on a Zariski cover glue to an actual finitely presented
module sheaf. -/
theorem exists_isFinitePresentation_toDescentData_iso
    {scheme : Scheme.{schemeUniverse}} (cover : scheme.OpenCover.{schemeUniverse})
    (datum : modulesPseudofunctor.DescentData cover.f)
    (finiteCoefficients : ∀ chartIndex,
      (datum.obj chartIndex : (cover.X chartIndex).Modules).IsFinitePresentation) :
    ∃ moduleSheaf : scheme.Modules, moduleSheaf.IsFinitePresentation ∧
      moduleSheaf.IsQuasicoherent ∧
      Nonempty ((modulesPseudofunctor.toDescentData cover.f).obj moduleSheaf ≅ datum) := by
  have quasiCoherentCoefficients (chartIndex : cover.I₀) :
      (datum.obj chartIndex : (cover.X chartIndex).Modules).IsQuasicoherent := by
    letI := finiteCoefficients chartIndex
    exact (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (datum.obj chartIndex)).choose.isQuasicoherent
  obtain ⟨moduleSheaf, quasiCoherent, ⟨realization⟩⟩ :=
    exists_isQuasicoherent_toDescentData_iso_of_mem_fpqcTopology cover.f
      (Scheme.zariskiTopology_le_fpqcTopology _ cover.mem_grothendieckTopology)
      datum quasiCoherentCoefficients
  refine ⟨moduleSheaf, ?_, quasiCoherent, ⟨realization⟩⟩
  apply isFinitePresentation_of_isOpenImmersion moduleSheaf cover.f cover.iSup_opensRange
  intro chartIndex
  let component : ((modulesPseudofunctor.toDescentData cover.f).obj moduleSheaf).obj
      chartIndex ≅ datum.obj chartIndex :=
    { hom := realization.hom.hom chartIndex
      inv := realization.inv.hom chartIndex
      hom_inv_id := by
        simpa only [Pseudofunctor.DescentData.comp_hom,
          Pseudofunctor.DescentData.id_hom] using
          congrArg (fun coefficientMap ↦ coefficientMap.hom chartIndex)
            realization.hom_inv_id
      inv_hom_id := by
        simpa only [Pseudofunctor.DescentData.comp_hom,
          Pseudofunctor.DescentData.id_hom] using
          congrArg (fun coefficientMap ↦ coefficientMap.hom chartIndex)
            realization.inv_hom_id }
  have finiteComponent :
      (((modulesPseudofunctor.toDescentData cover.f).obj moduleSheaf).obj chartIndex :
        (cover.X chartIndex).Modules).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (cover.X chartIndex).ringCatSheaf).prop_of_iso
      component.symm (finiteCoefficients chartIndex)
  change
    ((pullback (cover.f chartIndex)).obj moduleSheaf).IsFinitePresentation at finiteComponent
  exact finiteComponent

end AlgebraicGeometry.Scheme.Modules
