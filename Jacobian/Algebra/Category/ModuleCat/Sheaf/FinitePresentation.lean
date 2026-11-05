import Jacobian.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Finite presentations of module sheaves

Finite local presentation data give the native finite-presentation property,
independently of the universe of the cover. A finite global presentation gives
such local data by restriction to the trivial covering family.

Finite presentation descends along covering families. Continuous and
cocontinuous change of site preserves finite presentation when its local
pushforward functors preserve colimits and carry the unit to the unit.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe dataUniverse ringUniverse morphismUniverse objectUniverse
  targetMorphismUniverse targetObjectUniverse

open CategoryTheory Limits

namespace SheafOfModules

variable {site : Type objectUniverse} [Category.{morphismUniverse} site]
  {topology : GrothendieckTopology site}
  {ringSheaf : Sheaf topology RingCat.{ringUniverse}}
  [∀ object, HasSheafify (topology.over object) AddCommGrpCat.{ringUniverse}]
  [∀ object, (topology.over object).WEqualsLocallyBijective AddCommGrpCat.{ringUniverse}]

/-- Shrinking the indexing type of finite local presentation data preserves finiteness. -/
instance QuasicoherentData.isFinitePresentation_shrink
    {moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    (localData : QuasicoherentData.{dataUniverse} moduleSheaf) [localData.IsFinitePresentation] :
    localData.shrink.IsFinitePresentation where
  isFinite_presentation index := by
    change (localData.presentation index.2.choose).IsFinite
    exact QuasicoherentData.IsFinitePresentation.isFinite_presentation
      (q := localData) index.2.choose

/-- Finite local presentation data with a cover in any universe give finite presentation. -/
theorem QuasicoherentData.isFinitePresentation
    {moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    (localData : QuasicoherentData.{dataUniverse} moduleSheaf) [localData.IsFinitePresentation] :
    moduleSheaf.IsFinitePresentation :=
  ⟨localData.shrink, inferInstance⟩

section GlobalPresentation

variable [HasBinaryProducts site] [HasSheafify topology AddCommGrpCat.{ringUniverse}]
  [topology.WEqualsLocallyBijective AddCommGrpCat.{ringUniverse}]

/-- The local data attached to a finite global presentation have finite presentations. -/
instance Presentation.isFinitePresentation_quasicoherentData
    {moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    (presentation : moduleSheaf.Presentation) [presentation.IsFinite] :
    presentation.quasicoherentData.IsFinitePresentation where
  isFinite_presentation object :=
    { isFiniteType_generators := ⟨by
        change Finite presentation.generators.I
        infer_instance⟩
      isFiniteType_relations := ⟨by
        change Finite presentation.relations.I
        infer_instance⟩ }

/-- A finite global presentation gives the native finite-presentation property. -/
theorem Presentation.isFinitePresentation
    {moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    (presentation : moduleSheaf.Presentation) [presentation.IsFinite] :
    moduleSheaf.IsFinitePresentation :=
  presentation.quasicoherentData.isFinitePresentation

end GlobalPresentation

section Pushforward

variable {targetSite : Type targetObjectUniverse}
  [Category.{targetMorphismUniverse} targetSite]
  {targetTopology : GrothendieckTopology targetSite}
  {targetRingSheaf : Sheaf targetTopology RingCat.{ringUniverse}}
  [∀ object, (targetTopology.over object).WEqualsLocallyBijective AddCommGrpCat]
  [∀ object, HasSheafify (targetTopology.over object) AddCommGrpCat.{ringUniverse}]
  (siteFunctor : targetSite ⥤ site)
  [siteFunctor.IsContinuous targetTopology topology]
  [siteFunctor.IsCocontinuous targetTopology topology]
  (ringMap : targetRingSheaf ⟶
    (siteFunctor.sheafPushforwardContinuous RingCat.{ringUniverse} targetTopology topology).obj
      ringSheaf)

/-- Change of site preserves finite local presentations when the local
pushforwards preserve colimits and the unit. -/
instance QuasicoherentData.isFinitePresentation_pushforward
    (unitIso : (SheafOfModules.pushforward.{ringUniverse} ringMap).obj
      (unit ringSheaf) ≅ unit targetRingSheaf)
    [∀ object, (Over.post (X := object) siteFunctor).IsContinuous
      (targetTopology.over object) (topology.over _)]
    (preserves : ∀ (object : targetSite) (openObject : site)
      (morphism : siteFunctor.obj object ⟶ openObject),
      PreservesColimitsOfSize.{ringUniverse, ringUniverse}
        (SheafOfModules.pushforward.{ringUniverse} (R := ringSheaf.over openObject)
          (F := Over.post (X := object) siteFunctor ⋙ Over.map morphism)
          (((Over.forget object).sheafPushforwardContinuous RingCat.{ringUniverse}
            (targetTopology.over object) targetTopology).map ringMap)))
    {moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    (localData : moduleSheaf.QuasicoherentData) [localData.IsFinitePresentation] :
    (localData.pushforward siteFunctor ringMap unitIso preserves).IsFinitePresentation where
  isFinite_presentation index := by
    letI := preserves index.1 (localData.X index.2.1) index.2.2
    exact Presentation.isFinite_map _ _ _

/-- Finite presentation is preserved by a colimit-preserving local change of site. -/
theorem isFinitePresentation_pushforward
    (unitIso : (SheafOfModules.pushforward.{ringUniverse} ringMap).obj
      (unit ringSheaf) ≅ unit targetRingSheaf)
    [∀ object, (Over.post (X := object) siteFunctor).IsContinuous
      (targetTopology.over object) (topology.over _)]
    (preserves : ∀ (object : targetSite) (openObject : site)
      (morphism : siteFunctor.obj object ⟶ openObject),
      PreservesColimitsOfSize.{ringUniverse, ringUniverse}
        (SheafOfModules.pushforward.{ringUniverse} (R := ringSheaf.over openObject)
          (F := Over.post (X := object) siteFunctor ⋙ Over.map morphism)
          (((Over.forget object).sheafPushforwardContinuous RingCat.{ringUniverse}
            (targetTopology.over object) targetTopology).map ringMap)))
    {moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    [moduleSheaf.IsFinitePresentation] :
    ((SheafOfModules.pushforward.{ringUniverse} ringMap).obj moduleSheaf).IsFinitePresentation := by
  obtain ⟨localData, finiteData⟩ := IsFinitePresentation.exists_quasicoherentData moduleSheaf
  letI := finiteData
  exact (localData.pushforward siteFunctor ringMap unitIso preserves).isFinitePresentation

/-- Change of site along a left adjoint and an isomorphism of rings preserves
finite presentation. -/
theorem isFinitePresentation_pushforward_of_isLeftAdjoint
    (unitIso : (SheafOfModules.pushforward.{ringUniverse} ringMap).obj
      (unit ringSheaf) ≅ unit targetRingSheaf)
    [siteFunctor.IsLeftAdjoint] [IsIso ringMap]
    [∀ object, (Over.post (X := object) siteFunctor).IsContinuous
      (targetTopology.over object) (topology.over _)]
    [HasPullbacks site] [HasPullbacks targetSite]
    {moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf}
    [moduleSheaf.IsFinitePresentation] :
    ((SheafOfModules.pushforward.{ringUniverse} ringMap).obj moduleSheaf).IsFinitePresentation := by
  apply +allowSynthFailures isFinitePresentation_pushforward siteFunctor ringMap unitIso _
  intro object openObject morphism
  let localFunctor := Over.post (X := object) siteFunctor ⋙ Over.map morphism
  have : localFunctor.IsContinuous (targetTopology.over object) (topology.over openObject) :=
    Functor.isContinuous_comp _ _ _ (topology.over _) _
  have : localFunctor.IsCocontinuous (targetTopology.over object) (topology.over openObject) :=
    isCocontinuous_comp _ _ _ (topology.over _)
  let localRingMap : targetRingSheaf.over object ⟶
      (localFunctor.sheafPushforwardContinuous RingCat.{ringUniverse}
        (targetTopology.over object) (topology.over openObject)).obj
          (ringSheaf.over openObject) :=
    ((Over.forget object).sheafPushforwardContinuous RingCat.{ringUniverse}
      (targetTopology.over object) targetTopology).map ringMap
  have : (SheafOfModules.pushforward.{ringUniverse} localRingMap).IsLeftAdjoint :=
    isLeftAdjoint_pushforward_of_isIso localRingMap
  infer_instance

end Pushforward

section Descent

variable [∀ first second, HasSheafify ((topology.over first).over second)
    AddCommGrpCat.{ringUniverse}]
  [∀ first second, ((topology.over first).over second).WEqualsLocallyBijective
    AddCommGrpCat.{ringUniverse}]

/-- Gluing finite presentations along a cover preserves finiteness. -/
instance QuasicoherentData.isFinitePresentation_bind
    (moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf)
    {indices : Type ringUniverse} (objects : indices → site)
    (cover : topology.CoversTop objects)
    (localData : ∀ index, (moduleSheaf.over (objects index)).QuasicoherentData)
    [∀ index, (localData index).IsFinitePresentation] :
    (QuasicoherentData.bind moduleSheaf objects cover localData).IsFinitePresentation where
  isFinite_presentation index := by
    dsimp only [QuasicoherentData.bind]
    infer_instance

/-- Finite presentation can be checked on a covering family. -/
theorem IsFinitePresentation.of_coversTop
    (moduleSheaf : SheafOfModules.{ringUniverse} ringSheaf)
    {indices : Type ringUniverse} (objects : indices → site)
    (cover : topology.CoversTop objects)
    [∀ index, (moduleSheaf.over (objects index)).IsFinitePresentation] :
    moduleSheaf.IsFinitePresentation := by
  choose localData finiteData using fun index ↦
    IsFinitePresentation.exists_quasicoherentData (moduleSheaf.over (objects index))
  letI := finiteData
  exact (QuasicoherentData.bind moduleSheaf objects cover localData).isFinitePresentation

end Descent

end SheafOfModules
