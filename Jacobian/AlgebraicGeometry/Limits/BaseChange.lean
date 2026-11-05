import Jacobian.CategoryTheory.Limits.Shapes.Pullback.Map
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base change of inverse systems of schemes

Pulling an inverse system back to a scheme over one of its stages produces
another inverse system. A cofiltered limit remains a limit under this base
change, and affine transition maps preserve quasi-compactness and
quasi-separatedness of the chosen stage scheme.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {Index : Type schemeUniverse} [Category.{schemeUniverse} Index]
  (diagram : Index ⥤ Scheme.{schemeUniverse}) (cone : Cone diagram)

variable {stageIndex : Index} {stageScheme : Scheme.{schemeUniverse}}
  (stageMap : stageScheme ⟶ diagram.obj stageIndex)

set_option backward.defeqAttrib.useBackward true in

/-- The system obtained by pulling back to a chosen stage scheme. -/
@[simps] noncomputable def baseChangeDiagram : Over stageIndex ⥤ Scheme.{schemeUniverse} where
  obj sourceIndex := pullback stageMap (diagram.map sourceIndex.hom)
  map {sourceIndex targetIndex} transition :=
    pullback.map _ _ _ _ (𝟙 stageScheme) (diagram.map transition.left) (𝟙 _)
      (by simp) (by simp [← diagram.map_comp, Over.w transition])
  map_id sourceIndex := by apply pullback.hom_ext <;> simp
  map_comp transition nextTransition := by apply pullback.hom_ext <;> simp

set_option backward.defeqAttrib.useBackward true in

/-- The projection to the original system. -/
@[simps] noncomputable def baseChangeDiagramπ :
    baseChangeDiagram diagram stageMap ⟶ Over.forget stageIndex ⋙ diagram where
  app sourceIndex := pullback.snd _ _

set_option backward.defeqAttrib.useBackward true in

/-- The cone whose vertex is the pullback of the original cone vertex. -/
@[simps] noncomputable def baseChangeCone : Cone (baseChangeDiagram diagram stageMap) where
  pt := pullback stageMap (cone.π.app stageIndex)
  π.app sourceIndex :=
    pullback.map _ _ _ _ (𝟙 stageScheme) (cone.π.app sourceIndex.left) (𝟙 _)
      (by simp) (by simp)
  π.naturality {sourceIndex targetIndex} transition := by apply pullback.hom_ext <;> simp

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_fst {sourceIndex targetIndex : Over stageIndex}
    (transition : sourceIndex ⟶ targetIndex) :
    (baseChangeDiagram diagram stageMap).map transition ≫
        pullback.fst stageMap (diagram.map targetIndex.hom) =
      pullback.fst stageMap (diagram.map sourceIndex.hom) := by
  simp [baseChangeDiagram]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeDiagram_map_snd {sourceIndex targetIndex : Over stageIndex}
    (transition : sourceIndex ⟶ targetIndex) :
    (baseChangeDiagram diagram stageMap).map transition ≫
        pullback.snd stageMap (diagram.map targetIndex.hom) =
      pullback.snd stageMap (diagram.map sourceIndex.hom) ≫ diagram.map transition.left := by
  simp [baseChangeDiagram]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeCone_π_app_fst (sourceIndex : Over stageIndex) :
    (baseChangeCone diagram cone stageMap).π.app sourceIndex ≫
        pullback.fst stageMap (diagram.map sourceIndex.hom) =
      pullback.fst stageMap (cone.π.app stageIndex) := by
  simp [baseChangeCone]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma baseChangeCone_π_app_snd (sourceIndex : Over stageIndex) :
    (baseChangeCone diagram cone stageMap).π.app sourceIndex ≫
        pullback.snd stageMap (diagram.map sourceIndex.hom) =
      pullback.snd stageMap (cone.π.app stageIndex) ≫ cone.π.app sourceIndex.left := by
  simp [baseChangeCone]

set_option backward.defeqAttrib.useBackward true in
lemma isPullback_baseChangeDiagram_map {sourceIndex targetIndex : Over stageIndex}
    (transition : sourceIndex ⟶ targetIndex) :
    IsPullback ((baseChangeDiagram diagram stageMap).map transition)
      (pullback.snd stageMap (diagram.map sourceIndex.hom))
      (pullback.snd stageMap (diagram.map targetIndex.hom)) (diagram.map transition.left) :=
  isPullback_pullback_map _ _ _ _ (by rw [← diagram.map_comp, Over.w transition])

set_option backward.defeqAttrib.useBackward true in
lemma isPullback_baseChangeCone_π (sourceIndex : Over stageIndex) :
    IsPullback ((baseChangeCone diagram cone stageMap).π.app sourceIndex)
      (pullback.snd stageMap (cone.π.app stageIndex))
      ((baseChangeDiagramπ diagram stageMap).app sourceIndex) (cone.π.app sourceIndex.left) :=
  isPullback_pullback_map _ _ _ _ (cone.w sourceIndex.hom)

attribute [local instance] CategoryTheory.isConnected_of_hasTerminal

include cone in

/-- Pulling back a cofiltered limit to a stage scheme gives a limiting cone. -/
noncomputable def isLimitBaseChangeCone [IsCofiltered Index] (limit : IsLimit cone) :
    IsLimit (baseChangeCone diagram cone stageMap) :=
  isLimitOfIsPullbackOfIsConnected (baseChangeDiagramπ diagram stageMap) _
    (cone.whisker (Over.forget stageIndex))
    { hom := pullback.snd stageMap (cone.π.app stageIndex)
      w := fun sourceIndex ↦ by simp }
    (isPullback_baseChangeCone_π diagram cone stageMap)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget stageIndex) cone).symm limit)

instance [∀ {firstIndex secondIndex : Index} (transition : firstIndex ⟶ secondIndex),
    IsAffineHom (diagram.map transition)]
    {sourceIndex targetIndex : Over stageIndex} (transition : sourceIndex ⟶ targetIndex) :
    IsAffineHom ((baseChangeDiagram diagram stageMap).map transition) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_baseChangeDiagram_map diagram stageMap transition).flip inferInstance

variable [∀ {firstIndex secondIndex : Index} (transition : firstIndex ⟶ secondIndex),
  IsAffineHom (diagram.map transition)]

instance baseChange_compactSpace {sourceIndex targetIndex : Index}
    (transition : sourceIndex ⟶ targetIndex) {stageScheme : Scheme.{schemeUniverse}}
    (stageMap : stageScheme ⟶ diagram.obj targetIndex)
    [CompactSpace stageScheme] : CompactSpace ↥(pullback stageMap (diagram.map transition)) :=
  have : IsAffineHom (pullback.fst stageMap (diagram.map transition)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiCompact (pullback.fst stageMap (diagram.map transition)) := inferInstance
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst stageMap (diagram.map transition))

instance baseChange_quasiSeparatedSpace {sourceIndex targetIndex : Index}
    (transition : sourceIndex ⟶ targetIndex) {stageScheme : Scheme.{schemeUniverse}}
    (stageMap : stageScheme ⟶ diagram.obj targetIndex)
    [QuasiSeparatedSpace stageScheme] : QuasiSeparatedSpace ↥(pullback stageMap (diagram.map transition)) :=
  have : IsAffineHom (pullback.fst stageMap (diagram.map transition)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : QuasiSeparated (pullback.fst stageMap (diagram.map transition)) := inferInstance
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst stageMap (diagram.map transition))

instance baseChangeDiagram_compactSpace {targetIndex : Index}
    {stageScheme : Scheme.{schemeUniverse}} (stageMap : stageScheme ⟶ diagram.obj targetIndex)
    [CompactSpace stageScheme] (sourceIndex : Over targetIndex) :
    CompactSpace ↥((baseChangeDiagram diagram stageMap).obj sourceIndex) :=
  inferInstanceAs (CompactSpace ↥(pullback stageMap (diagram.map sourceIndex.hom)))

instance baseChangeDiagram_quasiSeparatedSpace {targetIndex : Index}
    {stageScheme : Scheme.{schemeUniverse}} (stageMap : stageScheme ⟶ diagram.obj targetIndex)
    [QuasiSeparatedSpace stageScheme] (sourceIndex : Over targetIndex) :
    QuasiSeparatedSpace ↥((baseChangeDiagram diagram stageMap).obj sourceIndex) :=
  inferInstanceAs (QuasiSeparatedSpace ↥(pullback stageMap (diagram.map sourceIndex.hom)))

/-- The structural map of the pulled-back system to the chosen base stage. -/
@[simps] noncomputable def baseChangeDiagramStructure {stageIndex : Index}
    {stageScheme : Scheme.{schemeUniverse}} (stageMap : stageScheme ⟶ diagram.obj stageIndex) :
    baseChangeDiagram diagram stageMap ⟶
      (Functor.const (Over stageIndex)).obj (diagram.obj stageIndex) where
  app sourceIndex := pullback.fst _ _ ≫ stageMap

end AlgebraicGeometry
