import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback

/-!
# Open preimages and their overlap diagrams

Restriction along a map over a fixed scheme is compatible with intersections,
diagonals and composition. Intersections and triple intersections give chosen
pullbacks for native module-sheaf descent.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

section Res

variable {baseScheme target source furtherSource : Scheme.{schemeUniverse}} {targetMap : target ⟶ baseScheme} {sourceMap : source ⟶ baseScheme}

/-- The restriction `sourceMap⁻¹ sourceOpen ⟶ targetMap⁻¹ targetOpen` of a morphism `morphism : source ⟶ target` over `baseScheme`, for `sourceOpen ≤ targetOpen`. -/
noncomputable def restrictPreimage (morphism : source ⟶ target) (hg : morphism ≫ targetMap = sourceMap) {targetOpen sourceOpen : baseScheme.Opens} (hWV : sourceOpen ≤ targetOpen) :
    (sourceMap ⁻¹ᵁ sourceOpen).toScheme ⟶ (targetMap ⁻¹ᵁ targetOpen).toScheme :=
  morphism.resLE (targetMap ⁻¹ᵁ targetOpen) (sourceMap ⁻¹ᵁ sourceOpen) (by
    subst hg
    rw [Scheme.Hom.comp_preimage]
    exact morphism.preimage_mono (targetMap.preimage_mono hWV))

@[reassoc (attr := simp)]
lemma restrictPreimage_ι (morphism : source ⟶ target) (hg : morphism ≫ targetMap = sourceMap) {targetOpen sourceOpen : baseScheme.Opens} (hWV : sourceOpen ≤ targetOpen) :
    restrictPreimage morphism hg hWV ≫ (targetMap ⁻¹ᵁ targetOpen).ι = (sourceMap ⁻¹ᵁ sourceOpen).ι ≫ morphism :=
  Scheme.Hom.resLE_comp_ι _ _

@[reassoc (attr := simp)]
lemma homOfLE_restrictPreimage (morphism : source ⟶ target) (hg : morphism ≫ targetMap = sourceMap) {targetOpen sourceOpen furtherOpen : baseScheme.Opens} (inclusion : sourceMap ⁻¹ᵁ furtherOpen ≤ sourceMap ⁻¹ᵁ sourceOpen)
    (hWV : sourceOpen ≤ targetOpen) (hW'V : furtherOpen ≤ targetOpen) :
    source.homOfLE inclusion ≫ restrictPreimage morphism hg hWV = restrictPreimage morphism hg hW'V := by
  rw [← cancel_mono (targetMap ⁻¹ᵁ targetOpen).ι]
  simp

@[reassoc]
lemma restrictPreimage_comp (morphism : source ⟶ target) (hg : morphism ≫ targetMap = sourceMap) {furtherStructureMap : furtherSource ⟶ baseScheme} (furtherMap : furtherSource ⟶ source) (hg₂ : furtherMap ≫ sourceMap = furtherStructureMap)
    {composite : furtherSource ⟶ target} (hh : furtherMap ≫ morphism = composite) (hg' : composite ≫ targetMap = furtherStructureMap) {targetOpen sourceOpen furtherOpen : baseScheme.Opens} (hWV : sourceOpen ≤ targetOpen)
    (hW'W : furtherOpen ≤ sourceOpen) (hW'V : furtherOpen ≤ targetOpen) :
    restrictPreimage furtherMap hg₂ hW'W ≫ restrictPreimage morphism hg hWV = restrictPreimage composite hg' hW'V := by
  rw [← cancel_mono (targetMap ⁻¹ᵁ targetOpen).ι]
  simp [← hh]


@[reassoc (attr := simp)]
lemma restrictPreimage_homOfLE (morphism : source ⟶ target) (hg : morphism ≫ targetMap = sourceMap) {targetOpen largerOpen sourceOpen : baseScheme.Opens} (hWV : sourceOpen ≤ targetOpen)
    (hVV' : targetOpen ≤ largerOpen) :
    restrictPreimage morphism hg hWV ≫ target.homOfLE (targetMap.preimage_mono hVV') = restrictPreimage morphism hg (hWV.trans hVV') := by
  rw [← cancel_mono (targetMap ⁻¹ᵁ largerOpen).ι]
  simp

end Res

section Diagrams

variable {Index : Type schemeUniverse} [Category.{schemeUniverse} Index]
  (diagram : Index ⥤ Scheme.{schemeUniverse}) {baseScheme : Scheme.{schemeUniverse}}
  (structureMap : diagram ⟶ (Functor.const Index).obj baseScheme)

/-- An inverse system restricted to the preimage of a fixed open in its base. -/
def preimageDiagram (baseOpen : baseScheme.Opens) : Index ⥤ Scheme.{schemeUniverse} where
  obj stageIndex := structureMap.app stageIndex ⁻¹ᵁ baseOpen
  map {sourceIndex targetIndex} transition := restrictPreimage (diagram.map transition)
    (by simpa using structureMap.naturality transition) le_rfl
  map_id stageIndex := by
    apply (cancel_mono (structureMap.app stageIndex ⁻¹ᵁ baseOpen).ι).mp
    simp
  map_comp firstTransition secondTransition := by
    apply (cancel_mono (structureMap.app _ ⁻¹ᵁ baseOpen).ι).mp
    simp [Category.assoc]

@[simp]
lemma preimageDiagram_map {baseOpen : baseScheme.Opens} {sourceIndex targetIndex : Index}
    (transition : sourceIndex ⟶ targetIndex) :
    (preimageDiagram diagram structureMap baseOpen).map transition =
      restrictPreimage (diagram.map transition)
        (by simpa using structureMap.naturality transition) le_rfl := rfl

/-- The open immersions from a preimage diagram to its original diagram. -/
@[simps]
def preimageDiagramι (baseOpen : baseScheme.Opens) :
    preimageDiagram diagram structureMap baseOpen ⟶ diagram where
  app stageIndex := (structureMap.app stageIndex ⁻¹ᵁ baseOpen).ι
  naturality sourceIndex targetIndex transition := by simp

instance (baseOpen : baseScheme.Opens) (stageIndex : Index) :
    IsOpenImmersion ((preimageDiagramι diagram structureMap baseOpen).app stageIndex) := by
  change IsOpenImmersion (structureMap.app stageIndex ⁻¹ᵁ baseOpen).ι
  infer_instance

variable (cone : Cone diagram) (limitMap : cone.pt ⟶ baseScheme)
  (factorization : ∀ stageIndex, cone.π.app stageIndex ≫ structureMap.app stageIndex = limitMap)

/-- Restriction of a cone to the preimage of a fixed open. -/
def preimageCone (baseOpen : baseScheme.Opens) :
    Cone (preimageDiagram diagram structureMap baseOpen) where
  pt := limitMap ⁻¹ᵁ baseOpen
  π.app stageIndex := restrictPreimage (cone.π.app stageIndex) (factorization stageIndex) le_rfl
  π.naturality sourceIndex targetIndex transition := by
    apply (cancel_mono (structureMap.app targetIndex ⁻¹ᵁ baseOpen).ι).mp
    simp [Category.assoc, cone.w]

@[simp]
lemma preimageCone_π_app (baseOpen : baseScheme.Opens) (stageIndex : Index) :
    (preimageCone diagram structureMap cone limitMap factorization baseOpen).π.app stageIndex =
      restrictPreimage (cone.π.app stageIndex) (factorization stageIndex) le_rfl := rfl

/-- Restricting a connected limit of schemes to an open preimage preserves its limit. -/
def isLimit_preimageCone [IsConnected Index] (limit : IsLimit cone)
    (baseOpen : baseScheme.Opens) :
    IsLimit (preimageCone diagram structureMap cone limitMap factorization baseOpen) :=
  isLimitOfIsPullbackOfIsConnected (preimageDiagramι diagram structureMap baseOpen) _ _
    (by
      refine { hom := (limitMap ⁻¹ᵁ baseOpen).ι, w := ?_ }
      intro stageIndex
      simp [preimageCone])
    (fun stageIndex ↦ IsOpenImmersion.isPullback _ _ _ _
      (by simp [preimageCone])
      (by simp [preimageCone, ← Scheme.Hom.comp_preimage, factorization])) limit

end Diagrams

section ChosenPullback

variable {baseScheme : Scheme.{schemeUniverse}} {Chart : Type schemeUniverse} (opens : Chart → baseScheme.Opens) {source : Scheme.{schemeUniverse}} (sourceMap : source ⟶ baseScheme)

/-- The intersection `sourceMap⁻¹ (opens firstIndex ⊓ opens secondIndex)` as a chosen pullback of the open immersions of `sourceMap⁻¹ opens firstIndex`
and `sourceMap⁻¹ opens secondIndex`. -/
@[simps]
noncomputable def preimageChosenPullback (firstIndex secondIndex : Chart) :
    ChosenPullback (sourceMap ⁻¹ᵁ opens firstIndex).ι (sourceMap ⁻¹ᵁ opens secondIndex).ι where
  pullback := sourceMap ⁻¹ᵁ (opens firstIndex ⊓ opens secondIndex)
  p₁ := source.homOfLE (sourceMap.preimage_mono inf_le_left)
  p₂ := source.homOfLE (sourceMap.preimage_mono inf_le_right)
  condition := by simp
  isLimit := (IsOpenImmersion.isPullback (source.homOfLE (sourceMap.preimage_mono inf_le_left))
    (source.homOfLE (sourceMap.preimage_mono inf_le_right)) (sourceMap ⁻¹ᵁ opens firstIndex).ι (sourceMap ⁻¹ᵁ opens secondIndex).ι (by simp)
    (by ext point; simp)).isLimit
  p := (sourceMap ⁻¹ᵁ (opens firstIndex ⊓ opens secondIndex)).ι
  hp₁ := by simp

/-- The triple intersection `sourceMap⁻¹ (opens firstIndex ⊓ opens secondIndex ⊓ opens thirdIndex)` as a chosen wide pullback. -/
@[simps]
noncomputable def preimageChosenPullback₃ (firstIndex secondIndex thirdIndex : Chart) :
    ChosenPullback₃ (preimageChosenPullback opens sourceMap firstIndex secondIndex) (preimageChosenPullback opens sourceMap secondIndex thirdIndex)
      (preimageChosenPullback opens sourceMap firstIndex thirdIndex) where
  chosenPullback :=
    { pullback := sourceMap ⁻¹ᵁ (opens firstIndex ⊓ opens secondIndex ⊓ opens thirdIndex)
      p₁ := source.homOfLE (sourceMap.preimage_mono inf_le_left)
      p₂ := source.homOfLE (sourceMap.preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
      condition := by simp
      isLimit := by
        refine (IsOpenImmersion.isPullback (source.homOfLE (sourceMap.preimage_mono inf_le_left))
          (source.homOfLE (sourceMap.preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right)))
          (source.homOfLE (sourceMap.preimage_mono inf_le_right))
          (source.homOfLE (sourceMap.preimage_mono inf_le_left)) (by simp) ?_).isLimit
        ext point
        simp only [opensRange_homOfLE, TopologicalSpace.Opens.map_coe,
          TopologicalSpace.Opens.coe_inf, Set.preimage_inter, Set.mem_inter_iff,
          Set.mem_preimage, Opens.ι_apply, homOfLE_apply, SetLike.mem_coe, iff_self_and,
          and_imp]
        exact fun _ _ ↦ point.2.2
      p := source.homOfLE (sourceMap.preimage_mono (inf_le_left.trans inf_le_right))
      hp₁ := by simp }
  p := (sourceMap ⁻¹ᵁ (opens firstIndex ⊓ opens secondIndex ⊓ opens thirdIndex)).ι
  p₁ := source.homOfLE (sourceMap.preimage_mono (inf_le_left.trans inf_le_left))
  p₃ := source.homOfLE (sourceMap.preimage_mono inf_le_right)
  l :=
    { f := source.homOfLE (sourceMap.preimage_mono (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) }
  hp₁ := by simp
  hp₃ := by simp

variable (firstIndex secondIndex thirdIndex : Chart)

@[simp]
lemma preimageChosenPullback₃_p₁₂ :
    (preimageChosenPullback₃ opens sourceMap firstIndex secondIndex thirdIndex).p₁₂ = source.homOfLE (sourceMap.preimage_mono inf_le_left) := rfl

@[simp]
lemma preimageChosenPullback₃_p₂₃ :
    (preimageChosenPullback₃ opens sourceMap firstIndex secondIndex thirdIndex).p₂₃ =
      source.homOfLE (sourceMap.preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) := rfl

@[simp]
lemma preimageChosenPullback₃_p₁₃ :
    (preimageChosenPullback₃ opens sourceMap firstIndex secondIndex thirdIndex).p₁₃ =
      source.homOfLE (sourceMap.preimage_mono (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) := rfl

@[simp]
lemma preimageChosenPullback₃_p₂ :
    (preimageChosenPullback₃ opens sourceMap firstIndex secondIndex thirdIndex).p₂ =
      source.homOfLE (sourceMap.preimage_mono (inf_le_left.trans inf_le_right)) := rfl

/-- The diagonal `sourceMap⁻¹ opens firstIndex ⟶ sourceMap⁻¹ (opens firstIndex ⊓ opens firstIndex)`. -/
noncomputable def preimageDiagonal (firstIndex : Chart) :
    (sourceMap ⁻¹ᵁ opens firstIndex).toScheme ⟶ (preimageChosenPullback opens sourceMap firstIndex firstIndex).pullback :=
  source.homOfLE (sourceMap.preimage_mono (le_inf le_rfl le_rfl))

@[reassoc (attr := simp)]
lemma preimageDiagonal_p₁ (firstIndex : Chart) : preimageDiagonal opens sourceMap firstIndex ≫ (preimageChosenPullback opens sourceMap firstIndex firstIndex).p₁ = 𝟙 _ := by
  simp [preimageDiagonal]

@[reassoc (attr := simp)]
lemma preimageDiagonal_p₂ (firstIndex : Chart) : preimageDiagonal opens sourceMap firstIndex ≫ (preimageChosenPullback opens sourceMap firstIndex firstIndex).p₂ = 𝟙 _ := by
  simp [preimageDiagonal]

end ChosenPullback

section ResTo

/-! ### Restrictions of a morphism over `baseScheme` to the chosen pullbacks -/

variable {baseScheme : Scheme.{schemeUniverse}} {Chart : Type schemeUniverse} (opens : Chart → baseScheme.Opens) {source furtherSource : Scheme.{schemeUniverse}} {sourceMap : source ⟶ baseScheme}
  {furtherStructureMap : furtherSource ⟶ baseScheme} (morphism : furtherSource ⟶ source) (hg : morphism ≫ sourceMap = furtherStructureMap) (firstIndex secondIndex thirdIndex : Chart)

lemma restrictPreimage_p₁ : restrictPreimage morphism hg (le_refl (opens firstIndex ⊓ opens secondIndex)) ≫ (preimageChosenPullback opens sourceMap firstIndex secondIndex).p₁ =
    (preimageChosenPullback opens furtherStructureMap firstIndex secondIndex).p₁ ≫ restrictPreimage morphism hg (le_refl (opens firstIndex)) := by
  rw [← cancel_mono (sourceMap ⁻¹ᵁ _).ι]
  simp

lemma restrictPreimage_p₂ : restrictPreimage morphism hg (le_refl (opens firstIndex ⊓ opens secondIndex)) ≫ (preimageChosenPullback opens sourceMap firstIndex secondIndex).p₂ =
    (preimageChosenPullback opens furtherStructureMap firstIndex secondIndex).p₂ ≫ restrictPreimage morphism hg (le_refl (opens secondIndex)) := by
  rw [← cancel_mono (sourceMap ⁻¹ᵁ _).ι]
  simp

lemma restrictPreimage_p₁₂ :
    restrictPreimage morphism hg (le_refl (opens firstIndex ⊓ opens secondIndex ⊓ opens thirdIndex)) ≫ (preimageChosenPullback₃ opens sourceMap firstIndex secondIndex thirdIndex).p₁₂ =
      (preimageChosenPullback₃ opens furtherStructureMap firstIndex secondIndex thirdIndex).p₁₂ ≫ restrictPreimage morphism hg (le_refl (opens firstIndex ⊓ opens secondIndex)) := by
  rw [← cancel_mono (sourceMap ⁻¹ᵁ _).ι]
  simp

lemma restrictPreimage_p₂₃ :
    restrictPreimage morphism hg (le_refl (opens firstIndex ⊓ opens secondIndex ⊓ opens thirdIndex)) ≫ (preimageChosenPullback₃ opens sourceMap firstIndex secondIndex thirdIndex).p₂₃ =
      (preimageChosenPullback₃ opens furtherStructureMap firstIndex secondIndex thirdIndex).p₂₃ ≫ restrictPreimage morphism hg (le_refl (opens secondIndex ⊓ opens thirdIndex)) := by
  rw [← cancel_mono (sourceMap ⁻¹ᵁ _).ι]
  simp

lemma restrictPreimage_p₁₃ :
    restrictPreimage morphism hg (le_refl (opens firstIndex ⊓ opens secondIndex ⊓ opens thirdIndex)) ≫ (preimageChosenPullback₃ opens sourceMap firstIndex secondIndex thirdIndex).p₁₃ =
      (preimageChosenPullback₃ opens furtherStructureMap firstIndex secondIndex thirdIndex).p₁₃ ≫ restrictPreimage morphism hg (le_refl (opens firstIndex ⊓ opens thirdIndex)) := by
  rw [← cancel_mono (sourceMap ⁻¹ᵁ _).ι]
  simp

lemma restrictPreimage_first :
    restrictPreimage morphism hg (le_refl (opens firstIndex ⊓ opens secondIndex ⊓ opens thirdIndex)) ≫ (preimageChosenPullback₃ opens sourceMap firstIndex secondIndex thirdIndex).p₁ =
      (preimageChosenPullback₃ opens furtherStructureMap firstIndex secondIndex thirdIndex).p₁ ≫ restrictPreimage morphism hg (le_refl (opens firstIndex)) := by
  rw [← cancel_mono (sourceMap ⁻¹ᵁ _).ι]
  simp

lemma restrictPreimage_middle :
    restrictPreimage morphism hg (le_refl (opens firstIndex ⊓ opens secondIndex ⊓ opens thirdIndex)) ≫ (preimageChosenPullback₃ opens sourceMap firstIndex secondIndex thirdIndex).p₂ =
      (preimageChosenPullback₃ opens furtherStructureMap firstIndex secondIndex thirdIndex).p₂ ≫ restrictPreimage morphism hg (le_refl (opens secondIndex)) := by
  rw [← cancel_mono (sourceMap ⁻¹ᵁ _).ι]
  simp

lemma restrictPreimage_last :
    restrictPreimage morphism hg (le_refl (opens firstIndex ⊓ opens secondIndex ⊓ opens thirdIndex)) ≫ (preimageChosenPullback₃ opens sourceMap firstIndex secondIndex thirdIndex).p₃ =
      (preimageChosenPullback₃ opens furtherStructureMap firstIndex secondIndex thirdIndex).p₃ ≫ restrictPreimage morphism hg (le_refl (opens thirdIndex)) := by
  rw [← cancel_mono (sourceMap ⁻¹ᵁ _).ι]
  simp

lemma preimageDiagonal_restrictPreimage :
    preimageDiagonal opens furtherStructureMap firstIndex ≫ restrictPreimage morphism hg (le_refl (opens firstIndex ⊓ opens firstIndex)) =
      restrictPreimage morphism hg (le_refl (opens firstIndex)) ≫ preimageDiagonal opens sourceMap firstIndex := by
  simp [preimageDiagonal]

end ResTo

end AlgebraicGeometry.Scheme.Modules
