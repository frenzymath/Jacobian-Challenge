import Jacobian.AlgebraicGeometry.Limits.BaseChange

/-!
# Eventual isomorphisms of finite-stage models

Two quasi-compact, quasi-separated schemes locally of finite presentation over
one stage of a cofiltered system with affine transitions become isomorphic at
a later stage if their pullbacks to the limit are identified. The resulting
isomorphism is compatible with the base and with the given limit comparison,
for any choices of Cartesian representatives at that later stage.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {Index : Type schemeUniverse} [Category.{schemeUniverse} Index]
  {diagram : Index ⥤ Scheme.{schemeUniverse}} {cone : Cone diagram} (limit : IsLimit cone)
  [IsCofiltered Index]
  [∀ {sourceIndex targetIndex : Index} (transition : sourceIndex ⟶ targetIndex),
    IsAffineHom (diagram.map transition)]

include limit in
/-- Two locally finitely presented models of the same scheme over a cofiltered limit
become compatibly isomorphic at a later stage. The stage models are assumed
quasi-compact and quasi-separated; the stages themselves need not be affine. -/
lemma Scheme.exists_iso_of_isPullback_of_isLimit {limitScheme : Scheme.{schemeUniverse}}
    {limitMap : limitScheme ⟶ cone.pt} {stageIndex : Index}
    {firstModel secondModel : Scheme.{schemeUniverse}}
    {firstStructure : firstModel ⟶ diagram.obj stageIndex}
    {secondStructure : secondModel ⟶ diagram.obj stageIndex}
    {firstComparison : limitScheme ⟶ firstModel} {secondComparison : limitScheme ⟶ secondModel}
    [LocallyOfFinitePresentation firstStructure] [LocallyOfFinitePresentation secondStructure]
    [CompactSpace firstModel] [QuasiSeparatedSpace firstModel]
    [CompactSpace secondModel] [QuasiSeparatedSpace secondModel]
    (firstSquare : IsPullback firstComparison limitMap firstStructure (cone.π.app stageIndex))
    (secondSquare : IsPullback secondComparison limitMap secondStructure (cone.π.app stageIndex)) :
    ∃ (laterIndex : Index) (transition : laterIndex ⟶ stageIndex),
      ∀ {firstLaterModel secondLaterModel : Scheme.{schemeUniverse}}
      {firstLaterStructure : firstLaterModel ⟶ diagram.obj laterIndex}
      {firstLaterProjection : firstLaterModel ⟶ firstModel}
      {secondLaterStructure : secondLaterModel ⟶ diagram.obj laterIndex}
      {secondLaterProjection : secondLaterModel ⟶ secondModel}
      {firstLaterComparison : limitScheme ⟶ firstLaterModel}
      {secondLaterComparison : limitScheme ⟶ secondLaterModel},
      IsPullback firstLaterProjection firstLaterStructure firstStructure (diagram.map transition) →
      firstLaterComparison ≫ firstLaterProjection = firstComparison →
      firstLaterComparison ≫ firstLaterStructure = limitMap ≫ cone.π.app laterIndex →
      IsPullback secondLaterProjection secondLaterStructure secondStructure (diagram.map transition) →
      secondLaterComparison ≫ secondLaterProjection = secondComparison →
      secondLaterComparison ≫ secondLaterStructure = limitMap ≫ cone.π.app laterIndex →
      ∃ modelIso : firstLaterModel ≅ secondLaterModel,
        modelIso.hom ≫ secondLaterStructure = firstLaterStructure ∧
        firstLaterComparison ≫ modelIso.hom = secondLaterComparison := by
  classical
  have firstComparison_fst : firstSquare.isoPullback.hom ≫ pullback.fst firstStructure (cone.π.app
    stageIndex) = firstComparison :=
    IsPullback.isoPullback_hom_fst _
  have firstComparison_snd : firstSquare.isoPullback.hom ≫ pullback.snd firstStructure (cone.π.app
    stageIndex) = limitMap :=
    IsPullback.isoPullback_hom_snd _
  have secondComparison_fst : secondSquare.isoPullback.hom ≫ pullback.fst secondStructure (cone.π.app
    stageIndex) = secondComparison :=
    IsPullback.isoPullback_hom_fst _
  have secondComparison_snd : secondSquare.isoPullback.hom ≫ pullback.snd secondStructure (cone.π.app
    stageIndex) = limitMap :=
    IsPullback.isoPullback_hom_snd _
  have firstInverse_structure : firstSquare.isoPullback.inv ≫ limitMap = pullback.snd firstStructure
    (cone.π.app stageIndex) := by
    rw [Iso.inv_comp_eq, firstComparison_snd]
  have secondInverse_structure : secondSquare.isoPullback.inv ≫ limitMap = pullback.snd secondStructure
    (cone.π.app stageIndex) := by
    rw [Iso.inv_comp_eq, secondComparison_snd]
  obtain ⟨firstStage, forwardApproximation, forwardApproximation_limit, forwardApproximation_structure⟩
    := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (baseChangeDiagram diagram firstStructure) (baseChangeDiagramStructure diagram firstStructure)
        secondStructure (baseChangeCone diagram cone firstStructure)
      (isLimitBaseChangeCone diagram cone firstStructure limit) (firstSquare.isoPullback.inv ≫
        secondComparison) (by
    ext coneIndex
    change ((baseChangeCone diagram cone firstStructure).π.app coneIndex ≫ pullback.fst firstStructure
      (diagram.map coneIndex.hom)) ≫ firstStructure =
      (firstSquare.isoPullback.inv ≫ secondComparison) ≫ secondStructure
    rw [baseChangeCone_π_app_fst, Category.assoc, secondSquare.w, ← Category.assoc,
      firstInverse_structure]
    exact pullback.condition)
  obtain ⟨secondStage, reverseApproximation, reverseApproximation_limit, reverseApproximation_structure⟩
    := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (baseChangeDiagram diagram secondStructure) (baseChangeDiagramStructure diagram secondStructure)
        firstStructure (baseChangeCone diagram cone secondStructure)
      (isLimitBaseChangeCone diagram cone secondStructure limit) (secondSquare.isoPullback.inv ≫
        firstComparison) (by
    ext coneIndex
    change ((baseChangeCone diagram cone secondStructure).π.app coneIndex ≫ pullback.fst secondStructure
      (diagram.map coneIndex.hom)) ≫ secondStructure =
      (secondSquare.isoPullback.inv ≫ firstComparison) ≫ firstStructure
    rw [baseChangeCone_π_app_fst, Category.assoc, firstSquare.w, ← Category.assoc,
      secondInverse_structure]
    exact pullback.condition)
  set commonStage := IsCofiltered.min firstStage secondStage with commonStage_def
  set toFirstStage : commonStage ⟶ firstStage := IsCofiltered.minToLeft firstStage secondStage with
    toFirstStage_def
  set toSecondStage : commonStage ⟶ secondStage := IsCofiltered.minToRight firstStage secondStage with
    toSecondStage_def
  have forwardApproximation_structure_eq : forwardApproximation ≫ secondStructure = pullback.fst
    firstStructure (diagram.map firstStage.hom) ≫ firstStructure := forwardApproximation_structure
  have reverseApproximation_structure_eq : reverseApproximation ≫ firstStructure = pullback.fst
    secondStructure (diagram.map secondStage.hom) ≫ secondStructure := reverseApproximation_structure
  set forwardCommon : (baseChangeDiagram diagram firstStructure).obj commonStage ⟶ (baseChangeDiagram
    diagram secondStructure).obj commonStage :=
    pullback.lift ((baseChangeDiagram diagram firstStructure).map toFirstStage ≫ forwardApproximation)
      (pullback.snd firstStructure (diagram.map commonStage.hom))
      (by rw [Category.assoc, forwardApproximation_structure_eq, baseChangeDiagram_map_fst_assoc]
          exact pullback.condition) with forwardCommon_def
  set reverseCommon : (baseChangeDiagram diagram secondStructure).obj commonStage ⟶ (baseChangeDiagram
    diagram firstStructure).obj commonStage :=
    pullback.lift ((baseChangeDiagram diagram secondStructure).map toSecondStage ≫ reverseApproximation)
      (pullback.snd secondStructure (diagram.map commonStage.hom))
      (by rw [Category.assoc, reverseApproximation_structure_eq, baseChangeDiagram_map_fst_assoc]
          exact pullback.condition) with reverseCommon_def
  have forwardCommon_fst : forwardCommon ≫ pullback.fst secondStructure (diagram.map commonStage.hom) =
    (baseChangeDiagram diagram firstStructure).map toFirstStage ≫ forwardApproximation :=
    pullback.lift_fst ..
  have forwardCommon_snd : forwardCommon ≫ pullback.snd secondStructure (diagram.map commonStage.hom) =
    pullback.snd firstStructure (diagram.map commonStage.hom) :=
    pullback.lift_snd ..
  have reverseCommon_fst : reverseCommon ≫ pullback.fst firstStructure (diagram.map commonStage.hom) =
    (baseChangeDiagram diagram secondStructure).map toSecondStage ≫ reverseApproximation :=
    pullback.lift_fst ..
  have reverseCommon_snd : reverseCommon ≫ pullback.snd firstStructure (diagram.map commonStage.hom) =
    pullback.snd secondStructure (diagram.map commonStage.hom) :=
    pullback.lift_snd ..
  have forwardCommon_limit : (baseChangeCone diagram cone firstStructure).π.app commonStage ≫
    forwardCommon =
      firstSquare.isoPullback.inv ≫ secondSquare.isoPullback.hom ≫ (baseChangeCone diagram cone
        secondStructure).π.app commonStage := by
    apply pullback.hom_ext
    · rw [Category.assoc, forwardCommon_fst, ← Category.assoc, (baseChangeCone diagram cone
      firstStructure).w toFirstStage, forwardApproximation_limit,
        Category.assoc, Category.assoc, baseChangeCone_π_app_fst, secondComparison_fst]
    · rw [Category.assoc, forwardCommon_snd, baseChangeCone_π_app_snd, Category.assoc, Category.assoc,
        baseChangeCone_π_app_snd, ← Category.assoc secondSquare.isoPullback.hom, secondComparison_snd,
        ← Category.assoc, firstInverse_structure]
  have reverseCommon_limit : (baseChangeCone diagram cone secondStructure).π.app commonStage ≫
    reverseCommon =
      secondSquare.isoPullback.inv ≫ firstSquare.isoPullback.hom ≫ (baseChangeCone diagram cone
        firstStructure).π.app commonStage := by
    apply pullback.hom_ext
    · rw [Category.assoc, reverseCommon_fst, ← Category.assoc, (baseChangeCone diagram cone
      secondStructure).w toSecondStage, reverseApproximation_limit,
        Category.assoc, Category.assoc, baseChangeCone_π_app_fst, firstComparison_fst]
    · rw [Category.assoc, reverseCommon_snd, baseChangeCone_π_app_snd, Category.assoc, Category.assoc,
        baseChangeCone_π_app_snd, ← Category.assoc firstSquare.isoPullback.hom, firstComparison_snd,
        ← Category.assoc, secondInverse_structure]
  have forwardReverse_limit : (baseChangeCone diagram cone firstStructure).π.app commonStage ≫
    forwardCommon ≫ reverseCommon = (baseChangeCone diagram cone firstStructure).π.app commonStage := by
    rw [← Category.assoc, forwardCommon_limit, Category.assoc, Category.assoc, reverseCommon_limit,
      Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_assoc]
  have reverseForward_limit : (baseChangeCone diagram cone secondStructure).π.app commonStage ≫
    reverseCommon ≫ forwardCommon = (baseChangeCone diagram cone secondStructure).π.app commonStage := by
    rw [← Category.assoc, reverseCommon_limit, Category.assoc, Category.assoc, forwardCommon_limit,
      Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_assoc]
  obtain ⟨firstIdentityStage, firstIdentityTransition, firstIdentity⟩ :=
    Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (baseChangeDiagram diagram firstStructure) (baseChangeDiagramStructure diagram firstStructure)
        firstStructure (baseChangeCone diagram cone firstStructure)
      (isLimitBaseChangeCone diagram cone firstStructure limit)
      (forwardCommon ≫ reverseCommon ≫ pullback.fst firstStructure (diagram.map commonStage.hom))
        (pullback.fst firstStructure (diagram.map commonStage.hom))
      (by
        change pullback.fst firstStructure (diagram.map commonStage.hom) ≫ firstStructure = _
        rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc reverseCommon,
          reverseCommon_snd,
          ← Category.assoc, forwardCommon_snd, ← pullback.condition])
      rfl
      (by
        have projectionEquality := congrArg (· ≫ pullback.fst firstStructure (diagram.map
          commonStage.hom)) forwardReverse_limit
        simp only [Category.assoc] at projectionEquality ⊢
        exact projectionEquality)
  obtain ⟨secondIdentityStage, secondIdentityTransition, secondIdentity⟩ :=
    Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (baseChangeDiagram diagram secondStructure) (baseChangeDiagramStructure diagram secondStructure)
        secondStructure (baseChangeCone diagram cone secondStructure)
      (isLimitBaseChangeCone diagram cone secondStructure limit)
      (reverseCommon ≫ forwardCommon ≫ pullback.fst secondStructure (diagram.map commonStage.hom))
        (pullback.fst secondStructure (diagram.map commonStage.hom))
      (by
        change pullback.fst secondStructure (diagram.map commonStage.hom) ≫ secondStructure = _
        rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc forwardCommon,
          forwardCommon_snd,
          ← Category.assoc, reverseCommon_snd, ← pullback.condition])
      rfl
      (by
        have projectionEquality := congrArg (· ≫ pullback.fst secondStructure (diagram.map
          commonStage.hom)) reverseForward_limit
        simp only [Category.assoc] at projectionEquality ⊢
        exact projectionEquality)
  obtain ⟨finalStage, equalizerTransition, equalizer_condition⟩ := IsCofilteredOrEmpty.cone_maps
    (IsCofiltered.minToLeft firstIdentityStage secondIdentityStage ≫ firstIdentityTransition)
      (IsCofiltered.minToRight firstIdentityStage secondIdentityStage ≫ secondIdentityTransition)
  obtain ⟨finalTransition, finalTransition_left, finalTransition_right⟩ : ∃ finalTransition : finalStage
    ⟶ commonStage, finalTransition = (equalizerTransition ≫ IsCofiltered.minToLeft firstIdentityStage
    secondIdentityStage) ≫ firstIdentityTransition ∧
      finalTransition = (equalizerTransition ≫ IsCofiltered.minToRight firstIdentityStage
        secondIdentityStage) ≫ secondIdentityTransition :=
    ⟨_, rfl, by rw [Category.assoc, equalizer_condition, Category.assoc]⟩
  have forwardReverse_fst : (baseChangeDiagram diagram firstStructure).map finalTransition ≫
    forwardCommon ≫ reverseCommon ≫ pullback.fst firstStructure (diagram.map commonStage.hom) =
      (baseChangeDiagram diagram firstStructure).map finalTransition ≫ pullback.fst firstStructure
        (diagram.map commonStage.hom) := by
    rw [finalTransition_left]
    simp only [Functor.map_comp, Category.assoc]
    rw [firstIdentity]
  have reverseForward_fst : (baseChangeDiagram diagram secondStructure).map finalTransition ≫
    reverseCommon ≫ forwardCommon ≫ pullback.fst secondStructure (diagram.map commonStage.hom) =
      (baseChangeDiagram diagram secondStructure).map finalTransition ≫ pullback.fst secondStructure
        (diagram.map commonStage.hom) := by
    rw [finalTransition_right]
    simp only [Functor.map_comp, Category.assoc]
    rw [secondIdentity]
  set forwardFinal : (baseChangeDiagram diagram firstStructure).obj finalStage ⟶ (baseChangeDiagram
    diagram secondStructure).obj finalStage :=
    pullback.lift ((baseChangeDiagram diagram firstStructure).map finalTransition ≫ forwardCommon ≫
      pullback.fst secondStructure (diagram.map commonStage.hom))
      (pullback.snd firstStructure (diagram.map finalStage.hom))
      (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc forwardCommon,
        forwardCommon_snd,
            ← Category.assoc, baseChangeDiagram_map_snd, Category.assoc, ← diagram.map_comp,
            Over.w finalTransition]) with forwardFinal_def
  set reverseFinal : (baseChangeDiagram diagram secondStructure).obj finalStage ⟶ (baseChangeDiagram
    diagram firstStructure).obj finalStage :=
    pullback.lift ((baseChangeDiagram diagram secondStructure).map finalTransition ≫ reverseCommon ≫
      pullback.fst firstStructure (diagram.map commonStage.hom))
      (pullback.snd secondStructure (diagram.map finalStage.hom))
      (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc reverseCommon,
        reverseCommon_snd,
            ← Category.assoc, baseChangeDiagram_map_snd, Category.assoc, ← diagram.map_comp,
            Over.w finalTransition]) with reverseFinal_def
  have forwardFinal_fst : forwardFinal ≫ pullback.fst secondStructure (diagram.map finalStage.hom) =
      (baseChangeDiagram diagram firstStructure).map finalTransition ≫ forwardCommon ≫ pullback.fst
        secondStructure (diagram.map commonStage.hom) := pullback.lift_fst ..
  have forwardFinal_snd : forwardFinal ≫ pullback.snd secondStructure (diagram.map finalStage.hom) =
    pullback.snd firstStructure (diagram.map finalStage.hom) :=
    pullback.lift_snd ..
  have reverseFinal_fst : reverseFinal ≫ pullback.fst firstStructure (diagram.map finalStage.hom) =
      (baseChangeDiagram diagram secondStructure).map finalTransition ≫ reverseCommon ≫ pullback.fst
        firstStructure (diagram.map commonStage.hom) := pullback.lift_fst ..
  have reverseFinal_snd : reverseFinal ≫ pullback.snd firstStructure (diagram.map finalStage.hom) =
    pullback.snd secondStructure (diagram.map finalStage.hom) :=
    pullback.lift_snd ..
  have forwardFinal_naturality : forwardFinal ≫ (baseChangeDiagram diagram secondStructure).map
    finalTransition = (baseChangeDiagram diagram firstStructure).map finalTransition ≫ forwardCommon
    := by
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeDiagram_map_fst, forwardFinal_fst, Category.assoc]
    · rw [Category.assoc, baseChangeDiagram_map_snd, ← Category.assoc, forwardFinal_snd,
        Category.assoc, forwardCommon_snd, baseChangeDiagram_map_snd]
  have reverseFinal_naturality : reverseFinal ≫ (baseChangeDiagram diagram firstStructure).map
    finalTransition = (baseChangeDiagram diagram secondStructure).map finalTransition ≫ reverseCommon
    := by
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeDiagram_map_fst, reverseFinal_fst, Category.assoc]
    · rw [Category.assoc, baseChangeDiagram_map_snd, ← Category.assoc, reverseFinal_snd,
        Category.assoc, reverseCommon_snd, baseChangeDiagram_map_snd]
  have forward_reverse : forwardFinal ≫ reverseFinal = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, reverseFinal_fst, ← Category.assoc, forwardFinal_naturality]
      simp only [Category.assoc]
      rw [forwardReverse_fst, baseChangeDiagram_map_fst, Category.id_comp]
    · rw [Category.assoc, reverseFinal_snd, forwardFinal_snd, Category.id_comp]
  have reverse_forward : reverseFinal ≫ forwardFinal = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, forwardFinal_fst, ← Category.assoc, reverseFinal_naturality]
      simp only [Category.assoc]
      rw [reverseForward_fst, baseChangeDiagram_map_fst, Category.id_comp]
    · rw [Category.assoc, forwardFinal_snd, reverseFinal_snd, Category.id_comp]
  have forwardCommon_limit_fst : (baseChangeCone diagram cone firstStructure).π.app commonStage ≫
    forwardCommon ≫ pullback.fst secondStructure (diagram.map commonStage.hom) =
      firstSquare.isoPullback.inv ≫ secondComparison := by
    rw [← Category.assoc, forwardCommon_limit, Category.assoc, Category.assoc, baseChangeCone_π_app_fst,
      secondComparison_fst]
  have forwardFinal_limit : (firstSquare.isoPullback.hom ≫ (baseChangeCone diagram cone
    firstStructure).π.app finalStage) ≫ forwardFinal =
      secondSquare.isoPullback.hom ≫ (baseChangeCone diagram cone secondStructure).π.app finalStage := by
    apply pullback.hom_ext
    · have forwardFinal_limit_fst : ((firstSquare.isoPullback.hom ≫ (baseChangeCone diagram cone
      firstStructure).π.app finalStage) ≫ forwardFinal) ≫
          pullback.fst secondStructure (diagram.map finalStage.hom) = secondComparison := by
        simp only [Category.assoc, forwardFinal_fst]
        rw [← Category.assoc ((baseChangeCone diagram cone firstStructure).π.app finalStage),
          (baseChangeCone diagram cone firstStructure).w finalTransition,
          forwardCommon_limit_fst, Iso.hom_inv_id_assoc]
      have secondFinal_limit_fst : (secondSquare.isoPullback.hom ≫ (baseChangeCone diagram cone
        secondStructure).π.app finalStage) ≫
          pullback.fst secondStructure (diagram.map finalStage.hom) = secondComparison := by
        rw [Category.assoc, baseChangeCone_π_app_fst, secondComparison_fst]
      rw [forwardFinal_limit_fst, secondFinal_limit_fst]
    · rw [Category.assoc, Category.assoc, forwardFinal_snd, baseChangeCone_π_app_snd, ← Category.assoc,
        firstComparison_snd, Category.assoc, baseChangeCone_π_app_snd, ← Category.assoc,
          secondComparison_snd]
  refine ⟨finalStage.left, finalStage.hom, ?_⟩
  intro firstLaterModel secondLaterModel firstLaterStructure firstLaterProjection secondLaterStructure
    secondLaterProjection firstLaterComparison secondLaterComparison firstLaterSquare
    firstLaterComparison_projection firstLaterComparison_structure secondLaterSquare
    secondLaterComparison_projection secondLaterComparison_structure
  have firstLaterSquare_fst : firstLaterSquare.isoPullback.hom ≫ pullback.fst firstStructure (diagram.map
    finalStage.hom) = firstLaterProjection :=
    IsPullback.isoPullback_hom_fst _
  have firstLaterSquare_snd : firstLaterSquare.isoPullback.hom ≫ pullback.snd firstStructure (diagram.map
    finalStage.hom) = firstLaterStructure :=
    IsPullback.isoPullback_hom_snd _
  have secondLaterSquare_fst : secondLaterSquare.isoPullback.hom ≫ pullback.fst secondStructure
    (diagram.map finalStage.hom) = secondLaterProjection :=
    IsPullback.isoPullback_hom_fst _
  have secondLaterSquare_snd : secondLaterSquare.isoPullback.hom ≫ pullback.snd secondStructure
    (diagram.map finalStage.hom) = secondLaterStructure :=
    IsPullback.isoPullback_hom_snd _
  have firstLaterComparison_identification : firstLaterComparison ≫ firstLaterSquare.isoPullback.hom =
      firstSquare.isoPullback.hom ≫ (baseChangeCone diagram cone firstStructure).π.app finalStage := by
    apply pullback.hom_ext
    · rw [Category.assoc, firstLaterSquare_fst, firstLaterComparison_projection, Category.assoc,
      baseChangeCone_π_app_fst, firstComparison_fst]
    · rw [Category.assoc, firstLaterSquare_snd, firstLaterComparison_structure, Category.assoc,
      baseChangeCone_π_app_snd,
        ← Category.assoc, firstComparison_snd]
  have secondLaterComparison_identification : secondLaterComparison ≫ secondLaterSquare.isoPullback.hom =
      secondSquare.isoPullback.hom ≫ (baseChangeCone diagram cone secondStructure).π.app finalStage := by
    apply pullback.hom_ext
    · rw [Category.assoc, secondLaterSquare_fst, secondLaterComparison_projection, Category.assoc,
      baseChangeCone_π_app_fst, secondComparison_fst]
    · rw [Category.assoc, secondLaterSquare_snd, secondLaterComparison_structure, Category.assoc,
      baseChangeCone_π_app_snd,
        ← Category.assoc, secondComparison_snd]
  refine ⟨firstLaterSquare.isoPullback ≪≫ ⟨forwardFinal, reverseFinal, forward_reverse, reverse_forward⟩
    ≪≫ secondLaterSquare.isoPullback.symm, ?_, ?_⟩
  · change firstLaterSquare.isoPullback.hom ≫ forwardFinal ≫ secondLaterSquare.isoPullback.inv ≫
    secondLaterStructure = firstLaterStructure
    rw [show secondLaterSquare.isoPullback.inv ≫ secondLaterStructure = pullback.snd secondStructure
      (diagram.map finalStage.hom) by
      rw [Iso.inv_comp_eq, secondLaterSquare_snd], forwardFinal_snd, firstLaterSquare_snd]
  · change firstLaterComparison ≫ firstLaterSquare.isoPullback.hom ≫ forwardFinal ≫
    secondLaterSquare.isoPullback.inv = secondLaterComparison
    rw [← Category.assoc, ← Category.assoc, firstLaterComparison_identification, forwardFinal_limit, ←
      secondLaterComparison_identification, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry
