import Jacobian.AlgebraicGeometry.Modules.Limits.FiniteMaps
import Jacobian.AlgebraicGeometry.Modules.Limits.Gluing

/-!
# Descent of overlap morphisms on affine inverse limits

Affine coefficient morphism descent is compatible with maps to two different
coefficient schemes. Recovery and eventual equality are expressed by the native
coherent pullback of morphisms, as required on double and triple overlaps.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

open Gluing

private theorem pullHom_mapComp_conj_recovers
    ⦃firstScheme secondScheme firstBase secondBase : Scheme.{schemeUniverse}⦄ ⦃firstModule : modulesPseudofunctor.obj (.mk (op firstScheme))⦄
    ⦃secondModule : modulesPseudofunctor.obj (.mk (op secondScheme))⦄ (firstChange : firstBase ⟶ firstScheme) (secondChange : secondBase ⟶ secondScheme)
    ⦃testScheme : Scheme.{schemeUniverse}⦄ (firstProjection : testScheme ⟶ firstBase) (secondProjection : testScheme ⟶ secondBase)
    (firstComposite : testScheme ⟶ firstScheme) (secondComposite : testScheme ⟶ secondScheme)
    (hx₁ : firstProjection ≫ firstChange = firstComposite) (hx₂ : secondProjection ≫ secondChange = secondComposite)
    (stageMap : (modulesPseudofunctor.map firstProjection.op.toLoc).toFunctor.obj ((modulesPseudofunctor.map firstChange.op.toLoc).toFunctor.obj firstModule) ⟶
      (modulesPseudofunctor.map secondProjection.op.toLoc).toFunctor.obj ((modulesPseudofunctor.map secondChange.op.toLoc).toFunctor.obj secondModule))
    ⦃furtherScheme : Scheme.{schemeUniverse}⦄ (testLift : furtherScheme ⟶ testScheme) (firstLift : furtherScheme ⟶ firstBase) (secondLift : furtherScheme ⟶ secondBase)
    (hz₁ : testLift ≫ firstProjection = firstLift) (hz₂ : testLift ≫ secondProjection = secondLift)
    (firstFurtherComposite : furtherScheme ⟶ firstScheme) (secondFurtherComposite : furtherScheme ⟶ secondScheme)
    (hy₁ : firstLift ≫ firstChange = firstFurtherComposite) (hy₂ : secondLift ≫ secondChange = secondFurtherComposite)
    (coefficientMap : (modulesPseudofunctor.map firstFurtherComposite.op.toLoc).toFunctor.obj firstModule ⟶
      (modulesPseudofunctor.map secondFurtherComposite.op.toLoc).toFunctor.obj secondModule)
    (hψ : pullHom stageMap testLift firstLift secondLift hz₁ hz₂ =
      (modulesPseudofunctor.mapComp' firstChange.op.toLoc firstLift.op.toLoc firstFurtherComposite.op.toLoc
        (op_toLoc_comp_eq hy₁)).inv.toNatTrans.app firstModule ≫ coefficientMap ≫
      (modulesPseudofunctor.mapComp' secondChange.op.toLoc secondLift.op.toLoc secondFurtherComposite.op.toLoc
        (op_toLoc_comp_eq hy₂)).hom.toNatTrans.app secondModule) :
    pullHom ((modulesPseudofunctor.mapComp' firstChange.op.toLoc firstProjection.op.toLoc firstComposite.op.toLoc
        (op_toLoc_comp_eq hx₁)).hom.toNatTrans.app firstModule ≫ stageMap ≫
      (modulesPseudofunctor.mapComp' secondChange.op.toLoc secondProjection.op.toLoc secondComposite.op.toLoc
        (op_toLoc_comp_eq hx₂)).inv.toNatTrans.app secondModule) testLift firstFurtherComposite secondFurtherComposite
      (by rw [← hy₁, ← hx₁, ← hz₁, Category.assoc])
      (by rw [← hy₂, ← hx₂, ← hz₂, Category.assoc]) = coefficientMap := by
  rw [pullHom_mapComp'_conj_symm firstChange secondChange firstProjection secondProjection firstComposite secondComposite hx₁ hx₂ stageMap
    testLift firstLift secondLift hz₁ hz₂ firstFurtherComposite secondFurtherComposite hy₁ hy₂, hψ]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
    Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]

section AffineLimits

variable {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
  [IsDirected Index (· ≤ ·)] {diagram : Indexᵒᵖ ⥤ Scheme.{schemeUniverse}}
  [∀ stageIndex, IsAffine (diagram.obj stageIndex)] {cone : Cone diagram}

/-- A map between two pulled-back finitely presented coefficients descends on an affine limit. -/
theorem exists_pullHom_of_affine_limit (limit : IsLimit cone)
    {initialIndex : Indexᵒᵖ} {firstScheme secondScheme : Scheme.{schemeUniverse}}
    {firstModule : firstScheme.Modules} {secondModule : secondScheme.Modules}
    [firstModule.IsFinitePresentation] [secondModule.IsFinitePresentation]
    (firstMap : diagram.obj initialIndex ⟶ firstScheme)
    (secondMap : diagram.obj initialIndex ⟶ secondScheme)
    {firstLimitMap : cone.pt ⟶ firstScheme} {secondLimitMap : cone.pt ⟶ secondScheme}
    (firstFactorization : cone.π.app initialIndex ≫ firstMap = firstLimitMap)
    (secondFactorization : cone.π.app initialIndex ≫ secondMap = secondLimitMap)
    (coefficientMap : (pullback firstLimitMap).obj firstModule ⟶
      (pullback secondLimitMap).obj secondModule) :
    ∃ (stageIndex : Indexᵒᵖ) (transition : stageIndex ⟶ initialIndex)
      (stageMap : (pullback (diagram.map transition ≫ firstMap)).obj firstModule ⟶
        (pullback (diagram.map transition ≫ secondMap)).obj secondModule),
      pullHom (F := modulesPseudofunctor) stageMap (cone.π.app stageIndex)
        firstLimitMap secondLimitMap (by rw [← firstFactorization, cone.w_assoc])
        (by rw [← secondFactorization, cone.w_assoc]) = coefficientMap := by
  letI : IsAffine cone.pt := Scheme.isAffine_of_isLimit _ limit
  let sourceModule := (pullback firstMap).obj firstModule
  let targetModule := (pullback secondMap).obj secondModule
  letI : sourceModule.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData sourceModule).choose.isQuasicoherent
  letI : targetModule.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData targetModule).choose.isQuasicoherent
  let conjugateMap : (pullback (cone.π.app initialIndex)).obj sourceModule ⟶
      (pullback (cone.π.app initialIndex)).obj targetModule :=
    (modulesPseudofunctor.mapComp' firstMap.op.toLoc (cone.π.app initialIndex).op.toLoc
      firstLimitMap.op.toLoc (op_toLoc_comp_eq firstFactorization)).inv.toNatTrans.app
        firstModule ≫ coefficientMap ≫
    (modulesPseudofunctor.mapComp' secondMap.op.toLoc (cone.π.app initialIndex).op.toLoc
      secondLimitMap.op.toLoc (op_toLoc_comp_eq secondFactorization)).hom.toNatTrans.app
        secondModule
  obtain ⟨stageIndex, initialLe, stageMaps, recovery⟩ :=
    exists_homs_of_affine_limits (Label := PUnit.{schemeUniverse + 1})
      (fun _ ↦ diagram) (fun _ ↦ cone) (fun _ ↦ limit) initialIndex.unop
      (fun _ ↦ sourceModule) (fun _ ↦ targetModule) (fun _ ↦ conjugateMap)
  let transition : op stageIndex ⟶ initialIndex := (homOfLE initialLe).op
  let stageMap := stageMaps PUnit.unit
  refine ⟨op stageIndex, transition,
    (modulesPseudofunctor.mapComp' firstMap.op.toLoc (diagram.map transition).op.toLoc
      (diagram.map transition ≫ firstMap).op.toLoc (op_toLoc_comp_eq rfl)).hom.toNatTrans.app
        firstModule ≫ stageMap ≫
    (modulesPseudofunctor.mapComp' secondMap.op.toLoc (diagram.map transition).op.toLoc
      (diagram.map transition ≫ secondMap).op.toLoc (op_toLoc_comp_eq rfl)).inv.toNatTrans.app
        secondModule, ?_⟩
  exact pullHom_mapComp_conj_recovers firstMap secondMap (diagram.map transition)
    (diagram.map transition) (diagram.map transition ≫ firstMap)
    (diagram.map transition ≫ secondMap) rfl rfl stageMap (cone.π.app (op stageIndex))
    (cone.π.app initialIndex) (cone.π.app initialIndex) (cone.w transition)
    (cone.w transition) firstLimitMap secondLimitMap firstFactorization secondFactorization
    coefficientMap (recovery PUnit.unit)

/-- An equality between overlap morphisms is detected at a finite affine stage. -/
theorem exists_pullHom_eq_of_affine_limit (limit : IsLimit cone)
    {initialIndex : Indexᵒᵖ} {firstScheme secondScheme : Scheme.{schemeUniverse}}
    {firstModule : firstScheme.Modules} {secondModule : secondScheme.Modules}
    [firstModule.IsFinitePresentation] [secondModule.IsFinitePresentation]
    (firstMap : diagram.obj initialIndex ⟶ firstScheme)
    (secondMap : diagram.obj initialIndex ⟶ secondScheme)
    {firstLimitMap : cone.pt ⟶ firstScheme} {secondLimitMap : cone.pt ⟶ secondScheme}
    (firstFactorization : cone.π.app initialIndex ≫ firstMap = firstLimitMap)
    (secondFactorization : cone.π.app initialIndex ≫ secondMap = secondLimitMap)
    (firstCoefficientMap secondCoefficientMap : (pullback firstMap).obj firstModule ⟶
      (pullback secondMap).obj secondModule)
    (equality : pullHom (F := modulesPseudofunctor) firstCoefficientMap
      (cone.π.app initialIndex) firstLimitMap secondLimitMap firstFactorization
        secondFactorization =
      pullHom secondCoefficientMap (cone.π.app initialIndex) firstLimitMap
        secondLimitMap firstFactorization secondFactorization) :
    ∃ (stageIndex : Indexᵒᵖ) (transition : stageIndex ⟶ initialIndex),
      pullHom (F := modulesPseudofunctor) (M₁ := firstModule) (M₂ := secondModule)
        firstCoefficientMap (diagram.map transition)
        (diagram.map transition ≫ firstMap) (diagram.map transition ≫ secondMap) rfl rfl =
      pullHom (F := modulesPseudofunctor) (M₁ := firstModule) (M₂ := secondModule)
        secondCoefficientMap (diagram.map transition)
        (diagram.map transition ≫ firstMap) (diagram.map transition ≫ secondMap) rfl rfl := by
  letI : IsAffine cone.pt := Scheme.isAffine_of_isLimit _ limit
  let sourceModule := (pullback firstMap).obj firstModule
  let targetModule := (pullback secondMap).obj secondModule
  letI : sourceModule.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData sourceModule).choose.isQuasicoherent
  letI : targetModule.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData targetModule).choose.isQuasicoherent
  obtain ⟨stageIndex, initialLe, stageEquality⟩ :=
    exists_hom_eq_of_affine_limit diagram cone limit initialIndex.unop
      firstCoefficientMap secondCoefficientMap
      (map_eq_map_of_pullHom_eq _ _ _ firstFactorization secondFactorization equality)
  exact ⟨op stageIndex, (homOfLE initialLe).op,
    pullHom_eq_pullHom_of_map_eq _ _ _ rfl rfl stageEquality⟩

/-- Eventual equality with an explicitly identified cone projection. -/
theorem exists_pullHom_eq_of_affine_limit_of_projection_eq (limit : IsLimit cone)
    {initialIndex : Indexᵒᵖ} {firstScheme secondScheme : Scheme.{schemeUniverse}}
    {firstModule : firstScheme.Modules} {secondModule : secondScheme.Modules}
    [firstModule.IsFinitePresentation] [secondModule.IsFinitePresentation]
    (firstMap : diagram.obj initialIndex ⟶ firstScheme)
    (secondMap : diagram.obj initialIndex ⟶ secondScheme)
    {firstLimitMap : cone.pt ⟶ firstScheme} {secondLimitMap : cone.pt ⟶ secondScheme}
    (projection : cone.pt ⟶ diagram.obj initialIndex)
    (projectionEquality : cone.π.app initialIndex = projection)
    (firstFactorization : projection ≫ firstMap = firstLimitMap)
    (secondFactorization : projection ≫ secondMap = secondLimitMap)
    (firstCoefficientMap secondCoefficientMap : (pullback firstMap).obj firstModule ⟶
      (pullback secondMap).obj secondModule)
    (equality : pullHom (F := modulesPseudofunctor) firstCoefficientMap
      projection firstLimitMap secondLimitMap firstFactorization secondFactorization =
      pullHom secondCoefficientMap projection firstLimitMap secondLimitMap
        firstFactorization secondFactorization) :
    ∃ (stageIndex : Indexᵒᵖ) (transition : stageIndex ⟶ initialIndex),
      pullHom (F := modulesPseudofunctor) (M₁ := firstModule) (M₂ := secondModule)
        firstCoefficientMap (diagram.map transition)
        (diagram.map transition ≫ firstMap) (diagram.map transition ≫ secondMap) rfl rfl =
      pullHom (F := modulesPseudofunctor) (M₁ := firstModule) (M₂ := secondModule)
        secondCoefficientMap (diagram.map transition)
        (diagram.map transition ≫ firstMap) (diagram.map transition ≫ secondMap) rfl rfl := by
  subst projection
  exact exists_pullHom_eq_of_affine_limit limit firstMap secondMap firstFactorization
    secondFactorization firstCoefficientMap secondCoefficientMap equality

end AffineLimits

end AlgebraicGeometry.Scheme.Modules
