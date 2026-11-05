import Jacobian.AlgebraicGeometry.Modules.Limits.Hom
import Jacobian.CategoryTheory.Sites.Descent.PullHom

/-!
# Simultaneous descent of finitely many coefficient morphisms

Finitely many morphisms on directed affine inverse limits descend to a common
stage. Finitely many equalities of morphisms are detected at a common stage.
The comparison of lifted maps uses the native pseudofunctor of module pullback,
so it is compatible with restriction to pair and triple intersections.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

private lemma pullHom_eq_pullbackCompOfEq
    {source middle firstTarget secondTarget : Scheme.{schemeUniverse}}
    {sourceModule : firstTarget.Modules} {targetModule : secondTarget.Modules}
    {firstMap : middle ⟶ firstTarget} {secondMap : middle ⟶ secondTarget}
    (coefficientMap : (pullback firstMap).obj sourceModule ⟶
      (pullback secondMap).obj targetModule)
    (morphism : source ⟶ middle) (firstComposite : source ⟶ firstTarget)
    (secondComposite : source ⟶ secondTarget)
    (firstFactorization : morphism ≫ firstMap = firstComposite)
    (secondFactorization : morphism ≫ secondMap = secondComposite) :
    pullHom (F := modulesPseudofunctor) coefficientMap morphism firstComposite
        secondComposite firstFactorization secondFactorization =
      (pullbackCompOfEq morphism firstMap firstComposite firstFactorization sourceModule).inv ≫
        (pullback morphism).map coefficientMap ≫
          (pullbackCompOfEq morphism secondMap secondComposite secondFactorization
            targetModule).hom := by
  subst firstComposite
  subst secondComposite
  simpa [pullbackCompOfEq, pullbackCongr] using
    modulesPseudofunctor_pullHom_eq coefficientMap morphism

private theorem exists_hom_pullHom_eq_of_affine_limit
    {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] (diagram : Indexᵒᵖ ⥤ Scheme.{schemeUniverse})
    [∀ stageIndex, IsAffine (diagram.obj stageIndex)]
    (cone : Cone diagram) (limit : IsLimit cone) [IsAffine cone.pt]
    (initialIndex : Index) (sourceModule targetModule : (diagram.obj (op initialIndex)).Modules)
    [sourceModule.IsFinitePresentation] [sourceModule.IsQuasicoherent]
    [targetModule.IsQuasicoherent]
    (coefficientMap : (pullback (cone.π.app (op initialIndex))).obj sourceModule ⟶
      (pullback (cone.π.app (op initialIndex))).obj targetModule) :
    ∃ (stageIndex : Index) (initialLe : initialIndex ≤ stageIndex)
      (stageMap : (pullback (diagram.map (homOfLE initialLe).op)).obj sourceModule ⟶
        (pullback (diagram.map (homOfLE initialLe).op)).obj targetModule),
      pullHom (F := modulesPseudofunctor) stageMap (cone.π.app (op stageIndex))
        (cone.π.app (op initialIndex)) (cone.π.app (op initialIndex))
        (cone.w (homOfLE initialLe).op) (cone.w (homOfLE initialLe).op) = coefficientMap := by
  obtain ⟨stageIndex, initialLe, stageMap, square⟩ :=
    exists_hom_of_affine_limit diagram cone limit initialIndex sourceModule targetModule
      coefficientMap
  refine ⟨stageIndex, initialLe, stageMap, ?_⟩
  rw [pullHom_eq_pullbackCompOfEq, square, Iso.inv_hom_id_assoc]

/-- A finite family of morphisms out of finitely presented coefficients on affine limits
descends to one common index. The maps at that index are constructed from the given limit
morphisms, with recovery expressed by coherent pullback of morphisms. -/
theorem exists_homs_of_affine_limits
    {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] {Label : Type schemeUniverse} [Finite Label]
    (diagrams : Label → Indexᵒᵖ ⥤ Scheme.{schemeUniverse})
    [∀ label stageIndex, IsAffine ((diagrams label).obj stageIndex)]
    (cones : ∀ label, Cone (diagrams label))
    (limits : ∀ label, IsLimit (cones label)) [∀ label, IsAffine (cones label).pt]
    (initialIndex : Index)
    (sourceModules targetModules : ∀ label, ((diagrams label).obj (op initialIndex)).Modules)
    [∀ label, (sourceModules label).IsFinitePresentation]
    [∀ label, (sourceModules label).IsQuasicoherent]
    [∀ label, (targetModules label).IsQuasicoherent]
    (coefficientMaps : ∀ label,
      (pullback ((cones label).π.app (op initialIndex))).obj (sourceModules label) ⟶
        (pullback ((cones label).π.app (op initialIndex))).obj (targetModules label)) :
    ∃ (stageIndex : Index) (initialLe : initialIndex ≤ stageIndex)
      (stageMaps : ∀ label,
        (pullback ((diagrams label).map (homOfLE initialLe).op)).obj (sourceModules label) ⟶
          (pullback ((diagrams label).map (homOfLE initialLe).op)).obj (targetModules label)),
      ∀ label, pullHom (F := modulesPseudofunctor) (stageMaps label)
        ((cones label).π.app (op stageIndex)) ((cones label).π.app (op initialIndex))
        ((cones label).π.app (op initialIndex))
        ((cones label).w (homOfLE initialLe).op)
        ((cones label).w (homOfLE initialLe).op) = coefficientMaps label := by
  classical
  letI : Fintype Label := Fintype.ofFinite Label
  have individualLifts (label : Label) :=
    exists_hom_pullHom_eq_of_affine_limit (diagrams label) (cones label) (limits label)
      initialIndex (sourceModules label) (targetModules label) (coefficientMaps label)
  choose localIndex initialLeLocal localMap localRecovery using individualLifts
  obtain ⟨stageIndex, stageBound⟩ :=
    (insert initialIndex (Finset.univ.image localIndex)).exists_le
  have initialLe : initialIndex ≤ stageIndex :=
    stageBound initialIndex (Finset.mem_insert_self _ _)
  have localLe (label : Label) : localIndex label ≤ stageIndex :=
    stageBound (localIndex label)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨label, Finset.mem_univ label, rfl⟩))
  have factorization (label : Label) :
      (diagrams label).map (homOfLE (localLe label)).op ≫
          (diagrams label).map (homOfLE (initialLeLocal label)).op =
        (diagrams label).map (homOfLE initialLe).op := by
    rw [← Functor.map_comp]
    rfl
  let stageMaps (label : Label) :=
    pullHom (F := modulesPseudofunctor) (localMap label)
      ((diagrams label).map (homOfLE (localLe label)).op)
      ((diagrams label).map (homOfLE initialLe).op)
      ((diagrams label).map (homOfLE initialLe).op)
      (factorization label) (factorization label)
  refine ⟨stageIndex, initialLe, stageMaps, ?_⟩
  intro label
  dsimp only [stageMaps]
  rw [pullHom_pullHom]
  have projectionCompatibility :
      (cones label).π.app (op stageIndex) ≫
          (diagrams label).map (homOfLE (localLe label)).op =
        (cones label).π.app (op (localIndex label)) :=
    (cones label).w (homOfLE (localLe label)).op
  simpa only [projectionCompatibility] using localRecovery label

/-- Finitely many equalities between coefficient morphisms on affine limits hold at one
common stage. This applies to the diagonal and triple-overlap equations of a finite cover. -/
theorem exists_hom_eqs_of_affine_limits
    {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] {Label : Type schemeUniverse} [Finite Label]
    (diagrams : Label → Indexᵒᵖ ⥤ Scheme.{schemeUniverse})
    [∀ label stageIndex, IsAffine ((diagrams label).obj stageIndex)]
    (cones : ∀ label, Cone (diagrams label))
    (limits : ∀ label, IsLimit (cones label)) [∀ label, IsAffine (cones label).pt]
    (initialIndex : Index)
    (sourceModules targetModules : ∀ label, ((diagrams label).obj (op initialIndex)).Modules)
    [∀ label, (sourceModules label).IsFinitePresentation]
    [∀ label, (sourceModules label).IsQuasicoherent]
    [∀ label, (targetModules label).IsQuasicoherent]
    (firstMaps secondMaps : ∀ label, sourceModules label ⟶ targetModules label)
    (equalities : ∀ label,
      (pullback ((cones label).π.app (op initialIndex))).map (firstMaps label) =
        (pullback ((cones label).π.app (op initialIndex))).map (secondMaps label)) :
    ∃ (stageIndex : Index) (initialLe : initialIndex ≤ stageIndex), ∀ label,
      (pullback ((diagrams label).map (homOfLE initialLe).op)).map (firstMaps label) =
        (pullback ((diagrams label).map (homOfLE initialLe).op)).map (secondMaps label) := by
  classical
  letI : Fintype Label := Fintype.ofFinite Label
  have individualEqualities (label : Label) :=
    exists_hom_eq_of_affine_limit (diagrams label) (cones label) (limits label)
      initialIndex (firstMaps label) (secondMaps label) (equalities label)
  choose localIndex initialLeLocal localEquality using individualEqualities
  obtain ⟨stageIndex, stageBound⟩ :=
    (insert initialIndex (Finset.univ.image localIndex)).exists_le
  have initialLe : initialIndex ≤ stageIndex :=
    stageBound initialIndex (Finset.mem_insert_self _ _)
  have localLe (label : Label) : localIndex label ≤ stageIndex :=
    stageBound (localIndex label)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨label, Finset.mem_univ label, rfl⟩))
  refine ⟨stageIndex, initialLe, ?_⟩
  intro label
  let firstTransition : (diagrams label).obj (op (localIndex label)) ⟶
      (diagrams label).obj (op initialIndex) :=
    (diagrams label).map (homOfLE (initialLeLocal label)).op
  let secondTransition : (diagrams label).obj (op stageIndex) ⟶
      (diagrams label).obj (op (localIndex label)) :=
    (diagrams label).map (homOfLE (localLe label)).op
  let composite : (diagrams label).obj (op stageIndex) ⟶
      (diagrams label).obj (op initialIndex) :=
    (diagrams label).map (homOfLE initialLe).op
  have factorization : secondTransition ≫ firstTransition = composite := by
    dsimp only [firstTransition, secondTransition, composite]
    rw [← Functor.map_comp]
    rfl
  let comparison : pullback composite ≅ pullback firstTransition ⋙ pullback secondTransition :=
    (pullbackCongr factorization.symm) ≪≫ (pullbackComp secondTransition firstTransition).symm
  have iteratedEquality :
      (pullback firstTransition ⋙ pullback secondTransition).map (firstMaps label) =
        (pullback firstTransition ⋙ pullback secondTransition).map (secondMaps label) :=
    congrArg (pullback secondTransition).map (localEquality label)
  apply (cancel_mono (comparison.hom.app (targetModules label))).mp
  rw [comparison.hom.naturality, comparison.hom.naturality, iteratedEquality]

end AlgebraicGeometry.Scheme.Modules
