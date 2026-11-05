import Jacobian.AlgebraicGeometry.Limits.BaseChange
import Jacobian.AlgebraicGeometry.Limits.ProperNoetherian
import Jacobian.AlgebraicGeometry.Modules.Limits.Flat
import Jacobian.AlgebraicGeometry.Modules.Limits.Objects
import Jacobian.AlgebraicGeometry.Modules.PullbackUnit

/-!
# Noetherian models with relatively flat coefficients

A proper finitely presented family over an affine scheme, together with a
finitely presented module flat over the base, descends to a proper family
over a Noetherian ring with relatively flat finitely presented coefficients.
The Cartesian square and the coefficient pullback isomorphism are constructed
simultaneously. On an arbitrary base this construction applies near every point.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

private def tailOverEquivalence {Index : Type u} [Preorder Index] (initialIndex : Index) :
    ({stageIndex : Index // initialIndex ≤ stageIndex})ᵒᵖ ≌ Over (Opposite.op initialIndex) where
  functor :=
    { obj := fun stageIndex ↦ Over.mk (homOfLE stageIndex.unop.property).op
      map := fun {sourceIndex targetIndex} transition ↦
        Over.homMk (homOfLE
          (show targetIndex.unop.val ≤ sourceIndex.unop.val from
            leOfHom transition.unop)).op (Subsingleton.elim _ _)
      map_id := fun _ ↦
        (Over.forget (Opposite.op initialIndex)).map_injective (Subsingleton.elim _ _)
      map_comp := fun _ _ ↦
        (Over.forget (Opposite.op initialIndex)).map_injective (Subsingleton.elim _ _) }
  inverse :=
    { obj := fun stageIndex ↦
        Opposite.op ⟨stageIndex.left.unop, leOfHom stageIndex.hom.unop⟩
      map := fun {sourceIndex targetIndex} transition ↦ (homOfLE (show
        (⟨targetIndex.left.unop, leOfHom targetIndex.hom.unop⟩ :
          {stageIndex : Index // initialIndex ≤ stageIndex}) ≤
        ⟨sourceIndex.left.unop, leOfHom sourceIndex.hom.unop⟩ from
          leOfHom transition.left.unop)).op
      map_id := fun _ ↦ Subsingleton.elim _ _
      map_comp := fun _ _ ↦ Subsingleton.elim _ _ }
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun _ ↦ Over.isoMk (Iso.refl _) (Subsingleton.elim _ _))
    (fun _ ↦
      (Over.forget (Opposite.op initialIndex)).map_injective (Subsingleton.elim _ _))
  functor_unitIso_comp := fun _ ↦
    (Over.forget (Opposite.op initialIndex)).map_injective (Subsingleton.elim _ _)

/-- A proper finitely presented family over an arbitrary affine scheme, with
finitely presented coefficients flat over its base, is the Cartesian pullback
of such a family and coefficients over a Noetherian ring. -/
theorem exists_isPullback_over_noetherian_of_isProper
    {sourceScheme baseScheme : Scheme.{u}} [IsAffine baseScheme]
    (sourceMap : sourceScheme ⟶ baseScheme) [IsProper sourceMap]
    [LocallyOfFinitePresentation sourceMap] (moduleSheaf : sourceScheme.Modules)
    [moduleSheaf.IsFinitePresentation] (flat : moduleSheaf.IsFlatOver sourceMap) :
    ∃ (stageRing : CommRingCat.{u}) (_ : IsNoetherianRing stageRing)
      (stageScheme : Scheme.{u}) (stageMap : stageScheme ⟶ Spec stageRing)
      (_ : IsProper stageMap) (_ : LocallyOfFinitePresentation stageMap)
      (stageModule : stageScheme.Modules) (_ : stageModule.IsFinitePresentation),
      stageModule.IsFlatOver stageMap ∧
        ∃ (comparison : sourceScheme ⟶ stageScheme)
          (baseComparison : baseScheme ⟶ Spec stageRing),
          IsPullback comparison sourceMap stageMap baseComparison ∧
            Nonempty ((pullback comparison).obj stageModule ≅ moduleSheaf) := by
  classical
  let Index := {subalgebra : Subalgebra ℤ Γ(baseScheme, ⊤) // subalgebra.FG}
  let ringDiagram := CommRingCat.fgSubalgebraDiagram Γ(baseScheme, ⊤)
  let ringCocone := CommRingCat.fgSubalgebraCocone Γ(baseScheme, ⊤)
  let diagram := ringDiagram.op ⋙ Scheme.Spec
  let specCone := Scheme.Spec.mapCone ringCocone.op
  have specLimit : IsLimit specCone := isLimitOfPreserves Scheme.Spec
    (CommRingCat.isColimitFgSubalgebraCocone Γ(baseScheme, ⊤)).op
  let cone := specCone.extend baseScheme.isoSpec.hom
  have limit : IsLimit cone := IsLimit.ofIsoLimit specLimit
    (Cone.extendIso specCone baseScheme.isoSpec.symm)
  letI noetherianStages : ∀ stageIndex, IsNoetherianRing (ringDiagram.obj stageIndex) := by
    intro stageIndex
    change IsNoetherianRing stageIndex.val
    letI : Algebra.FiniteType ℤ stageIndex.val :=
      (Subalgebra.fg_iff_finiteType _).mp stageIndex.property
    exact Algebra.FiniteType.isNoetherianRing ℤ stageIndex.val
  letI : ∀ {sourceIndex targetIndex : Indexᵒᵖ} (transition : sourceIndex ⟶ targetIndex),
      IsAffineHom (diagram.map transition) := by
    intro sourceIndex targetIndex transition
    change IsAffineHom (Spec.map (ringDiagram.map transition.unop))
    infer_instance
  obtain ⟨initialIndex, initialScheme, initialMap, initialComparison, proper,
      finitePresentation, quasiCompact, quasiSeparated, initialSquare⟩ :=
    Scheme.exists_isPullback_of_isProper_of_isLimit ringDiagram cone limit sourceMap
  letI : IsProper initialMap := proper
  letI : LocallyOfFinitePresentation initialMap := finitePresentation
  letI : QuasiCompact initialMap := quasiCompact
  letI : QuasiSeparated initialMap := quasiSeparated
  letI : CompactSpace initialScheme :=
    QuasiCompact.compactSpace_of_compactSpace initialMap
  let Tail := {stageIndex : Index // initialIndex ≤ stageIndex}
  letI : Nonempty Tail := ⟨⟨initialIndex, le_rfl⟩⟩
  letI : IsDirectedOrder Tail := ⟨by
    intro firstIndex secondIndex
    obtain ⟨commonIndex, firstLe, secondLe⟩ := exists_ge_ge firstIndex.val secondIndex.val
    exact ⟨⟨commonIndex, firstIndex.property.trans firstLe⟩, firstLe, secondLe⟩⟩
  let equivalence := tailOverEquivalence initialIndex
  let coefficientDiagram := equivalence.functor ⋙ baseChangeDiagram diagram initialMap
  let coefficientCone := (baseChangeCone diagram cone initialMap).whisker equivalence.functor
  have coefficientLimit : IsLimit coefficientCone :=
    (Functor.Initial.isLimitWhiskerEquiv equivalence.functor
      (baseChangeCone diagram cone initialMap)).symm
        (isLimitBaseChangeCone diagram cone initialMap limit)
  letI : ∀ {sourceIndex targetIndex : Tailᵒᵖ} (transition : sourceIndex ⟶ targetIndex),
      IsAffineHom (coefficientDiagram.map transition) := by
    intro sourceIndex targetIndex transition
    exact inferInstanceAs (IsAffineHom
      ((baseChangeDiagram diagram initialMap).map (equivalence.functor.map transition)))
  letI : ∀ stageIndex : Tailᵒᵖ, CompactSpace (coefficientDiagram.obj stageIndex) := by
    intro stageIndex
    exact inferInstanceAs (CompactSpace
      ((baseChangeDiagram diagram initialMap).obj (equivalence.functor.obj stageIndex)))
  letI : ∀ stageIndex : Tailᵒᵖ, (coefficientDiagram.obj stageIndex).IsSeparated := by
    intro stageIndex
    haveI : (diagram.obj (equivalence.functor.obj stageIndex).left).IsSeparated :=
      inferInstanceAs ((Spec (ringDiagram.obj
        (equivalence.functor.obj stageIndex).left.unop)).IsSeparated)
    change (Limits.pullback initialMap
      (diagram.map (equivalence.functor.obj stageIndex).hom)).IsSeparated
    rw [Scheme.isSeparated_iff, ← terminal.comp_from (pullback.snd initialMap
      (diagram.map (equivalence.functor.obj stageIndex).hom))]
    infer_instance
  let canonicalIso := initialSquare.isoPullback
  let limitModule := (pullback canonicalIso.inv).obj moduleSheaf
  obtain ⟨coefficientIndex, coefficientModule, finiteCoefficient, ⟨recovery⟩⟩ :=
    exists_isFinitePresentation_pullback_iso_of_isLimit coefficientDiagram coefficientCone
      coefficientLimit limitModule
  letI : coefficientModule.IsFinitePresentation := finiteCoefficient
  let coefficientProjection :
      Limits.pullback initialMap (cone.π.app (Opposite.op initialIndex)) ⟶
        Limits.pullback initialMap (diagram.map (homOfLE coefficientIndex.property).op) :=
    coefficientCone.π.app (Opposite.op coefficientIndex)
  let coefficientMap := pullback.snd initialMap
    (diagram.map (homOfLE coefficientIndex.property).op)
  let coefficientComparison := canonicalIso.hom ≫ coefficientProjection
  have canonicalSquare : IsPullback canonicalIso.hom sourceMap
      (pullback.snd initialMap (cone.π.app (Opposite.op initialIndex))) (𝟙 baseScheme) :=
    IsPullback.of_horiz_isIso
      ⟨initialSquare.isoPullback_hom_snd.trans (Category.comp_id _).symm⟩
  have coefficientSquare : IsPullback coefficientComparison sourceMap coefficientMap
      (cone.π.app (Opposite.op coefficientIndex.val)) := by
    have stageSquare := isPullback_baseChangeCone_π diagram cone initialMap
      (Over.mk (homOfLE coefficientIndex.property).op)
    change IsPullback coefficientProjection
      (pullback.snd initialMap (cone.π.app (Opposite.op initialIndex))) coefficientMap
      (cone.π.app (Opposite.op coefficientIndex.val)) at stageSquare
    simpa only [Category.id_comp] using canonicalSquare.paste_horiz
      stageSquare
  let coefficientRecovery : (pullback coefficientComparison).obj coefficientModule ≅
      moduleSheaf :=
    (pullbackCompOfEq canonicalIso.hom coefficientProjection coefficientComparison rfl
      coefficientModule).symm ≪≫
      (pullback canonicalIso.hom).mapIso recovery ≪≫
      pullbackCompOfEq canonicalIso.hom canonicalIso.inv (𝟙 sourceScheme)
        canonicalIso.hom_inv_id moduleSheaf ≪≫ (pullbackId sourceScheme).app moduleSheaf
  have coefficientFlat : ((pullback (pullback.fst coefficientMap
      (cone.π.app (Opposite.op coefficientIndex.val)))).obj coefficientModule).IsFlatOver
      (pullback.snd coefficientMap (cone.π.app (Opposite.op coefficientIndex.val))) := by
    rw [← coefficientSquare.isoPullback_inv_snd]
    exact (flat.pullback_of_isOpenImmersion coefficientSquare.isoPullback.inv).of_iso
      ((pullback coefficientSquare.isoPullback.inv).mapIso coefficientRecovery.symm ≪≫
        pullbackCompOfEq _ _ _ coefficientSquare.isoPullback_inv_fst coefficientModule)
  obtain ⟨flatIndex, transition, eventuallyFlat⟩ :=
    exists_isFlatOver_pullback_of_fgSubalgebra baseScheme
      (initialStage := Opposite.op coefficientIndex.val) coefficientMap
      coefficientModule coefficientFlat
  let stageTransition : diagram.obj flatIndex ⟶
      diagram.obj (Opposite.op coefficientIndex.val) :=
    Spec.map (CommRingCat.ofHom
      (Subalgebra.inclusion (leOfHom transition.unop)).toRingHom)
  have stageNaturality : cone.π.app flatIndex ≫ stageTransition =
      cone.π.app (Opposite.op coefficientIndex.val) := by
    change cone.π.app flatIndex ≫ diagram.map transition = _
    exact cone.w transition
  let stageScheme := Limits.pullback coefficientMap stageTransition
  let stageMap : stageScheme ⟶ Spec (ringDiagram.obj flatIndex.unop) :=
    pullback.snd coefficientMap stageTransition
  let stageModule := (pullback (pullback.fst coefficientMap stageTransition)).obj coefficientModule
  have stageFlat : stageModule.IsFlatOver stageMap := by
    simpa only [stageModule, stageMap, stageTransition, Category.id_comp] using
      eventuallyFlat flatIndex (𝟙 flatIndex)
  let comparison : sourceScheme ⟶ stageScheme := pullback.lift coefficientComparison
    (sourceMap ≫ cone.π.app flatIndex) (by
      calc
        coefficientComparison ≫ coefficientMap =
            sourceMap ≫ cone.π.app (Opposite.op coefficientIndex.val) := coefficientSquare.w
        _ = sourceMap ≫ (cone.π.app flatIndex ≫ stageTransition) :=
          congrArg (fun baseMap ↦ sourceMap ≫ baseMap) stageNaturality.symm
        _ = (sourceMap ≫ cone.π.app flatIndex) ≫ stageTransition :=
          (Category.assoc sourceMap (cone.π.app flatIndex) stageTransition).symm)
  have square : IsPullback comparison sourceMap stageMap (cone.π.app flatIndex) := by
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback coefficientMap stageTransition)
    · simpa only [comparison, pullback.lift_fst, stageNaturality] using coefficientSquare
    · exact pullback.lift_snd _ _ _
  refine ⟨ringDiagram.obj flatIndex.unop, noetherianStages flatIndex.unop,
    stageScheme, stageMap, inferInstance, inferInstance, stageModule, inferInstance,
    stageFlat, comparison, cone.π.app flatIndex, square, ?_⟩
  exact ⟨pullbackCompOfEq comparison (pullback.fst coefficientMap stageTransition)
    coefficientComparison (pullback.lift_fst _ _ _) coefficientModule ≪≫ coefficientRecovery⟩

/-- Near every point of an arbitrary base, a proper finitely presented family
with relatively flat finitely presented coefficients has a proper Noetherian
model with relatively flat coefficients and an actual recovery isomorphism. -/
theorem exists_mem_opens_isPullback_over_noetherian_of_isProper
    {sourceScheme baseScheme : Scheme.{u}} (sourceMap : sourceScheme ⟶ baseScheme)
    [IsProper sourceMap] [LocallyOfFinitePresentation sourceMap]
    (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsFinitePresentation]
    (flat : moduleSheaf.IsFlatOver sourceMap) (point : baseScheme) :
    ∃ openSubset : baseScheme.Opens, point ∈ openSubset ∧ IsAffine openSubset.toScheme ∧
      ∃ (stageRing : CommRingCat.{u}) (_ : IsNoetherianRing stageRing)
        (stageScheme : Scheme.{u}) (stageMap : stageScheme ⟶ Spec stageRing)
        (_ : IsProper stageMap) (_ : LocallyOfFinitePresentation stageMap)
        (stageModule : stageScheme.Modules) (_ : stageModule.IsFinitePresentation),
        stageModule.IsFlatOver stageMap ∧
          ∃ (comparison : Limits.pullback sourceMap openSubset.ι ⟶ stageScheme)
            (baseComparison : openSubset.toScheme ⟶ Spec stageRing),
            IsPullback comparison (pullback.snd sourceMap openSubset.ι)
              stageMap baseComparison ∧
              Nonempty ((pullback comparison).obj stageModule ≅
                (pullback (pullback.fst sourceMap openSubset.ι)).obj moduleSheaf) := by
  obtain ⟨openSubset, affine, membership, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := baseScheme) (x := point) (U := ⊤) (by trivial)
  letI : IsAffine openSubset.toScheme := affine
  let restrictedModule := (pullback (pullback.fst sourceMap openSubset.ι)).obj moduleSheaf
  have restrictedFlat : restrictedModule.IsFlatOver (pullback.snd sourceMap openSubset.ι) := by
    apply IsFlatOver.of_comp_isOpenImmersion openSubset.ι
    rw [← pullback.condition]
    exact flat.pullback_of_isOpenImmersion (pullback.fst sourceMap openSubset.ι)
  obtain ⟨stageRing, noetherian, stageScheme, stageMap, proper, finitePresentation,
      stageModule, finiteCoefficient, stageFlat, comparison, baseComparison,
      square, recovery⟩ := exists_isPullback_over_noetherian_of_isProper
        (pullback.snd sourceMap openSubset.ι) restrictedModule restrictedFlat
  exact ⟨openSubset, membership, affine, stageRing, noetherian, stageScheme, stageMap,
    proper, finitePresentation, stageModule, finiteCoefficient, stageFlat,
    comparison, baseComparison, square, recovery⟩

end AlgebraicGeometry.Scheme.Modules
