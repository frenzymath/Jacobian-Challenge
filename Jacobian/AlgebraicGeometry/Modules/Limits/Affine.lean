import Jacobian.Algebra.Category.ModuleCat.FinitePresentation.Descent
import Jacobian.AlgebraicGeometry.Modules.FinitePresentation
import Jacobian.AlgebraicGeometry.Modules.PullbackTilde

/-!
# Finitely presented module sheaves on affine inverse limits

A finitely presented module sheaf on the spectrum of a directed ring colimit
is the pullback of a finitely presented module sheaf on one of the stages.
The stage sheaf is constructed from a descended finite presentation of global
sections, using the native sheafification and pullback comparison.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A finitely presented module sheaf over an affine inverse limit comes from a stage. -/
theorem exists_finitePresentation_model_of_directedColimit
    {Index : Type schemeUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] (diagram : Index ⥤ CommRingCat.{schemeUniverse})
    (moduleSheaf : (Spec (colimit diagram)).Modules) [moduleSheaf.IsFinitePresentation] :
    ∃ (stageIndex : Index) (stageSheaf : (Spec (diagram.obj stageIndex)).Modules),
      stageSheaf.IsFinitePresentation ∧
      Nonempty ((pullback (Spec.map (colimit.ι diagram stageIndex))).obj stageSheaf ≅
        moduleSheaf) := by
  let sections : ModuleCat.{schemeUniverse} (colimit diagram : CommRingCat.{schemeUniverse}) :=
    moduleSpecΓFunctor.obj moduleSheaf
  letI : Module.FinitePresentation (colimit diagram : CommRingCat.{schemeUniverse}) sections :=
    finitePresentation_sections_top_of_isFinitePresentation moduleSheaf
  obtain ⟨stageIndex, stageModule, finitePresentation, ⟨sectionsComparison⟩⟩ :=
    ModuleCat.exists_finitePresentation_model diagram sections
  letI : Module.FinitePresentation (diagram.obj stageIndex) stageModule := finitePresentation
  let stageSheaf : (Spec (diagram.obj stageIndex)).Modules := tilde stageModule
  obtain ⟨generators, spanGenerators, relations, spanRelations⟩ := finitePresentation.out
  let presentation := presentationTilde stageModule (generators : Set stageModule)
    spanGenerators (relations : Set _) spanRelations
  letI : presentation.IsFinite :=
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (generators : Set stageModule))⟩
      isFiniteType_relations :=
        ⟨inferInstanceAs (Finite (relations : Set (generators →₀ diagram.obj stageIndex)))⟩ }
  have finiteStageSheaf : stageSheaf.IsFinitePresentation := presentation.isFinitePresentation
  letI : SheafOfModules.IsQuasicoherent
      (R := (Spec (colimit diagram)).ringCatSheaf) moduleSheaf :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData moduleSheaf).choose.isQuasicoherent
  letI : IsIso moduleSheaf.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent moduleSheaf
  refine ⟨stageIndex, stageSheaf, finiteStageSheaf, ?_⟩
  exact ⟨(tildePullbackIso (colimit.ι diagram stageIndex)).app stageModule ≪≫
    (tilde.functor (colimit diagram)).mapIso sectionsComparison ≪≫
      asIso moduleSheaf.fromTildeΓ⟩

end AlgebraicGeometry.Scheme.Modules
