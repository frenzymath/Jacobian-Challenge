import Jacobian.AlgebraicGeometry.Modules.AffinePushforward
import Jacobian.AlgebraicGeometry.Modules.FinitePresentation
import Jacobian.AlgebraicGeometry.Modules.FiniteLocallyFree
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Coherent pushforward along finite morphisms

Over a locally Noetherian target, finite morphisms carry coherent module sheaves
to coherent module sheaves. On an affine open this is restriction of scalars
along a finite ring map.

Finite flat morphisms locally of finite presentation also preserve finite
locally free module sheaves, over arbitrary target schemes. This follows from
transitivity of finite presentation and flatness on affine sections.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {sourceScheme targetScheme : Scheme.{u}}

/-- A finite flat morphism locally of finite presentation sends vector bundles
to vector bundles, without a Noetherian hypothesis or a fixed-rank assumption. -/
theorem isFiniteLocallyFree_pushforward (morphism : sourceScheme ⟶ targetScheme)
    [IsFinite morphism] [Flat morphism] [LocallyOfFinitePresentation morphism]
    (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsFiniteLocallyFree] :
    ((pushforward morphism).obj moduleSheaf).IsFiniteLocallyFree := by
  letI := isQuasicoherent_pushforward_of_isAffineHom morphism moduleSheaf
  refine isFiniteLocallyFree_of_finitePresentation_flat_sections _ fun openSubset affine ↦ ?_
  have preimageAffine : IsAffineOpen (morphism ⁻¹ᵁ openSubset) := affine.preimage morphism
  obtain ⟨finitePresentation, projective⟩ :=
    finitePresentation_projective_sections moduleSheaf preimageAffine
  letI := (morphism.app openSubset).hom.toAlgebra
  letI : Module Γ(sourceScheme, morphism ⁻¹ᵁ openSubset)
      Γ((pushforward morphism).obj moduleSheaf, openSubset) :=
    inferInstanceAs (Module Γ(sourceScheme, morphism ⁻¹ᵁ openSubset)
      Γ(moduleSheaf, morphism ⁻¹ᵁ openSubset))
  letI : Module.FinitePresentation Γ(sourceScheme, morphism ⁻¹ᵁ openSubset)
      Γ((pushforward morphism).obj moduleSheaf, openSubset) := finitePresentation
  letI : Module.Projective Γ(sourceScheme, morphism ⁻¹ᵁ openSubset)
      Γ((pushforward morphism).obj moduleSheaf, openSubset) := projective
  letI : IsScalarTower Γ(targetScheme, openSubset) Γ(sourceScheme, morphism ⁻¹ᵁ openSubset)
      Γ((pushforward morphism).obj moduleSheaf, openSubset) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module.Finite Γ(targetScheme, openSubset)
      Γ(sourceScheme, morphism ⁻¹ᵁ openSubset) := morphism.finite_app openSubset affine
  letI : Algebra.FinitePresentation Γ(targetScheme, openSubset)
      Γ(sourceScheme, morphism ⁻¹ᵁ openSubset) := by
    have presentation := morphism.finitePresentation_appLE affine preimageAffine le_rfl
    rwa [← Hom.app_eq_appLE] at presentation
  letI : Module.Flat Γ(targetScheme, openSubset)
      Γ(sourceScheme, morphism ⁻¹ᵁ openSubset) := by
    have flat := morphism.flat_appLE affine preimageAffine le_rfl
    rwa [← Hom.app_eq_appLE] at flat
  letI : Module.FinitePresentation Γ(targetScheme, openSubset)
      Γ(sourceScheme, morphism ⁻¹ᵁ openSubset) :=
    .of_finite_of_finitePresentation _ _
  exact ⟨.trans Γ(targetScheme, openSubset) Γ((pushforward morphism).obj moduleSheaf, openSubset)
    Γ(sourceScheme, morphism ⁻¹ᵁ openSubset),
    .trans Γ(targetScheme, openSubset) Γ(sourceScheme, morphism ⁻¹ᵁ openSubset)
      Γ((pushforward morphism).obj moduleSheaf, openSubset)⟩

/-- A finite morphism to a locally Noetherian scheme preserves coherent sheaves. -/
theorem isFinitePresentation_pushforward_of_isFinite [IsLocallyNoetherian targetScheme]
    (morphism : sourceScheme ⟶ targetScheme) [IsFinite morphism] (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsFinitePresentation] :
    ((pushforward morphism).obj moduleSheaf).IsFinitePresentation := by
  letI := isQuasicoherent_pushforward_of_isAffineHom morphism moduleSheaf
  refine (isFinitePresentation_iff_forall_isAffineOpen ((pushforward morphism).obj moduleSheaf)).mpr ?_
  intro openSubset hU
  let scalarMap := (morphism.app openSubset).hom
  letI : Algebra Γ(targetScheme, openSubset) Γ(sourceScheme, morphism ⁻¹ᵁ openSubset) := scalarMap.toAlgebra
  letI : Module Γ(targetScheme, openSubset) Γ(moduleSheaf, morphism ⁻¹ᵁ openSubset) := Module.compHom Γ(moduleSheaf, morphism ⁻¹ᵁ openSubset) scalarMap
  letI : IsScalarTower Γ(targetScheme, openSubset) Γ(sourceScheme, morphism ⁻¹ᵁ openSubset) Γ(moduleSheaf, morphism ⁻¹ᵁ openSubset) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module.Finite Γ(targetScheme, openSubset) Γ(sourceScheme, morphism ⁻¹ᵁ openSubset) := morphism.finite_app openSubset hU
  letI := finitePresentation_sections_of_isFinitePresentation moduleSheaf (hU.preimage morphism)
  letI : Module.Finite Γ(targetScheme, openSubset) Γ(moduleSheaf, morphism ⁻¹ᵁ openSubset) :=
    Module.Finite.trans Γ(sourceScheme, morphism ⁻¹ᵁ openSubset) Γ(moduleSheaf, morphism ⁻¹ᵁ openSubset)
  letI := IsLocallyNoetherian.component_noetherian ⟨openSubset, hU⟩
  exact Module.finitePresentation_of_finite Γ(targetScheme, openSubset) Γ(moduleSheaf, morphism ⁻¹ᵁ openSubset)

end AlgebraicGeometry.Scheme.Modules
