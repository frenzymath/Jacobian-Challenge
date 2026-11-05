import Jacobian.AlgebraicGeometry.Curve.FiniteDuality
import Jacobian.AlgebraicGeometry.Modules.PushforwardHom
import Jacobian.AlgebraicGeometry.Modules.TensorHom
import Jacobian.AlgebraicGeometry.Cohomology.Pushforward

/-!
# Finite duality for vector bundles on smooth curves

For a finite flat, generically unramified morphism from a smooth curve to the projective
line, the trace of differentials identifies the pushforward of an internal Hom with the
internal Hom of the pushforward. This comparison is natural in finite locally free
coefficients. Taking global sections identifies the latter with degree-zero cohomology
of the dual tensored with the canonical sheaf.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
  [source.Over (Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]

/-- The trace comparison for a finite flat, generically unramified map to the projective
line is an isomorphism for every finite locally free sheaf. -/
theorem exists_isIso_pushforwardHomObjComparison
    (morphism : source ⟶ projectiveLine baseField)
    [morphism.IsOver (Spec (.of baseField))] [IsFinite morphism] [Flat morphism]
    (genericUnramified : ∀ point : source, IsField (source.presheaf.stalk point) →
      (morphism.stalkMap point).hom.FormallyUnramified) :
    ∃ trace : (Modules.pushforward morphism).obj
        (source ↘ Spec (.of baseField)).relativeDifferentials ⟶
        (projectiveLineToSpec baseField).relativeDifferentials,
      ∀ moduleSheaf : source.Modules, moduleSheaf.IsFiniteLocallyFree →
        IsIso (Modules.pushforwardHomObjComparison morphism trace moduleSheaf) := by
  obtain ⟨trace, traceIsIso⟩ := exists_isIso_pushforwardHomObjComparison_unit
    morphism genericUnramified
  refine ⟨trace, fun moduleSheaf locallyFree ↦ ?_⟩
  letI := locallyFree
  exact Modules.isIso_pushforwardHomObjComparison_of_isIso_unit traceIsIso moduleSheaf

/-- Internal Hom into the canonical sheaf commutes with finite pushforward, naturally in
finite locally free coefficients, for a generically unramified map to the projective line. -/
theorem nonempty_homObj_pushforward_iso_pushforward_homObj
    (morphism : source ⟶ projectiveLine baseField)
    [morphism.IsOver (Spec (.of baseField))] [IsFinite morphism] [Flat morphism]
    (genericUnramified : ∀ point : source, IsField (source.presheaf.stalk point) →
      (morphism.stalkMap point).hom.FormallyUnramified) :
    Nonempty ((SheafOfModules.isFiniteLocallyFree source.ringCatSheaf).ι.op ⋙
        (Modules.pushforward morphism).op ⋙
        (SheafOfModules.homFunctor (projectiveLine baseField).sheaf).flip.obj
          (projectiveLineToSpec baseField).relativeDifferentials ≅
      (SheafOfModules.isFiniteLocallyFree source.ringCatSheaf).ι.op ⋙
        (SheafOfModules.homFunctor source.sheaf).flip.obj
          (source ↘ Spec (.of baseField)).relativeDifferentials ⋙
        Modules.pushforward morphism) := by
  obtain ⟨trace, traceIsIso⟩ := exists_isIso_pushforwardHomObjComparison
    morphism genericUnramified
  let comparison := CategoryTheory.Functor.whiskerLeft
    (SheafOfModules.isFiniteLocallyFree source.ringCatSheaf).ι.op
    (Modules.pushforwardHomObjComparisonNatTrans morphism trace)
  letI (moduleSheaf :
      (SheafOfModules.isFiniteLocallyFree source.ringCatSheaf).FullSubcategoryᵒᵖ) :
      IsIso (comparison.app moduleSheaf) :=
    traceIsIso moduleSheaf.unop.obj moduleSheaf.unop.property
  letI : IsIso comparison := NatIso.isIso_of_isIso_app comparison
  exact ⟨(asIso comparison).symm⟩

/-- Global sections of internal Hom from a finite pushforward into the canonical sheaf
identify naturally with degree-zero cohomology of the source dual tensored with its
canonical sheaf. -/
theorem nonempty_homObj_pushforward_iso
    (morphism : source ⟶ projectiveLine baseField)
    [morphism.IsOver (Spec (.of baseField))] [IsFinite morphism] [Flat morphism]
    (genericUnramified : ∀ point : source, IsField (source.presheaf.stalk point) →
      (morphism.stalkMap point).hom.FormallyUnramified) :
    Nonempty ((SheafOfModules.isFiniteLocallyFree source.ringCatSheaf).ι.op ⋙
        (Modules.pushforward morphism).op ⋙
        (SheafOfModules.homFunctor (projectiveLine baseField).sheaf).flip.obj
          (projectiveLineToSpec baseField).relativeDifferentials ⋙
        Modules.cohomologyFunctor baseField 0 ≅
      (SheafOfModules.isFiniteLocallyFree source.ringCatSheaf).ι.op ⋙
        Modules.dualFunctor source ⋙
        tensorRight (source ↘ Spec (.of baseField)).relativeDifferentials ⋙
        Modules.cohomologyFunctor baseField 0) := by
  obtain ⟨comparison⟩ := nonempty_homObj_pushforward_iso_pushforward_homObj
    morphism genericUnramified
  letI : (source ↘ Spec (.of baseField)).relativeDifferentials.IsInvertible :=
    Hom.isInvertible_relativeDifferentials (source ↘ Spec (.of baseField))
  exact ⟨CategoryTheory.Functor.isoWhiskerRight comparison
      (Modules.cohomologyFunctor baseField 0) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft
      ((SheafOfModules.isFiniteLocallyFree source.ringCatSheaf).ι.op ⋙
        (SheafOfModules.homFunctor source.sheaf).flip.obj
          (source ↘ Spec (.of baseField)).relativeDifferentials)
      (Modules.pushforwardCompCohomologyFunctorZeroIso baseField morphism) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft
      (SheafOfModules.isFiniteLocallyFree source.ringCatSheaf).ι.op
      (CategoryTheory.Functor.isoWhiskerRight
        (Modules.dualTensorHomIso (source ↘ Spec (.of baseField)).relativeDifferentials)
        (Modules.cohomologyFunctor baseField 0)).symm⟩

end AlgebraicGeometry.Scheme
