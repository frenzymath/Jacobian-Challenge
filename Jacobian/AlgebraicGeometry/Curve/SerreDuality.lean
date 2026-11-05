import Jacobian.AlgebraicGeometry.Curve.SeparatingFiniteMap
import Jacobian.AlgebraicGeometry.Curve.FiniteDualityComparison
import Jacobian.AlgebraicGeometry.Cohomology.Affine.Pushforward
import Jacobian.AlgebraicGeometry.Modules.FinitePushforward
import Jacobian.AlgebraicGeometry.ProjectiveLine.Duality

/-!
# Degree-one Serre duality for smooth proper integral curves

A separating finite flat map to the projective line transports degree-one
duality on the projective line to the curve. Affine pushforward preserves
cohomology, and finite differential trace identifies the dualizing modules.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe curveUniverse

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme

variable {baseField : Type curveUniverse} [Field baseField] {source : Scheme.{curveUniverse}}
  [source.Over (Spec (.of baseField))] [IsIntegral source]
  [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
  [IsProper (source ↘ Spec (.of baseField))]

/-- Degree-one Serre duality is natural in finite locally free coefficients. -/
theorem nonempty_dual_H_one_iso :
    Nonempty ((SheafOfModules.isFiniteLocallyFree source.ringCatSheaf).ι.op ⋙
        (Modules.cohomologyFunctor baseField 1).op ⋙ ModuleCat.dualFunctor baseField ≅
      (SheafOfModules.isFiniteLocallyFree source.ringCatSheaf).ι.op ⋙ Modules.dualFunctor source ⋙
        tensorRight (source ↘ Spec (.of baseField)).relativeDifferentials ⋙
          Modules.cohomologyFunctor baseField 0) := by
  obtain ⟨morphism, _, _, _, _, genericUnramified⟩ :=
    exists_isFinite_flat_hom_projectiveLine (baseField := baseField) (source := source)
  obtain ⟨affineComparison⟩ :=
    Modules.nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom baseField morphism 1
  obtain ⟨projectiveLineDuality⟩ := ProjectiveLine.nonempty_dual_H_one_iso baseField
  obtain ⟨finiteComparison⟩ := nonempty_homObj_pushforward_iso morphism genericUnramified
  let quasicoherentCoefficients :
      (SheafOfModules.isFiniteLocallyFree source.ringCatSheaf).FullSubcategory ⥤
        (SheafOfModules.isQuasicoherent source.ringCatSheaf).FullSubcategory :=
    ObjectProperty.lift _ (SheafOfModules.isFiniteLocallyFree source.ringCatSheaf).ι
      fun coefficient ↦ by
        have : coefficient.obj.IsFiniteLocallyFree := coefficient.property
        exact inferInstanceAs coefficient.obj.IsQuasicoherent
  let pushforwardCoefficients :
      (SheafOfModules.isFiniteLocallyFree source.ringCatSheaf).FullSubcategory ⥤
        ObjectProperty.FullSubcategory
          (fun coefficient : (projectiveLine baseField).Modules ↦ coefficient.IsFinitePresentation) :=
    ObjectProperty.lift _
      ((SheafOfModules.isFiniteLocallyFree source.ringCatSheaf).ι ⋙ Modules.pushforward morphism)
      fun coefficient ↦ by
        have : coefficient.obj.IsFiniteLocallyFree := coefficient.property
        let pushforward := (Modules.pushforward morphism).obj coefficient.obj
        have := Modules.isFiniteLocallyFree_pushforward morphism coefficient.obj
        exact SheafOfModules.IsFiniteLocallyFree.isFinitePresentation pushforward
  exact ⟨Functor.isoWhiskerRight
    (NatIso.op (Functor.isoWhiskerLeft quasicoherentCoefficients affineComparison).symm)
      (ModuleCat.dualFunctor baseField) ≪≫
    Functor.isoWhiskerLeft pushforwardCoefficients.op projectiveLineDuality ≪≫ finiteComparison⟩

end AlgebraicGeometry.Scheme
