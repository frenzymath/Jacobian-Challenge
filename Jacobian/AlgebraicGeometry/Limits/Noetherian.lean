import Jacobian.Algebra.Category.Ring.Subalgebras
import Jacobian.AlgebraicGeometry.Limits.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.FiniteType

/-!
# Noetherian stages for affine finitely presented morphisms

An affine scheme of finite presentation over an affine base is the Cartesian
base change of an affine finitely presented scheme over a Noetherian ring.
The ring is constructed as a finitely generated integer subalgebra of the
global sections of the base; no Noetherian assumption on the base is needed.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- An affine finitely presented morphism between affine schemes descends to
an affine finitely presented morphism over a Noetherian ring. -/
theorem Scheme.exists_isPullback_over_noetherian_of_isAffine
    {sourceScheme baseScheme : Scheme.{schemeUniverse}}
    [IsAffine sourceScheme] [IsAffine baseScheme]
    (sourceMap : sourceScheme ⟶ baseScheme) [LocallyOfFinitePresentation sourceMap] :
    ∃ (stageRing : CommRingCat.{schemeUniverse}) (_ : IsNoetherianRing stageRing)
      (stageScheme : Scheme.{schemeUniverse}) (_ : IsAffine stageScheme)
      (stageMap : stageScheme ⟶ Spec stageRing) (_ : LocallyOfFinitePresentation stageMap)
      (comparison : sourceScheme ⟶ stageScheme) (baseComparison : baseScheme ⟶ Spec stageRing),
      IsPullback comparison sourceMap stageMap baseComparison := by
  let ringDiagram := CommRingCat.fgSubalgebraDiagram Γ(baseScheme, ⊤)
  let ringCocone := CommRingCat.fgSubalgebraCocone Γ(baseScheme, ⊤)
  let diagram := ringDiagram.op ⋙ Scheme.Spec
  let specCone := Scheme.Spec.mapCone ringCocone.op
  have specLimit : IsLimit specCone := isLimitOfPreserves Scheme.Spec
    (CommRingCat.isColimitFgSubalgebraCocone Γ(baseScheme, ⊤)).op
  let cone := specCone.extend baseScheme.isoSpec.hom
  have limit : IsLimit cone := IsLimit.ofIsoLimit specLimit
    (Cone.extendIso specCone baseScheme.isoSpec.symm)
  haveI affineStages : ∀ index, IsAffine (diagram.obj index) := by
    intro index
    change IsAffine (Spec (ringDiagram.obj index.unop))
    infer_instance
  haveI affineTransitions : ∀ {sourceIndex targetIndex} (transition : sourceIndex ⟶ targetIndex),
      IsAffineHom (diagram.map transition) := by
    intro sourceIndex targetIndex transition
    change IsAffineHom (Scheme.Spec.map (ringDiagram.op.map transition))
    infer_instance
  obtain ⟨stage, stageScheme, stageAffine, stageMap, stage_finitePresentation,
      comparison, square⟩ :=
    Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine diagram cone limit sourceMap
  refine ⟨.of stage.unop.1, ?_, stageScheme, stageAffine, stageMap,
    stage_finitePresentation, comparison, cone.π.app stage, square⟩
  letI : Algebra.FiniteType ℤ stage.unop.1 :=
    (Subalgebra.fg_iff_finiteType _).mp stage.unop.2
  exact Algebra.FiniteType.isNoetherianRing ℤ stage.unop.1

end AlgebraicGeometry
