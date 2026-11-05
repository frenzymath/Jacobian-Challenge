import Jacobian.AlgebraicGeometry.Cohomology.Projective
import Jacobian.AlgebraicGeometry.Cohomology.ProjectiveSpace
import Jacobian.AlgebraicGeometry.Modules.FinitePushforward
import Jacobian.AlgebraicGeometry.ProjectiveLine.Basic

/-!
# Finite cohomology over projective space

Finite pushforward preserves finite presentation over a locally Noetherian
projective scheme, and native cohomology is unchanged by affine pushforward.
This transfers the projective finite-cohomology theorem to finite morphisms and
closed immersions into polynomial projective space. Affine morphisms also
transfer the quasi-coherent cohomological dimension bound for projective space.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable {sourceScheme : Scheme.{max u v}}

/-- Coherent sheaves on schemes finite over polynomial projective space have
finite native cohomology over the coefficient ring. -/
theorem hasFiniteH_of_isFinite_projectiveSpaceOverAffine
    (coordinates : Type v) (coefficients : Type (max u v)) [CommRing coefficients]
    [IsNoetherianRing coefficients] [Finite coordinates]
    (morphism : sourceScheme ⟶ Proj.projectiveSpaceOverAffine coordinates coefficients)
    [IsFinite morphism] (moduleSheaf : sourceScheme.Modules)
    [moduleSheaf.IsFinitePresentation] :
    HasFiniteH (morphism ≫ Proj.projectiveSpaceOverAffineToSpec coordinates coefficients)
      moduleSheaf := by
  letI : IsLocallyNoetherian (Proj.projectiveSpaceOverAffine coordinates coefficients) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Proj.projectiveSpaceOverAffineToSpec coordinates coefficients)
  letI := isFinitePresentation_pushforward_of_isFinite morphism moduleSheaf
  exact (hasFiniteH_pushforward_iff morphism
    (Proj.projectiveSpaceOverAffineToSpec coordinates coefficients) moduleSheaf).mp
    (Proj.hasFiniteH_projectiveSpaceOverAffine coordinates coefficients
      ((pushforward morphism).obj moduleSheaf))

/-- Closed immersions into polynomial projective space preserve finite
cohomology of finitely presented native module sheaves. -/
theorem hasFiniteH_of_isClosedImmersion_projectiveSpaceOverAffine
    (coordinates : Type v) (coefficients : Type (max u v)) [CommRing coefficients]
    [IsNoetherianRing coefficients] [Finite coordinates]
    (morphism : sourceScheme ⟶ Proj.projectiveSpaceOverAffine coordinates coefficients)
    [IsClosedImmersion morphism] (moduleSheaf : sourceScheme.Modules)
    [moduleSheaf.IsFinitePresentation] :
    HasFiniteH (morphism ≫ Proj.projectiveSpaceOverAffineToSpec coordinates coefficients)
      moduleSheaf :=
  hasFiniteH_of_isFinite_projectiveSpaceOverAffine coordinates coefficients morphism moduleSheaf

/-- The native degreewise finite-cohomology consequence for a closed immersion
into polynomial projective space. -/
theorem finite_H_of_isClosedImmersion_projectiveSpaceOverAffine
    (coordinates : Type v) (coefficients : Type (max u v)) [CommRing coefficients]
    [IsNoetherianRing coefficients] [Finite coordinates]
    (morphism : sourceScheme ⟶ Proj.projectiveSpaceOverAffine coordinates coefficients)
    [IsClosedImmersion morphism] (moduleSheaf : sourceScheme.Modules)
    [moduleSheaf.IsFinitePresentation] (degree : ℕ) :
    letI := moduleHOfSpec
      (morphism ≫ Proj.projectiveSpaceOverAffineToSpec coordinates coefficients)
      moduleSheaf degree
    Module.Finite coefficients (moduleSheaf.H degree) := by
  exact (hasFiniteH_of_isClosedImmersion_projectiveSpaceOverAffine
    coordinates coefficients morphism moduleSheaf) degree

/-- A coherent sheaf on a scheme finite over the native projective line has
finite native cohomology over the ground field. -/
theorem hasFiniteH_of_isFinite_projectiveLine {lineSourceScheme : Scheme.{u}}
    (coefficients : Type u) [Field coefficients]
    (morphism : lineSourceScheme ⟶ projectiveLine coefficients) [IsFinite morphism]
    (moduleSheaf : lineSourceScheme.Modules) [moduleSheaf.IsFinitePresentation] :
    HasFiniteH (morphism ≫ projectiveLineToSpec coefficients) moduleSheaf := by
  change HasFiniteH
    (morphism ≫ Proj.projectiveSpaceOverAffineToSpec (Fin 2) coefficients) moduleSheaf
  exact hasFiniteH_of_isFinite_projectiveSpaceOverAffine
    (Fin 2) coefficients morphism moduleSheaf

/-- A scheme affine over polynomial projective `d`-space has vanishing
quasi-coherent cohomology in degrees greater than `d`. -/
theorem subsingleton_H_of_isAffineHom_projectiveSpaceOverAffine
    (coordinates : Type v) (coefficients : Type (max u v)) [CommRing coefficients]
    [Finite coordinates] {dimension : ℕ}
    (coordinateCount : Nat.card coordinates = dimension + 1)
    (morphism : sourceScheme ⟶ Proj.projectiveSpaceOverAffine coordinates coefficients)
    [IsAffineHom morphism] (moduleSheaf : sourceScheme.Modules)
    [moduleSheaf.IsQuasicoherent] {degree : ℕ} (degreeBound : dimension < degree) :
    Subsingleton (moduleSheaf.H degree) := by
  letI : ((pushforward morphism).obj moduleSheaf).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom morphism moduleSheaf
  letI := Proj.subsingleton_H_projectiveSpaceOverAffine_of_lt coordinates coefficients
    coordinateCount ((pushforward morphism).obj moduleSheaf) degreeBound
  obtain ⟨comparison⟩ := nonempty_functorH_iso_pushforwardAb_of_isAffineHom morphism degree
  let acyclicModule : (cechAcyclicOnAffines sourceScheme).FullSubcategory :=
    ⟨(SheafOfModules.toSheaf sourceScheme.ringCatSheaf).obj moduleSheaf,
      cechAcyclicOnAffines_of_isQuasicoherent moduleSheaf⟩
  let cohomologyEquiv : moduleSheaf.H degree ≃+
      ((pushforward morphism).obj moduleSheaf).H degree :=
    (comparison.app acyclicModule).addCommGroupIsoToAddEquiv
  exact cohomologyEquiv.injective.subsingleton

/-- A scheme affine over the projective line has vanishing quasi-coherent
cohomology above degree one. -/
theorem subsingleton_H_of_isAffineHom_projectiveLine {lineSourceScheme : Scheme.{u}}
    (coefficients : Type u) [Field coefficients]
    (morphism : lineSourceScheme ⟶ projectiveLine coefficients) [IsAffineHom morphism]
    (moduleSheaf : lineSourceScheme.Modules) [moduleSheaf.IsQuasicoherent]
    {degree : ℕ} (degreeBound : 1 < degree) : Subsingleton (moduleSheaf.H degree) := by
  exact subsingleton_H_of_isAffineHom_projectiveSpaceOverAffine
    (Fin 2) coefficients (dimension := 1) (by simp) morphism moduleSheaf degreeBound

end AlgebraicGeometry.Scheme.Modules
