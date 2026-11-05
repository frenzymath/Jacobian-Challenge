import Jacobian.AlgebraicGeometry.Modules.RestrictionIsomorphism
import Jacobian.AlgebraicGeometry.ProjectiveSpace.OfSections
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.Polynomial

/-!
# Twisting sheaves on relative projective space

The sheaf `𝒪(m)` on relative projective space is pulled back from its integral
model. Twisting sheaves are invertible and commute with base change.
Multiplication by a homogeneous coordinate is an isomorphism on the
corresponding standard open, as is its nonnegative power `𝒪 ⟶ 𝒪(d)`.
These power sections retain this property after pullback to any scheme.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (coordinates : Type u)

namespace ProjectiveSpace

open Scheme.Modules

variable (baseScheme : Scheme.{u})

/-- The twisting sheaf `𝒪(m)` on relative projective space, pulled back from the integral model. -/
def twist (degree : ℤ) : ℙ(coordinates; baseScheme).Modules :=
  (pullback (toIntegralModel coordinates baseScheme)).obj
    (Proj.twist (MvPolynomial.homogeneousSubmodule coordinates (ULift.{u} ℤ)) degree)

/-- The zeroth twisting sheaf is the structure sheaf. -/
def unitIsoTwistZero :
    SheafOfModules.unit ℙ(coordinates; baseScheme).ringCatSheaf ≅ twist coordinates baseScheme 0 :=
  (pullbackObjUnitIso (toIntegralModel coordinates baseScheme)).symm ≪≫
    (pullback (toIntegralModel coordinates baseScheme)).mapIso Proj.unitIsoTwistZero

/-- Every relative twisting sheaf is invertible. -/
instance isInvertible_twist (degree : ℤ) : (twist coordinates baseScheme degree).IsInvertible := by
  change ((pullback (toIntegralModel coordinates baseScheme)).obj
    (Proj.twist (MvPolynomial.homogeneousSubmodule coordinates (ULift.{u} ℤ)) degree)).IsInvertible
  infer_instance

/-- Twisting sheaves commute with an arbitrary change of base. -/
def pullbackMapTwistIso {sourceScheme targetScheme : Scheme.{u}}
    (baseMap : sourceScheme ⟶ targetScheme) (degree : ℤ) :
    (pullback (map coordinates baseMap)).obj (twist coordinates targetScheme degree) ≅
      twist coordinates sourceScheme degree :=
  (pullbackComp (map coordinates baseMap) (toIntegralModel coordinates targetScheme)).app _ ≪≫
    (pullbackCongr (map_toIntegralModel coordinates baseMap)).app _

variable {coordinates baseScheme} in
/-- The pullback of a twisting sheaf along a morphism to projective space. -/
abbrev twistRestrict {sourceScheme : Scheme.{u}} (embedding : sourceScheme ⟶ ℙ(coordinates; baseScheme))
    (degree : ℤ) : sourceScheme.Modules :=
  (pullback embedding).obj (twist coordinates baseScheme degree)

/-- Multiplication by a homogeneous coordinate on relative projective space. -/
  def twistMulX (coordinate : coordinates) (degree : ℤ) :
    twist coordinates baseScheme degree ⟶ twist coordinates baseScheme (degree + 1) :=
  (pullback (toIntegralModel coordinates baseScheme)).map
    (Proj.twistMul degree (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinate))

/-- A homogeneous coordinate acts invertibly on its standard open. -/
  instance isIso_restrict_twistMulX (coordinate : coordinates) (degree : ℤ) :
    IsIso ((restrictFunctor (standardOpen coordinates baseScheme coordinate).ι).map
      (twistMulX coordinates baseScheme coordinate degree)) :=
  isIso_restrict_pullback_map (toIntegralModel coordinates baseScheme)
    (Proj.twistMul degree (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) coordinate))
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule coordinates (ULift.{u} ℤ))
      (MvPolynomial.X coordinate))

/-- Multiplications by homogeneous coordinates commute. -/
lemma twistMulX_comp_twistMulX (firstCoordinate secondCoordinate : coordinates) (degree : ℤ) :
    twistMulX coordinates baseScheme firstCoordinate degree ≫
        twistMulX coordinates baseScheme secondCoordinate (degree + 1) =
      twistMulX coordinates baseScheme secondCoordinate degree ≫
        twistMulX coordinates baseScheme firstCoordinate (degree + 1) := by
  rw [twistMulX, twistMulX, twistMulX, twistMulX, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (pullback (toIntegralModel coordinates baseScheme)).map
    (Proj.twistMul_comp_twistMul degree _ _)

/-- The global section `Tᵢ^d` of `𝒪(d)`, regarded as a morphism from the structure sheaf. -/
def twistPowSection (coordinate : coordinates) :
    (degree : ℕ) → (SheafOfModules.unit ℙ(coordinates; baseScheme).ringCatSheaf ⟶
      twist coordinates baseScheme degree)
  | 0 => (unitIsoTwistZero coordinates baseScheme).hom ≫ eqToHom (by rw [Nat.cast_zero])
  | degree + 1 => twistPowSection coordinate degree ≫
      twistMulX coordinates baseScheme coordinate degree ≫ eqToHom (by rw [Nat.cast_succ])

/-- A coordinate power trivializes its twist on the corresponding standard open. -/
instance isIso_restrict_twistPowSection (coordinate : coordinates) (degree : ℕ) :
    IsIso ((restrictFunctor (standardOpen coordinates baseScheme coordinate).ι).map
      (twistPowSection coordinates baseScheme coordinate degree)) := by
  induction degree with
  | zero =>
    rw [twistPowSection, Functor.map_comp]
    infer_instance
  | succ degree inductionHypothesis =>
    rw [twistPowSection, Functor.map_comp, Functor.map_comp]
    infer_instance

variable {coordinates baseScheme}

/-- The coordinate-power section pulled back along a morphism to projective space. -/
def pullbackTwistPowSection {sourceScheme : Scheme.{u}}
    (embedding : sourceScheme ⟶ ℙ(coordinates; baseScheme)) (coordinate : coordinates) (degree : ℕ) :
    SheafOfModules.unit sourceScheme.ringCatSheaf ⟶ twistRestrict embedding degree :=
  (pullbackObjUnitIso embedding).inv ≫
    (pullback embedding).map (twistPowSection coordinates baseScheme coordinate degree)

/-- A pulled-back coordinate power trivializes its twist over the inverse image of its
standard open. -/
instance isIso_restrict_pullbackTwistPowSection {sourceScheme : Scheme.{u}}
    (embedding : sourceScheme ⟶ ℙ(coordinates; baseScheme)) (coordinate : coordinates) (degree : ℕ) :
    IsIso ((restrictFunctor (embedding ⁻¹ᵁ standardOpen coordinates baseScheme coordinate).ι).map
      (pullbackTwistPowSection embedding coordinate degree)) := by
  have := isIso_restrict_pullback_map embedding
    (twistPowSection coordinates baseScheme coordinate degree)
    (standardOpen coordinates baseScheme coordinate)
  rw [pullbackTwistPowSection, Functor.map_comp]
  infer_instance

end ProjectiveSpace

end AlgebraicGeometry
