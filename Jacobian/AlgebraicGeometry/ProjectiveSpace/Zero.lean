import Jacobian.AlgebraicGeometry.ProjectiveSpace.Relative
import Jacobian.RingTheory.MvPolynomial.HomogeneousCharts

/-!
# Projective space on one homogeneous coordinate

For a singleton coordinate type, the unique standard affine open is the whole
projective space and its degree-zero coordinate ring is the base ring. Thus
the structure morphism of the relative projective space is an isomorphism.
-/

noncomputable section

set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (coordinates baseRing : Type u) [CommRing baseRing] [Unique coordinates]

/-- The degree-zero localization of a polynomial ring on one coordinate has no new elements. -/
lemma bijective_fromZeroRingHom_X :
    Function.Bijective (fromZeroRingHom (homogeneousSubmodule coordinates baseRing)
      (Submonoid.powers (X (default : coordinates)))) := by
  have homogeneous : ∀ coordinate : coordinates, (X coordinate : MvPolynomial coordinates baseRing) ∈
      homogeneousSubmodule coordinates baseRing 1 := fun coordinate ↦ isHomogeneous_X baseRing coordinate
  constructor
  · have regularPowers : Submonoid.powers (X (default : coordinates)) ≤
        nonZeroDivisors (MvPolynomial coordinates baseRing) :=
      Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp isRegular_X)
    have injectiveLocalization : Function.Injective (algebraMap (MvPolynomial coordinates baseRing)
        (Localization (Submonoid.powers (X default : MvPolynomial coordinates baseRing)))) :=
      IsLocalization.injective
        (S := Localization (Submonoid.powers (X default : MvPolynomial coordinates baseRing)))
        regularPowers
    intro firstElement secondElement equality
    refine Subtype.ext (injectiveLocalization ?_)
    rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap]
    exact congrArg HomogeneousLocalization.val equality
  · intro element
    have generators := Away.adjoin_mk_prod_pow_eq_top
      (𝒜 := homogeneousSubmodule coordinates baseRing) (homogeneous default)
      coordinates (X : coordinates → MvPolynomial coordinates baseRing)
      (adjoin_range_X_eq_top coordinates baseRing) (fun _ ↦ 1) homogeneous
    have constants : (⊤ : Subalgebra (homogeneousSubmodule coordinates baseRing 0)
        (Away (homogeneousSubmodule coordinates baseRing) (X (default : coordinates)))) ≤ ⊥ := by
      rw [← generators]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨degree, exponents, totalDegree, -, rfl⟩
      have product_eq : (∏ coordinate, (X coordinate : MvPolynomial coordinates baseRing) ^
          exponents coordinate) = X (default : coordinates) ^ degree := by
        rw [Fintype.prod_unique]
        congr 1
        simpa using totalDegree
      refine Algebra.mem_bot.mpr ⟨1, ?_⟩
      rw [map_one]
      refine HomogeneousLocalization.val_injective _ ?_
      rw [HomogeneousLocalization.val_one, Away.val_mk, product_eq]
      exact (Localization.mk_self_mk _ _).symm
    exact Algebra.mem_bot.mp (constants Algebra.mem_top)

end MvPolynomial

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable (coordinates baseRing : Type u) [CommRing baseRing] [Unique coordinates]

/-- The standard open of the unique homogeneous coordinate is the entire projective space. -/
lemma Proj.basicOpen_X_eq_top :
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule coordinates baseRing)
      (MvPolynomial.X default) = ⊤ := by
  have cover := Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule coordinates baseRing)
    (MvPolynomial.X : coordinates → MvPolynomial coordinates baseRing)
    (fun coordinate ↦ ⟨1, MvPolynomial.isHomogeneous_X baseRing coordinate⟩)
    (MvPolynomial.adjoin_range_X_eq_top coordinates baseRing)
  rwa [iSup_unique] at cover

/-- Projective space with a singleton coordinate type over an affine scheme is its base. -/
instance Proj.instIsIsoProjectiveSpaceOverAffineToSpec :
    IsIso (Proj.projectiveSpaceOverAffineToSpec coordinates baseRing) := by
  let grading := MvPolynomial.homogeneousSubmodule coordinates baseRing
  have homogeneous := MvPolynomial.isHomogeneous_X baseRing (default : coordinates)
  have : IsIso (Proj.awayι grading (MvPolynomial.X default) homogeneous one_pos) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _
      ((Proj.opensRange_awayι grading _ homogeneous one_pos).trans
        (Proj.basicOpen_X_eq_top coordinates baseRing))
  have : IsIso (CommRingCat.ofHom
      (fromZeroRingHom grading (Submonoid.powers (MvPolynomial.X (default : coordinates))))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (MvPolynomial.bijective_fromZeroRingHom_X coordinates baseRing)
  have : IsIso (Proj.awayι grading (MvPolynomial.X default) homogeneous one_pos ≫
      Proj.toSpecZero grading) := by
    rw [Proj.awayι_toSpecZero]
    infer_instance
  have : IsIso (Proj.toSpecZero grading) :=
    IsIso.of_isIso_comp_left (Proj.awayι grading (MvPolynomial.X default) homogeneous one_pos) _
  have : IsIso (CommRingCat.ofHom
      (MvPolynomial.homogeneousSubmoduleZeroEquiv coordinates baseRing).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (MvPolynomial.homogeneousSubmoduleZeroEquiv coordinates baseRing).bijective
  rw [Proj.projectiveSpaceOverAffineToSpec]
  infer_instance

/-- The structure morphism identifies projective space on one coordinate with its affine base. -/
def Proj.projectiveSpaceOverAffineIsoSpec :
    Proj.projectiveSpaceOverAffine coordinates baseRing ≅ Spec (.of baseRing) :=
  asIso (Proj.projectiveSpaceOverAffineToSpec coordinates baseRing)

@[simp]
lemma Proj.projectiveSpaceOverAffineIsoSpec_hom :
    (Proj.projectiveSpaceOverAffineIsoSpec coordinates baseRing).hom =
      Proj.projectiveSpaceOverAffineToSpec coordinates baseRing := rfl

namespace ProjectiveSpace

variable (coordinates : Type u) [Unique coordinates] (baseScheme : Scheme.{u})

/-- Relative projective space with a singleton coordinate type is its base scheme. -/
instance instIsIso : IsIso (ℙ(coordinates; baseScheme) ↘ baseScheme) := by
  have structureMap : terminal.from (Proj.projectiveSpaceOverAffine coordinates (ULift.{u} ℤ)) =
      Proj.projectiveSpaceOverAffineToSpec coordinates (ULift.{u} ℤ) ≫ terminal.from _ :=
    terminal.hom_ext _ _
  have terminalMap : terminal.from (Spec (.of (ULift.{u} ℤ))) =
      (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).hom := terminal.hom_ext _ _
  have : IsIso (terminal.from (Spec (.of (ULift.{u} ℤ)))) := terminalMap ▸ inferInstance
  have : IsIso (terminal.from
      (Proj.projectiveSpaceOverAffine coordinates (ULift.{u} ℤ))) := structureMap ▸ inferInstance
  exact inferInstanceAs (IsIso (pullback.fst _ _))

end ProjectiveSpace

end AlgebraicGeometry
