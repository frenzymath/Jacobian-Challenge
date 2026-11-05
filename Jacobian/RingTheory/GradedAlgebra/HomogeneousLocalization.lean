import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Scalars and unit fractions in homogeneous localization

The degree-zero homogeneous localization of a graded algebra is an algebra over
 the coefficient ring. Fractions with equal numerator and denominator are units.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HomogeneousLocalization

variable {grades baseRing gradedRing : Type*} [CommRing baseRing] [CommRing gradedRing]
  [Algebra baseRing gradedRing] [AddCommMonoid grades] [DecidableEq grades]
  {grading : grades → Submodule baseRing gradedRing} [GradedAlgebra grading]
  (denominators : Submonoid gradedRing)

@[simp]
lemma val_fromZeroRingHom (element : grading 0) :
    (fromZeroRingHom grading denominators element).val = Localization.mk (element : gradedRing) 1 :=
  rfl

/-- If `A` is a graded `R`-algebra, the degree-zero part of a localization of `A` is an
`R`-algebra, via `R → 𝒜 0 → HomogeneousLocalization 𝒜 x`. -/
instance algebra : Algebra baseRing (HomogeneousLocalization grading denominators) :=
  { instSMul denominators with
    algebraMap := (fromZeroRingHom grading denominators).comp (algebraMap baseRing (grading 0))
    commutes' := fun _ _ ↦ mul_comm _ _
    smul_def' := fun coefficient fraction ↦ by
      obtain ⟨fraction, rfl⟩ := mk_surjective fraction
      ext
      simp only [← mk_smul, val_mk, RingHom.coe_comp, Function.comp_apply, val_mul,
        val_fromZeroRingHom, NumDenSameDeg.num_smul, NumDenSameDeg.den_smul,
        Localization.mk_mul, one_mul, Algebra.smul_def, SetLike.GradeZero.coe_algebraMap] }

instance scalarTowerFromGradeZero : IsScalarTower baseRing (grading 0) (HomogeneousLocalization grading denominators) :=
  .of_algebraMap_eq' rfl

@[simp]
lemma val_algebraMap (coefficient : baseRing) :
    (algebraMap baseRing (HomogeneousLocalization grading denominators) coefficient).val = Localization.mk (algebraMap baseRing gradedRing coefficient) 1 :=
  rfl

/-- The fraction map of a homogeneous localization preserves finite sums. -/
lemma val_sum {indices : Type*} (terms : Finset indices)
    (fractions : indices → HomogeneousLocalization grading denominators) :
    (∑ index ∈ terms, fractions index).val = ∑ index ∈ terms, (fractions index).val :=
  map_sum (algebraMap (HomogeneousLocalization grading denominators) (Localization denominators))
    fractions terms

variable (grading : ℕ → Submodule baseRing gradedRing) [GradedAlgebra grading]
  {denominator : gradedRing} {degree : ℕ}

lemma Away.mk_pow_self (hf : denominator ∈ grading degree) (exponent : ℕ) (homogeneous : denominator ^ exponent ∈ grading (exponent • degree)) :
    Away.mk grading hf exponent (denominator ^ exponent) homogeneous = 1 := by
  apply val_injective
  rw [Away.val_mk, val_one]
  exact Localization.mk_self (⟨denominator ^ exponent, exponent, rfl⟩ : Submonoid.powers denominator)

/-- The fraction `f / f` is `1` in `Away 𝒜 f`. -/
@[simp]
lemma Away.mk_self (hf : denominator ∈ grading degree) (homogeneous : denominator ∈ grading (1 • degree)) :
    Away.mk grading hf 1 denominator homogeneous = 1 := by
  simpa using Away.mk_pow_self grading hf 1 (by simpa using homogeneous)

end HomogeneousLocalization
