import Jacobian.AlgebraicGeometry.Curve.SeparatingFunction
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Rational functions regular on a finite set of a curve

On a smooth proper integral curve, a transcendental rational function can be
chosen to lie in every local ring in a prescribed finite set. Starting with a
transcendental element, one takes the reciprocal of a polynomial whose roots
avoid its residues at the points where it is regular. The reversed polynomial
shows regularity at its poles. The construction works over finite fields too.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A smooth proper integral curve has a transcendental rational function
regular at every point of any prescribed finite set. -/
theorem exists_transcendental_mem_range_stalk {baseField : Type u} [Field baseField]
    {scheme : Scheme.{u}} [scheme.Over (Spec (.of baseField))] [IsIntegral scheme]
    [SmoothOfRelativeDimension 1 (scheme ↘ Spec (.of baseField))]
    [IsProper (scheme ↘ Spec (.of baseField))] (points : Finset scheme) :
    ∃ element : scheme.functionField,
      (letI := (functionFieldRingHom baseField scheme).toAlgebra;
        Transcendental baseField element) ∧
      ∀ point ∈ points,
        element ∈ Set.range (algebraMap (scheme.presheaf.stalk point) scheme.functionField) := by
  classical
  let functionField := scheme.functionField
  letI := (functionFieldRingHom baseField scheme).toAlgebra
  obtain ⟨initial, transcendental, _⟩ := exists_separating_functionField_of_isProper
    (baseField := baseField) (scheme := scheme)
  let coefficients (point : scheme) : baseField →+* scheme.presheaf.stalk point :=
    ((scheme ↘ Spec (.of baseField)).structureStalk point).hom
  have compatible (point : scheme) :
      (algebraMap (scheme.presheaf.stalk point) functionField).comp (coefficients point) =
        functionFieldRingHom baseField scheme := by
    change (((scheme ↘ Spec (.of baseField)).structureStalk point) ≫
        scheme.presheaf.stalkSpecializes (genericPoint_specializes point)).hom =
      ((scheme ↘ Spec (.of baseField)).structureStalk (genericPoint scheme)).hom
    rw [Hom.structureStalk_stalkSpecializes]
  let residueCoefficients (point : scheme) :
      baseField →+* IsLocalRing.ResidueField (scheme.presheaf.stalk point) :=
    (IsLocalRing.residue _).comp (coefficients point)
  let residueValue (point : scheme) : IsLocalRing.ResidueField (scheme.presheaf.stalk point) :=
    if regular : IsLocalization.IsInteger (scheme.presheaf.stalk point) initial then
      IsLocalRing.residue _ regular.choose else 0
  let annihilator (point : scheme) : Polynomial baseField :=
    if integral : (residueCoefficients point).IsIntegralElem (residueValue point) then
      integral.choose else 1
  have monic (point : scheme) : (annihilator point).Monic := by
    simp only [annihilator]
    split_ifs with integral
    · exact integral.choose_spec.1
    · exact Polynomial.monic_one
  let polynomial : Polynomial baseField := Polynomial.X * ∏ point ∈ points, annihilator point + 1
  have polynomial_monic : polynomial.Monic := by
    refine (Polynomial.monic_X.mul
      (Polynomial.monic_prod_of_monic _ _ fun point _ ↦ monic point)).add_of_left ?_
    have product_monic := Polynomial.monic_prod_of_monic points annihilator
      fun point _ ↦ monic point
    rw [Polynomial.degree_one, Polynomial.degree_mul, Polynomial.degree_X,
      Polynomial.degree_eq_natDegree product_monic.ne_zero]
    norm_cast
    omega
  have residue_nonzero (point : scheme) (membership : point ∈ points) :
      Polynomial.eval₂ (residueCoefficients point) (residueValue point) polynomial ≠ 0 := by
    intro zero
    by_cases integral : (residueCoefficients point).IsIntegralElem (residueValue point)
    · have annihilates : Polynomial.eval₂ (residueCoefficients point) (residueValue point)
          (annihilator point) = 0 := by
        simp only [annihilator, dif_pos integral]
        exact integral.choose_spec.2
      have product_zero : Polynomial.eval₂ (residueCoefficients point) (residueValue point)
          (∏ otherPoint ∈ points, annihilator otherPoint) = 0 := by
        rw [Polynomial.eval₂_finsetProd]
        exact Finset.prod_eq_zero membership annihilates
      simp [polynomial, Polynomial.eval₂_add, Polynomial.eval₂_mul, product_zero] at zero
    · exact integral ⟨polynomial, polynomial_monic, zero⟩
  have positive_degree : polynomial.natDegree ≠ 0 := by
    have product_monic := Polynomial.monic_prod_of_monic points annihilator
      fun point _ ↦ monic point
    have product_degree : 0 < (Polynomial.X * ∏ point ∈ points, annihilator point).degree := by
      rw [Polynomial.degree_mul, Polynomial.degree_X,
        Polynomial.degree_eq_natDegree product_monic.ne_zero]
      norm_cast
      omega
    have constant_degree : (1 : Polynomial baseField).degree <
        (Polynomial.X * ∏ point ∈ points, annihilator point).degree := by
      rwa [Polynomial.degree_one]
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt constant_degree]
    exact (Polynomial.natDegree_pos_iff_degree_pos.mpr product_degree).ne'
  have initial_nonzero : initial ≠ 0 := fun equality ↦
    transcendental (equality ▸ isAlgebraic_zero)
  have map_inverse (point : scheme) {value : scheme.presheaf.stalk point} (unit : IsUnit value) :
      algebraMap (scheme.presheaf.stalk point) functionField ↑unit.unit⁻¹ =
        (algebraMap (scheme.presheaf.stalk point) functionField value)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, IsUnit.mul_val_inv, map_one])
  refine ⟨(Polynomial.aeval initial polynomial)⁻¹,
    fun algebraic ↦ transcendental ?_, fun point membership ↦ ?_⟩
  · refine IsAlgebraic.of_aeval polynomial positive_degree ?_ (IsAlgebraic.inv_iff.mp algebraic)
    rw [polynomial_monic.leadingCoeff]
    exact one_mem _
  letI : ValuationRing (scheme.presheaf.stalk point) :=
    valuationRing_stalk (scheme ↘ Spec (.of baseField)) point
  by_cases regular : IsLocalization.IsInteger (scheme.presheaf.stalk point) initial
  · have initial_image : algebraMap _ functionField regular.choose = initial := regular.choose_spec
    have residue_eq : residueValue point = IsLocalRing.residue _ regular.choose := by
      simp [residueValue, dif_pos regular]
    have evaluated_unit : IsUnit (Polynomial.eval₂ (coefficients point) regular.choose polynomial) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, Polynomial.hom_eval₂, ← residue_eq]
      exact residue_nonzero point membership
    refine ⟨↑evaluated_unit.unit⁻¹, ?_⟩
    rw [map_inverse, Polynomial.hom_eval₂, compatible, initial_image]
    rfl
  · obtain ⟨localInverse, inverse_image⟩ :=
      (ValuationRing.isInteger_or_isInteger (scheme.presheaf.stalk point) initial).resolve_left regular
    have inverse_in_maximal : localInverse ∈ IsLocalRing.maximalIdeal (scheme.presheaf.stalk point) := by
      refine (IsLocalRing.mem_maximalIdeal _).mpr fun unit ↦ regular ⟨↑unit.unit⁻¹, ?_⟩
      rw [map_inverse, inverse_image, inv_inv]
    have reversed_unit : IsUnit
        (Polynomial.eval₂ (coefficients point) localInverse polynomial.reverse) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, Polynomial.hom_eval₂,
        (IsLocalRing.residue_eq_zero_iff localInverse).mpr inverse_in_maximal,
        Polynomial.eval₂_at_zero, Polynomial.coeff_zero_reverse,
        polynomial_monic.leadingCoeff, map_one]
      exact one_ne_zero
    letI := invertibleOfNonzero initial_nonzero
    have evaluation_eq : Polynomial.aeval initial polynomial =
        algebraMap _ functionField
          (Polynomial.eval₂ (coefficients point) localInverse polynomial.reverse) *
            initial ^ polynomial.natDegree := by
      rw [Polynomial.hom_eval₂, compatible, inverse_image, ← invOf_eq_inv,
        Polynomial.eval₂_reverse_mul_pow]
      rfl
    refine ⟨↑reversed_unit.unit⁻¹ * localInverse ^ polynomial.natDegree, ?_⟩
    rw [map_mul, map_pow, map_inverse, inverse_image, evaluation_eq, mul_inv, inv_pow]

end AlgebraicGeometry.Scheme
