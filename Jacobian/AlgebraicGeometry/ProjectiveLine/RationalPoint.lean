import Jacobian.AlgebraicGeometry.ProjectiveLine.Charts
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Rational functions as points of the projective line

An element of a field extension gives the point `[1:t]` through the standard
affine chart. A transcendental element has nonclosed image, and its affine
coordinate belongs to the image of the induced homomorphism on local rings.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveLine

variable {baseField : Type u} [Field baseField]

section Ring

variable {extensionRing : Type u} [CommRing extensionRing]

/-- The point `[1:element]`, defined using the standard affine chart. -/
def affinePoint (coefficients : baseField →+* extensionRing) (element : extensionRing) :
    Spec (.of extensionRing) ⟶ projectiveLine baseField :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.eval₂Hom coefficients (fun _ : {index : Fin 2 // index ≠ 0} ↦ element))) ≫
      chartMorphism baseField 0

/-- The point `[1:element]` has the prescribed structure morphism. -/
theorem affinePoint_toSpec (coefficients : baseField →+* extensionRing)
    (element : extensionRing) :
    affinePoint coefficients element ≫ projectiveLineToSpec baseField =
      Spec.map (CommRingCat.ofHom coefficients) := by
  rw [affinePoint, Category.assoc, chartMorphism_toSpec, ← Spec.map_comp]
  congr 1
  ext coefficient
  simp

/-- The standard affine point commutes with homomorphisms of coefficient algebras. -/
theorem SpecMap_affinePoint {targetRing : Type u} [CommRing targetRing]
    (coefficients : baseField →+* extensionRing) (homomorphism : extensionRing →+* targetRing)
    (element : extensionRing) :
    Spec.map (CommRingCat.ofHom homomorphism) ≫ affinePoint coefficients element =
      affinePoint (homomorphism.comp coefficients) (homomorphism element) := by
  have evaluation :
      homomorphism.comp (MvPolynomial.eval₂Hom coefficients
        (fun _ : {index : Fin 2 // index ≠ 0} ↦ element)) =
      MvPolynomial.eval₂Hom (homomorphism.comp coefficients)
        (fun _ : {index : Fin 2 // index ≠ 0} ↦ homomorphism element) := by
    ext <;> simp
  simpa only [affinePoint, ← Category.assoc, ← Spec.map_comp, CommRingCat.ofHom_comp] using congrArg
    (fun ringMap ↦ Spec.map (CommRingCat.ofHom ringMap) ≫ chartMorphism baseField 0) evaluation

end Ring

variable {extensionField : Type u} [Field extensionField]

/-- A transcendental affine coordinate gives a nonclosed point of the projective line. -/
theorem not_isClosed_affinePoint (coefficients : baseField →+* extensionField)
    (element : extensionField)
    (transcendental : letI := coefficients.toAlgebra; Transcendental baseField element) :
    ¬ IsClosed {affinePoint coefficients element (IsLocalRing.closedPoint extensionField)} := by
  letI : Unique {index : Fin 2 // index ≠ 0} :=
    ⟨⟨⟨1, by decide⟩⟩, fun ⟨index, nonzero⟩ ↦ by
      have equality : index = 1 := by omega
      subst index
      rfl⟩
  let evaluation := MvPolynomial.eval₂Hom coefficients
    (fun _ : {index : Fin 2 // index ≠ 0} ↦ element)
  let affinePoint := Spec.map (CommRingCat.ofHom evaluation)
    (IsLocalRing.closedPoint extensionField)
  have injective : Function.Injective evaluation := by
    let := coefficients.toAlgebra
    have independent : AlgebraicIndependent baseField
        (fun _ : {index : Fin 2 // index ≠ 0} ↦ element) :=
      algebraicIndependent_unique_type_iff.mpr transcendental
    exact independent
  intro closed
  have affine_closed : IsClosed ({affinePoint} :
      Set (Spec (.of (MvPolynomial {index : Fin 2 // index ≠ 0} baseField)))) := by
    have preimage : {affinePoint} = (chartMorphism baseField 0) ⁻¹'
        {chartMorphism baseField 0 affinePoint} := by
      ext point
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact (chartMorphism baseField 0).isOpenEmbedding.injective.eq_iff.symm
    rw [preimage]
    exact closed.preimage (chartMorphism baseField 0).continuous
  have maximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal affinePoint).mp affine_closed
  have zero_ideal : affinePoint.asIdeal = ⊥ := by
    change Ideal.comap evaluation (IsLocalRing.closedPoint extensionField).asIdeal = ⊥
    have zero : (IsLocalRing.closedPoint extensionField).asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.closedPoint extensionField).isPrime.ne_top
    rw [zero, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot evaluation).mp injective]
  rw [zero_ideal, ← Ring.isField_iff_maximal_bot] at maximal
  exact Polynomial.not_isField baseField
    (MulEquiv.isField maximal
      (MvPolynomial.uniqueAlgEquiv baseField {index : Fin 2 // index ≠ 0}).symm.toMulEquiv)

/-- The affine coordinate belongs to the image of the local-ring map of its field-valued point. -/
theorem mem_range_stalkClosedPointTo_affinePoint (coefficients : baseField →+* extensionField)
    (element : extensionField) :
    element ∈ Set.range (Scheme.stalkClosedPointTo (affinePoint coefficients element)) := by
  let evaluation := MvPolynomial.eval₂Hom coefficients
    (fun _ : {index : Fin 2 // index ≠ 0} ↦ element)
  let affineMap := Spec.map (CommRingCat.ofHom evaluation)
  let point := affineMap (IsLocalRing.closedPoint extensionField)
  let coordinate : Γ(Spec (.of (MvPolynomial {index : Fin 2 // index ≠ 0} baseField)), ⊤) :=
    (Scheme.ΓSpecIso _).inv (MvPolynomial.X ⟨1, by decide⟩)
  let germ := (Spec (.of (MvPolynomial {index : Fin 2 // index ≠ 0} baseField))).presheaf.germ
    ⊤ point trivial coordinate
  let stalkMap := (chartMorphism baseField 0).stalkMap point
  have inverse_apply : stalkMap (inv stalkMap germ) = germ := by
    exact CommRingCat.hom_inv_apply (asIso stalkMap) germ
  refine ⟨inv stalkMap germ, ?_⟩
  change Scheme.stalkClosedPointTo (affineMap ≫ chartMorphism baseField 0) (inv stalkMap germ) = _
  rw [Scheme.stalkClosedPointTo_comp, CommRingCat.comp_apply]
  change Scheme.stalkClosedPointTo affineMap (stalkMap (inv stalkMap germ)) = _
  rw [inverse_apply]
  change ((Spec (.of (MvPolynomial {index : Fin 2 // index ≠ 0} baseField))).presheaf.germ
    ⊤ point trivial ≫ Scheme.stalkClosedPointTo affineMap) coordinate = _
  rw [Scheme.germ_stalkClosedPointTo_Spec, CommRingCat.comp_apply]
  simp [coordinate, evaluation]

end AlgebraicGeometry.ProjectiveLine
