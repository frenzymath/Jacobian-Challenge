import Jacobian.RingTheory.GradedAlgebra.HomogeneousLocalization.DegreePart

/-!
# Maps on homogeneous degree parts at prime ideals

A graded ring homomorphism induces semilinear maps on every degree part of
localizations at corresponding prime ideals. These maps send homogeneous
fractions to the fractions of their images and respect the degree-zero
identification with homogeneous localization.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HomogeneousLocalization

variable {sourceRing targetRing sourceSubobjects targetSubobjects : Type*}
  [CommRing sourceRing] [CommRing targetRing]
  [SetLike sourceSubobjects sourceRing] [AddSubgroupClass sourceSubobjects sourceRing]
  [SetLike targetSubobjects targetRing] [AddSubgroupClass targetSubobjects targetRing]
  {sourceGrading : ℕ → sourceSubobjects} {targetGrading : ℕ → targetSubobjects}
  [GradedRing sourceGrading] [GradedRing targetGrading]
  (gradedMap : sourceGrading →+*ᵍ targetGrading)
  (sourcePrime : Ideal sourceRing) (targetPrime : Ideal targetRing)
  [sourcePrime.IsPrime] [targetPrime.IsPrime]
  (primeCompatibility : sourcePrime = targetPrime.comap gradedMap)

private lemma localRingHom_mem_degreePart (degree : ℤ)
    (fraction : degreePart sourceGrading sourcePrime.primeCompl degree) :
    Localization.localRingHom sourcePrime targetPrime gradedMap primeCompatibility fraction ∈
      degreePart targetGrading targetPrime.primeCompl degree := by
  obtain zero | ⟨numeratorDegree, denominatorDegree, numerator, denominator,
    denominatorMem, numeratorHomogeneous, denominatorHomogeneous, degreeEquation,
    fractionEquation⟩ := fraction.property
  · exact Or.inl (by rw [zero, map_zero])
  · have mappedDenominator : gradedMap denominator ∈ targetPrime.primeCompl := by
      change denominator ∉ sourcePrime at denominatorMem
      change gradedMap denominator ∉ targetPrime
      simpa only [primeCompatibility, Ideal.mem_comap] using denominatorMem
    refine Or.inr ⟨numeratorDegree, denominatorDegree, gradedMap numerator,
      gradedMap denominator, mappedDenominator, gradedMap.map_mem numeratorHomogeneous,
      gradedMap.map_mem denominatorHomogeneous, degreeEquation, ?_⟩
    rw [fractionEquation, Localization.localRingHom_mk]
    simp only [GradedRingHom.toRingHom_eq_toRingHom, GradedRingHom.coe_toRingHom]

/-- A graded ring homomorphism maps homogeneous fractions of degree `degree` at
corresponding prime ideals semilinearly over the homogeneous local-ring map. -/
def degreePart.localRingHom (degree : ℤ) :
    degreePart sourceGrading sourcePrime.primeCompl degree →ₛₗ[
      HomogeneousLocalization.localRingHom gradedMap sourcePrime targetPrime primeCompatibility]
      degreePart targetGrading targetPrime.primeCompl degree where
  toFun fraction := ⟨Localization.localRingHom sourcePrime targetPrime gradedMap
    primeCompatibility fraction,
    localRingHom_mem_degreePart gradedMap sourcePrime targetPrime primeCompatibility degree fraction⟩
  map_add' first second := Subtype.ext (map_add _ _ _)
  map_smul' scalar fraction := by
    apply Subtype.ext
    change Localization.localRingHom sourcePrime targetPrime gradedMap primeCompatibility
        (scalar.val * (fraction : Localization sourcePrime.primeCompl)) =
      (HomogeneousLocalization.localRingHom gradedMap sourcePrime targetPrime
        primeCompatibility scalar).val *
        Localization.localRingHom sourcePrime targetPrime gradedMap primeCompatibility fraction
    rw [map_mul, HomogeneousLocalization.val_localRingHom]

@[simp]
lemma degreePart.coe_localRingHom (degree : ℤ)
    (fraction : degreePart sourceGrading sourcePrime.primeCompl degree) :
    (degreePart.localRingHom gradedMap sourcePrime targetPrime primeCompatibility degree fraction :
      Localization targetPrime.primeCompl) =
      Localization.localRingHom sourcePrime targetPrime gradedMap primeCompatibility fraction :=
  rfl

@[simp]
lemma degreePart.localRingHom_mk {degree : ℤ} {numeratorDegree denominatorDegree : ℕ}
    (numerator : sourceGrading numeratorDegree) (denominator : sourceGrading denominatorDegree)
    (denominatorMem : (denominator : sourceRing) ∈ sourcePrime.primeCompl)
    (degreeEquation : (numeratorDegree : ℤ) = denominatorDegree + degree) :
    degreePart.localRingHom gradedMap sourcePrime targetPrime primeCompatibility degree
        (degreePart.mk numerator denominator denominatorMem degreeEquation) =
      degreePart.mk (gradedMap.gradedAddHom numeratorDegree numerator)
        (gradedMap.gradedAddHom denominatorDegree denominator)
        (by
          change gradedMap (denominator : sourceRing) ∉ targetPrime
          change (denominator : sourceRing) ∉ sourcePrime at denominatorMem
          simpa only [primeCompatibility, Ideal.mem_comap] using denominatorMem)
        degreeEquation := by
  apply Subtype.ext
  rw [degreePart.coe_localRingHom, degreePart.coe_mk, degreePart.coe_mk]
  have numeratorImage :
      ((gradedMap.gradedAddHom numeratorDegree numerator : targetGrading numeratorDegree) :
        targetRing) = gradedMap (numerator : sourceRing) := rfl
  have denominatorImage :
      ((gradedMap.gradedAddHom denominatorDegree denominator : targetGrading denominatorDegree) :
        targetRing) = gradedMap (denominator : sourceRing) := rfl
  simpa only [numeratorImage, denominatorImage, GradedRingHom.toRingHom_eq_toRingHom,
    GradedRingHom.coe_toRingHom] using
    Localization.localRingHom_mk sourcePrime targetPrime gradedMap primeCompatibility
      (numerator : sourceRing) ⟨(denominator : sourceRing), denominatorMem⟩

@[simp]
lemma degreePart.localRingHom_zeroEquiv (fraction : AtPrime sourceGrading sourcePrime) :
    degreePart.localRingHom gradedMap sourcePrime targetPrime primeCompatibility 0
        (degreePart.zeroEquiv fraction) =
      degreePart.zeroEquiv (HomogeneousLocalization.localRingHom gradedMap sourcePrime
        targetPrime primeCompatibility fraction) := by
  apply Subtype.ext
  exact (HomogeneousLocalization.val_localRingHom fraction).symm

end HomogeneousLocalization
