import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Gluing
import Jacobian.AlgebraicGeometry.Modules.TensorPower
import Jacobian.AlgebraicGeometry.Modules.TensorSection
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.FreeGenerator

/-!
# Tensor products and powers of twisting sheaves

Degree-one standard opens carry the free generators given by powers of their
homogeneous coordinates. Matching transition functions identify tensor products
of twists with the twist by the sum of their degrees.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace HomogeneousLocalization

namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist
open Scheme.Modules

variable {gradedRing gradedPieceType : Type u} [CommRing gradedRing] [SetLike gradedPieceType gradedRing] [AddSubgroupClass gradedPieceType gradedRing]
variable (grading : ℕ → gradedPieceType) [GradedRing grading] (twistDegree : ℤ)

section TensorObj

open MonoidalCategory Scheme.Modules

variable {grading} {homogeneousElement otherHomogeneousElement : gradedRing}

/-- A power of a homogeneous element of degree `1` is homogeneous of degree its exponent. -/
lemma pow_mem_of_mem_one (hf : homogeneousElement ∈ grading 1) (exponent : ℕ) : homogeneousElement ^ exponent ∈ grading exponent := by
  simpa using SetLike.pow_mem_graded exponent hf

/-- A power of `f` avoids every point of `D₊(f)`. -/
lemma pow_mem_primeCompl (point : Proj.basicOpen grading homogeneousElement) (exponent : ℕ) :
    homogeneousElement ^ exponent ∈ point.1.asHomogeneousIdeal.toIdeal.primeCompl :=
  fun compatibility ↦ point.2 (point.1.isPrime.mem_of_pow_mem _ compatibility)

variable (hf : homogeneousElement ∈ grading 1)

/-- The value at a point of `D₊(f)` of the section `fᵐ` of `𝒪(m)`, for `f` homogeneous of
degree `1`: the fraction `f ^ m / 1` if `m ≥ 0`, and `1 / f ^ (-m)` if `m ≤ 0`. -/
def twistPowFun (point : Proj.basicOpen grading homogeneousElement) : fiber grading twistDegree point.1 :=
  degreePart.mk (m := twistDegree) ⟨homogeneousElement ^ twistDegree.toNat, pow_mem_of_mem_one hf _⟩
    ⟨homogeneousElement ^ (-twistDegree).toNat, pow_mem_of_mem_one hf _⟩ (pow_mem_primeCompl point _) (by omega)

/-- The section `fᵐ` of `𝒪(m)` over `D₊(f)`, for `f` homogeneous of degree `1`. -/
def twistPowSection : Γ(twist grading twistDegree, Proj.basicOpen grading homogeneousElement) :=
  ⟨twistPowFun twistDegree hf, isLocallyFraction_mk (by omega) ⟨homogeneousElement ^ twistDegree.toNat, pow_mem_of_mem_one hf _⟩
    ⟨homogeneousElement ^ (-twistDegree).toNat, pow_mem_of_mem_one hf _⟩ (pow_mem_primeCompl · _)⟩

/-- The value of the section `fᵐ` of `𝒪(m)` at a point of `D₊(f)`. -/
lemma val_twistPowSection_apply (point : Proj.basicOpen grading homogeneousElement) :
    ((twistPowSection twistDegree hf).1 point : Localization.AtPrime point.1.asHomogeneousIdeal.toIdeal) =
      Localization.mk (homogeneousElement ^ twistDegree.toNat) ⟨homogeneousElement ^ (-twistDegree).toNat, pow_mem_primeCompl point _⟩ :=
  degreePart.coe_mk _ _ _ (by omega)

/-- `fᵐ fⁿ = fᵐ⁺ⁿ` at every point of `D₊(f)`. -/
lemma val_twistPowSection_mul {exponent power : ℤ} (compatibility : twistDegree + exponent = power) (point : Proj.basicOpen grading homogeneousElement) :
    ((twistPowSection twistDegree hf).1 point : Localization.AtPrime point.1.asHomogeneousIdeal.toIdeal) *
        (twistPowSection exponent hf).1 point = (twistPowSection power hf).1 point := by
  rw [val_twistPowSection_apply, val_twistPowSection_apply, val_twistPowSection_apply,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, ← pow_add]
  congr 1
  omega

/-- `f⁰ = 1` at every point of `D₊(f)`. -/
lemma val_twistPowSection_zero (point : Proj.basicOpen grading homogeneousElement) :
    ((twistPowSection 0 hf).1 point : Localization.AtPrime point.1.asHomogeneousIdeal.toIdeal) = 1 := by
  rw [val_twistPowSection_apply]
  simp

/-- **The section `fᵐ` is a free generator of `𝒪(m)` on `D₊(f)`**, with inverse `f⁻ᵐ`. -/
lemma isFreeGenerator_twistPowSection : IsFreeGenerator (twistPowSection twistDegree hf) :=
  isFreeGenerator_twist_of_mul_eq_one _ (twistPowSection (-twistDegree) hf) fun point ↦
    (val_twistPowSection_mul twistDegree hf (add_neg_cancel twistDegree) point).trans (val_twistPowSection_zero hf point)

/-- If `fᵐ = c • gᵐ` and `fⁿ = d • gⁿ` on an open `W ⊆ D₊(f) ∩ D₊(g)`, then
`fᵐ⁺ⁿ = (c d) • gᵐ⁺ⁿ` on `W`. -/
lemma twistPowSection_map_eq_mul_smul (hg : otherHomogeneousElement ∈ grading 1) {firstDegree secondDegree : ℤ} {smallestOpen : (Proj grading).Opens}
    (hWf : smallestOpen ≤ Proj.basicOpen grading homogeneousElement) (hWg : smallestOpen ≤ Proj.basicOpen grading otherHomogeneousElement) {comparison degree : Γ(Proj grading, smallestOpen)}
    (hc : comparison • (twist grading firstDegree).presheaf.map (homOfLE hWg).op (twistPowSection firstDegree hg) =
      (twist grading firstDegree).presheaf.map (homOfLE hWf).op (twistPowSection firstDegree hf))
    (hd : degree • (twist grading secondDegree).presheaf.map (homOfLE hWg).op (twistPowSection secondDegree hg) =
      (twist grading secondDegree).presheaf.map (homOfLE hWf).op (twistPowSection secondDegree hf)) :
    (comparison * degree) • (twist grading (firstDegree + secondDegree)).presheaf.map (homOfLE hWg).op (twistPowSection (firstDegree + secondDegree) hg) =
      (twist grading (firstDegree + secondDegree)).presheaf.map (homOfLE hWf).op (twistPowSection (firstDegree + secondDegree) hf) := by
  refine Subtype.ext (funext fun point ↦ Subtype.ext ?_)
  have hc' := congrArg (fun sectionValue : Γ(twist grading firstDegree, smallestOpen) ↦
    (sectionValue.1 point : Localization.AtPrime point.1.asHomogeneousIdeal.toIdeal)) hc
  have hd' := congrArg (fun sectionValue : Γ(twist grading secondDegree, smallestOpen) ↦
    (sectionValue.1 point : Localization.AtPrime point.1.asHomogeneousIdeal.toIdeal)) hd
  dsimp only at hc' hd'
  rw [coe_twist_smul_apply, twist_presheaf_map_apply, twist_presheaf_map_apply] at hc' hd'
  change ((comparison * degree).1 point).val * ((twistPowSection (firstDegree + secondDegree) hg).1 ⟨point.1, hWg point.2⟩ :
      Localization.AtPrime point.1.asHomogeneousIdeal.toIdeal) =
    ((twistPowSection (firstDegree + secondDegree) hf).1 ⟨point.1, hWf point.2⟩ :
      Localization.AtPrime point.1.asHomogeneousIdeal.toIdeal)
  rw [← val_twistPowSection_mul firstDegree hf rfl, ← val_twistPowSection_mul firstDegree hg rfl, ← hc', ← hd']
  change ((comparison.1 point * degree.1 point)).val * _ = _
  rw [HomogeneousLocalization.val_mul]
  ring

variable (grading) in
/-- **Twists and tensor products**: when the basic open sets `D₊(f)` of the homogeneous elements
`f` of degree `1` cover `Proj 𝒜`, `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)`. On `D₊(f)` both sides are free, with
free generators `fᵃ ⊗ fᵇ` and `fᵃ⁺ᵇ`, and the transition functions agree: if `fᵃ = c • gᵃ` and
`fᵇ = d • gᵇ` on `D₊(f) ∩ D₊(g)`, then `fᵃ ⊗ fᵇ = (c d) • gᵃ ⊗ gᵇ` and `fᵃ⁺ᵇ = (c d) • gᵃ⁺ᵇ`.
The two modules are then isomorphic by `Scheme.Modules.nonempty_iso_of_isFreeGenerator`.
 -/
theorem nonempty_tensorObj_twist_iso (compatibility : ∀ point : Proj grading, ∃ homogeneousElement ∈ grading 1, point ∈ Proj.basicOpen grading homogeneousElement)
    (firstDegree secondDegree : ℤ) : Nonempty (twist grading firstDegree ⊗ twist grading secondDegree ≅ twist grading (firstDegree + secondDegree)) := by
  let openSubset (index : {homogeneousElement : gradedRing // homogeneousElement ∈ grading 1}) : (Proj grading).Opens := Proj.basicOpen grading index.1
  have hU : ⨆ index, openSubset index = ⊤ := eq_top_iff.mpr fun point _ ↦ by
    obtain ⟨homogeneousElement, hf, hx⟩ := compatibility point
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨homogeneousElement, hf⟩, hx⟩
  refine (nonempty_iso_of_isFreeGenerator
    (moduleSheaf := twist grading (firstDegree + secondDegree)) hU
    (fun index ↦ isFreeGenerator_twistPowSection (firstDegree + secondDegree) index.2)
    (secondGenerators := fun index ↦
      tmulSection (twistPowSection firstDegree index.2) (twistPowSection secondDegree index.2)) ?_
    fun index ↦ (isFreeGenerator_twistPowSection firstDegree index.2).tmulSection
      (isFreeGenerator_twistPowSection secondDegree index.2)).map Iso.symm
  rintro ⟨homogeneousElement, hf⟩ ⟨otherHomogeneousElement, hg⟩ smallestOpen hi hj α β hαβ
  obtain ⟨comparison, hc⟩ := ((isFreeGenerator_twistPowSection firstDegree hg).map hj).exists_smul_eq
    ((twist grading firstDegree).presheaf.map (homOfLE hi).op (twistPowSection firstDegree hf))
  obtain ⟨degree, hd⟩ := ((isFreeGenerator_twistPowSection secondDegree hg).map hj).exists_smul_eq
    ((twist grading secondDegree).presheaf.map (homOfLE hi).op (twistPowSection secondDegree hf))
  have hcd := twistPowSection_map_eq_mul_smul hf hg hi hj hc hd
  have hβ : α * (comparison * degree) = β := by
    refine ((isFreeGenerator_twistPowSection (firstDegree + secondDegree) hg).map hj).smul_left_injective ?_
    dsimp only
    rw [mul_smul, hcd]
    exact hαβ
  change α • (twist grading firstDegree ⊗ twist grading secondDegree).presheaf.map (homOfLE hi).op (tmulSection _ _) =
    β • (twist grading firstDegree ⊗ twist grading secondDegree).presheaf.map (homOfLE hj).op (tmulSection _ _)
  rw [tmulSection_map, tmulSection_map, ← hc, ← hd, smul_tmulSection, tmulSection_smul,
    smul_smul, smul_smul, ← hβ, mul_assoc]

end TensorObj

/-- Tensor powers of the degree-one twist are the corresponding natural twists. -/
theorem nonempty_tensorPow_twist_one_iso
    (compatibility : ∀ point : Proj grading, ∃ homogeneousElement ∈ grading 1, point ∈ Proj.basicOpen grading homogeneousElement) (exponent : ℕ) :
    Nonempty ((twist grading 1).tensorPow exponent ≅ twist grading (exponent : ℤ)) := by
  induction exponent with
  | zero => exact ⟨unitIsoTwistZero⟩
  | succ exponent inductionHypothesis =>
    obtain ⟨previousIso⟩ := inductionHypothesis
    obtain ⟨productIso⟩ := nonempty_tensorObj_twist_iso grading compatibility 1 (exponent : ℤ)
    exact ⟨(Iso.refl _ ⊗ᵢ previousIso) ≪≫ productIso ≪≫
      eqToIso (congrArg (twist grading) (by omega : 1 + (exponent : ℤ) = ↑(exponent + 1)))⟩

/-- The negative twist is inverse to the corresponding tensor power of the degree-one twist. -/
theorem nonempty_tensorPow_twist_one_tensor_neg_iso
    (compatibility : ∀ point : Proj grading, ∃ homogeneousElement ∈ grading 1,
      point ∈ Proj.basicOpen grading homogeneousElement) (exponent : ℕ) :
    Nonempty ((twist grading 1).tensorPow exponent ⊗
      twist grading (-(exponent : ℤ)) ≅ Scheme.Modules.unit (Proj grading)) := by
  obtain ⟨powerIso⟩ := nonempty_tensorPow_twist_one_iso grading compatibility exponent
  obtain ⟨productIso⟩ := nonempty_tensorObj_twist_iso grading compatibility
    (exponent : ℤ) (-(exponent : ℤ))
  have degreeEquality : (exponent : ℤ) + -(exponent : ℤ) = 0 := add_neg_cancel _
  exact ⟨(powerIso ⊗ᵢ Iso.refl _) ≪≫ productIso ≪≫
    eqToIso (congrArg (twist grading) degreeEquality) ≪≫
    (unitIsoTwistZero (𝒜 := grading)).symm⟩

end AlgebraicGeometry.Proj
