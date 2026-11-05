import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# Differentials of the function field of a smooth scheme

For an integral scheme smooth of relative dimension `n` over a field, the
differentials of its function field have dimension `n`. The proof uses an étale
polynomial chart at the generic point and localization of Kähler differentials.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory KaehlerDifferential

namespace AlgebraicGeometry

/-- The differentials of the function field of an integral smooth scheme have
dimension equal to the relative dimension. The coefficient ring may be identified
with the global sections of the spectrum of the ground field. -/
theorem finrank_kaehlerDifferential_functionField {baseField baseRing : Type u}
    [Field baseField] [CommRing baseRing] {scheme : Scheme.{u}} [IsIntegral scheme]
    (morphism : scheme ⟶ Spec (.of baseField)) (dimension : ℕ)
    [SmoothOfRelativeDimension dimension morphism] [Algebra baseRing scheme.functionField]
    (coefficients : baseRing ≃+* Γ(Spec (.of baseField), ⊤))
    (compatible : algebraMap baseRing scheme.functionField =
      (scheme.presheaf.germ ⊤ (genericPoint scheme) trivial).hom.comp
        (morphism.appTop.hom.comp coefficients.toRingHom)) :
    Module.finrank scheme.functionField Ω[scheme.functionField⁄baseRing] = dimension := by
  have : Nontrivial baseRing := coefficients.toEquiv.nontrivial
  obtain ⟨baseOpen, -, chartOpen, affineChart, generic_mem, image_mem, standardSmooth⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := dimension) (f := morphism) (genericPoint scheme)
  obtain rfl : baseOpen = ⊤ := eq_top_iff.mpr fun point _ ↦
    Subsingleton.elim (morphism (genericPoint scheme)) point ▸ image_mem generic_mem
  obtain ⟨chartMap, chartMap_coefficients, chartMap_etale⟩ :=
    standardSmooth.exists_etale_mvPolynomial
  have : Nonempty chartOpen := ⟨⟨genericPoint scheme, generic_mem⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen scheme chartOpen affineChart
  let polynomialEquiv : MvPolynomial (Fin dimension) baseRing ≃+*
      MvPolynomial (Fin dimension) Γ(Spec (.of baseField), ⊤) :=
    MvPolynomial.mapEquiv _ coefficients
  let : Algebra baseRing Γ(scheme, chartOpen) :=
    ((morphism.appLE ⊤ chartOpen image_mem).hom.comp coefficients.toRingHom).toAlgebra
  let : Algebra (MvPolynomial (Fin dimension) baseRing) Γ(scheme, chartOpen) :=
    (chartMap.comp polynomialEquiv.toRingHom).toAlgebra
  have : IsScalarTower baseRing (MvPolynomial (Fin dimension) baseRing)
      Γ(scheme, chartOpen) := .of_algebraMap_eq fun coefficient ↦ by
    simp [RingHom.algebraMap_toAlgebra, polynomialEquiv, ← chartMap_coefficients]
  have : Algebra.Etale (MvPolynomial (Fin dimension) baseRing) Γ(scheme, chartOpen) :=
    RingHom.Etale.respectsIso.2 _ _ chartMap_etale
  have : IsScalarTower baseRing Γ(scheme, chartOpen) scheme.functionField :=
    .of_algebraMap_eq fun coefficient ↦ by
      rw [compatible]
      simp [RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE]
  have differentialsEquiv := tensorKaehlerEquivOfFormallyEtale baseRing
    (MvPolynomial (Fin dimension) baseRing) Γ(scheme, chartOpen)
  have : Module.Free Γ(scheme, chartOpen) Ω[Γ(scheme, chartOpen)⁄baseRing] :=
    .of_equiv differentialsEquiv
  have chartDimension :
      Module.finrank Γ(scheme, chartOpen) Ω[Γ(scheme, chartOpen)⁄baseRing] = dimension := by
    rw [← differentialsEquiv.finrank_eq, Module.finrank_baseChange,
      Module.finrank_eq_card_basis (mvPolynomialBasis baseRing (Fin dimension)),
      Fintype.card_fin]
  rw [Module.finrank_of_isLocalizedModule_of_free scheme.functionField
    (nonZeroDivisors Γ(scheme, chartOpen))
    (KaehlerDifferential.map baseRing baseRing Γ(scheme, chartOpen) scheme.functionField),
    chartDimension]

end AlgebraicGeometry
