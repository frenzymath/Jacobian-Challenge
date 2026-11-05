import Jacobian.RingTheory.MvPolynomial.QuotientBasis
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Limits.Over

/-!
# Affine charts for polynomial quotients with a prescribed basis

The spectrum of the universal quotient-basis ring classifies polynomial ideals
whose quotients have a specified basis. The classification holds over every test
scheme and commutes with pullback. These spectra are the affine basis charts of
the Hilbert functor of points of affine space.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Hilbert

variable {indeterminates : Type schemeUniverse} {base : Scheme.{schemeUniverse}} [IsAffine base]
  {rank : ℕ}

/-- The affine scheme parametrizing polynomial quotients with the prescribed basis. -/
abbrev basisChart (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)) : Over base :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap Γ(base, ⊤) (MvPolynomial.QuotientBasisRing family))) ≫ base.isoSpec.inv)

/-- The structure morphism of a basis chart is induced by its coefficient algebra. -/
lemma basisChart_hom (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)) :
    (basisChart family).hom = Spec.map (CommRingCat.ofHom
      (algebraMap Γ(base, ⊤) (MvPolynomial.QuotientBasisRing family))) ≫ base.isoSpec.inv :=
  rfl

instance (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)) :
    IsAffine (basisChart family).left :=
  inferInstanceAs (IsAffine (Spec _))

private lemma isoSpec_inv_appTop (scheme : Scheme.{schemeUniverse}) [IsAffine scheme] :
    scheme.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(scheme, ⊤)).inv := by
  rw [← Iso.hom_comp_eq_id, ← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom,
    ← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]

/-- The coordinate-ring map of a morphism to a basis chart. -/
def basisChartRingHom {family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)}
    {test : Over base} (chartMap : test ⟶ basisChart family) :
    MvPolynomial.QuotientBasisRing family →+* Γ(test.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.QuotientBasisRing family))).inv ≫
    chartMap.left.appTop).hom

/-- A chart morphism induces a map of algebras over the base ring. -/
lemma basisChartRingHom_comp_algebraMap
    {family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)} {test : Over base}
    (chartMap : test ⟶ basisChart family) :
    (basisChartRingHom chartMap).comp
        (algebraMap Γ(base, ⊤) (MvPolynomial.QuotientBasisRing family)) =
      test.hom.appTop.hom := by
  have compatibility : CommRingCat.ofHom
      (algebraMap Γ(base, ⊤) (MvPolynomial.QuotientBasisRing family)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.QuotientBasisRing family))).inv ≫
        chartMap.left.appTop = (chartMap.left ≫ (basisChart family).hom).appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, basisChart_hom, Scheme.Hom.comp_appTop,
      Scheme.Hom.comp_appTop, isoSpec_inv_appTop, Category.assoc]
    rfl
  rw [← Over.w chartMap, ← compatibility]
  rfl

/-- Morphisms to a basis chart are determined by their coordinate-ring maps. -/
lemma basisChartRingHom_injective
    {family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)} {test : Over base} :
    Function.Injective (basisChartRingHom (family := family) (test := test)) := by
  intro firstMap secondMap equality
  refine Over.OverMorphism.ext (ext_of_isAffine ((cancel_epi
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.QuotientBasisRing family))).inv).1 ?_))
  exact CommRingCat.hom_ext equality

/-- A compatible algebra map defines a morphism to the basis chart. -/
lemma exists_basisChartRingHom_eq
    {family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)} {test : Over base}
    (classifier : MvPolynomial.QuotientBasisRing family →+* Γ(test.left, ⊤))
    (compatibility : classifier.comp
      (algebraMap Γ(base, ⊤) (MvPolynomial.QuotientBasisRing family)) =
        test.hom.appTop.hom) :
    ∃ chartMap : test ⟶ basisChart family, basisChartRingHom chartMap = classifier := by
  have scalarEquality : CommRingCat.ofHom
      (algebraMap Γ(base, ⊤) (MvPolynomial.QuotientBasisRing family)) ≫
      (CommRingCat.ofHom classifier : CommRingCat.of _ ⟶ Γ(test.left, ⊤)) =
        test.hom.appTop :=
    CommRingCat.hom_ext compatibility
  have overEquality : (test.left.toSpecΓ ≫ Spec.map
      (CommRingCat.ofHom classifier : CommRingCat.of _ ⟶ Γ(test.left, ⊤))) ≫
        (basisChart family).hom = test.hom := by
    rw [basisChart_hom, Category.assoc, ← Spec.map_comp_assoc, scalarEquality,
      ← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  refine ⟨Over.homMk _ overEquality, ?_⟩
  simp only [basisChartRingHom, Over.homMk_left, Scheme.Hom.comp_appTop,
    Scheme.toSpecΓ_appTop]
  rw [Scheme.ΓSpecIso_naturality (S := Γ(test.left, ⊤)) (CommRingCat.ofHom classifier),
    Iso.inv_hom_id_assoc, CommRingCat.hom_ofHom]

/-- The coordinate-ring classification commutes with changing the test scheme. -/
lemma basisChartRingHom_comp
    {family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)} {test smallerTest : Over base}
    (restriction : smallerTest ⟶ test) (chartMap : test ⟶ basisChart family) :
    basisChartRingHom (restriction ≫ chartMap) =
      restriction.left.appTop.hom.comp (basisChartRingHom chartMap) := by
  rw [basisChartRingHom, basisChartRingHom, Over.comp_left, Scheme.Hom.comp_appTop,
    ← Category.assoc, CommRingCat.hom_comp]

/-- Morphisms to a basis chart are algebra maps from its coordinate ring. -/
def basisChartAlgHomEquiv (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
    (test : Over base) :
    letI := test.hom.appTop.hom.toAlgebra
    (test ⟶ basisChart family) ≃
      (MvPolynomial.QuotientBasisRing family →ₐ[Γ(base, ⊤)] Γ(test.left, ⊤)) := by
  letI := test.hom.appTop.hom.toAlgebra
  refine Equiv.ofBijective
    (fun chartMap ↦ ⟨basisChartRingHom chartMap, fun scalar ↦
      RingHom.congr_fun (basisChartRingHom_comp_algebraMap chartMap) scalar⟩) ⟨?_, ?_⟩
  · intro firstMap secondMap equality
    exact basisChartRingHom_injective (congrArg AlgHom.toRingHom equality)
  · intro classifier
    obtain ⟨chartMap, equality⟩ := exists_basisChartRingHom_eq classifier.toRingHom
      (RingHom.ext classifier.commutes)
    refine ⟨chartMap, ?_⟩
    exact AlgHom.ext fun element ↦ RingHom.congr_fun equality element

/-- The universal ideal classifies all polynomial quotients with the given basis. -/
def basisChartEquiv (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
    (test : Over base) :
    letI := test.hom.appTop.hom.toAlgebra
    (test ⟶ basisChart family) ≃
      {ideal : Ideal (MvPolynomial indeterminates Γ(test.left, ⊤)) //
        MvPolynomial.IsQuotientBasis family ideal} := by
  letI := test.hom.appTop.hom.toAlgebra
  exact (basisChartAlgHomEquiv family test).trans
    (MvPolynomial.quotientBasisEquiv family Γ(test.left, ⊤))

/-- A chart morphism pulls back the universal ideal by its coordinate-ring map. -/
lemma basisChartEquiv_apply (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
    {test : Over base} (chartMap : test ⟶ basisChart family) :
    (basisChartEquiv family test chartMap).1 =
      (MvPolynomial.quotientBasisIdeal family).map
        (MvPolynomial.map (basisChartRingHom chartMap)) :=
  rfl

/-- The universal family is compatible with pullback of chart morphisms. -/
lemma basisChartEquiv_comp (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
    {test smallerTest : Over base} (restriction : smallerTest ⟶ test)
    (chartMap : test ⟶ basisChart family) :
    (basisChartEquiv family smallerTest (restriction ≫ chartMap)).1 =
      ((basisChartEquiv family test chartMap).1).map
        (MvPolynomial.map restriction.left.appTop.hom) := by
  rw [basisChartEquiv_apply, basisChartEquiv_apply, basisChartRingHom_comp, Ideal.map_map]
  congr 1
  exact RingHom.ext fun polynomial ↦
    (MvPolynomial.map_map (basisChartRingHom chartMap)
      restriction.left.appTop.hom polynomial).symm

/-- The presheaf of polynomial ideals whose quotient has the prescribed basis. -/
def basisQuotientPresheaf (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)) :
    (Over base)ᵒᵖ ⥤ Type schemeUniverse where
  obj test :=
    letI := test.unop.hom.appTop.hom.toAlgebra
    {ideal : Ideal (MvPolynomial indeterminates Γ(test.unop.left, ⊤)) //
      MvPolynomial.IsQuotientBasis family ideal}
  map restriction := TypeCat.ofHom fun ideal ↦
    basisChartEquiv family _ (restriction.unop ≫ (basisChartEquiv family _).symm ideal)
  map_id test := by
    ext ideal
    simp
  map_comp firstRestriction secondRestriction := by
    ext ideal
    simp [Category.assoc]

/-- The presheaf acts by extending ideals along pullback of global functions. -/
lemma basisQuotientPresheaf_map_val
    (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤))
    {test smallerTest : Over base} (restriction : smallerTest ⟶ test)
    (ideal : (basisQuotientPresheaf family).obj (op test)) :
    ((basisQuotientPresheaf family).map restriction.op ideal).1 =
      ideal.1.map (MvPolynomial.map restriction.left.appTop.hom) := by
  change (basisChartEquiv family smallerTest
    (restriction ≫ (basisChartEquiv family test).symm ideal)).1 = _
  rw [basisChartEquiv_comp, Equiv.apply_symm_apply]

/-- The spectrum of the universal quotient-basis ring represents the basis chart. -/
def basisQuotientPresheafRepresentableBy
    (family : Fin rank → MvPolynomial indeterminates Γ(base, ⊤)) :
    (basisQuotientPresheaf family).RepresentableBy (basisChart family) where
  homEquiv := basisChartEquiv family _
  homEquiv_comp restriction chartMap := by
    change basisChartEquiv family _ (restriction ≫ chartMap) =
      basisChartEquiv family _
        (restriction ≫ (basisChartEquiv family _).symm (basisChartEquiv family _ chartMap))
    rw [Equiv.symm_apply_apply]

end AlgebraicGeometry.Hilbert
