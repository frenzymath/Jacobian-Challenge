import Jacobian.AlgebraicGeometry.Hilbert.BasisChart
import Jacobian.RingTheory.MvPolynomial.QuotientSpan
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Open basis loci for Hilbert charts

The annihilator of the cokernel of a polynomial family cuts out its spanning
locus. In a finite locally free quotient of fixed rank, these are basis loci,
and the loci attached to monomial families cover the base spectrum.
-/

noncomputable section

universe u

open AlgebraicGeometry

namespace MvPolynomial

variable {indeterminates coefficientRing : Type u} [CommRing coefficientRing]

/-- The annihilator measuring the failure of a polynomial family to span a quotient. -/
def basisCokernelAnnihilator (ideal : Ideal (MvPolynomial indeterminates coefficientRing))
    {indices : Type*} (family : indices → MvPolynomial indeterminates coefficientRing) :
    Ideal coefficientRing :=
  Module.annihilator coefficientRing ((MvPolynomial indeterminates coefficientRing ⧸ ideal) ⧸
    Submodule.span coefficientRing (Set.range fun index ↦ Ideal.Quotient.mk ideal (family index)))

/-- The open locus where the images of a polynomial family span the quotient. -/
def basisLocus (ideal : Ideal (MvPolynomial indeterminates coefficientRing)) {indices : Type*}
    (family : indices → MvPolynomial indeterminates coefficientRing) :
    TopologicalSpace.Opens (PrimeSpectrum coefficientRing) :=
  ⟨(PrimeSpectrum.zeroLocus (basisCokernelAnnihilator ideal family : Set coefficientRing))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- A prime belongs to the basis locus precisely when it does not contain the annihilator. -/
lemma mem_basisLocus_iff (ideal : Ideal (MvPolynomial indeterminates coefficientRing))
    {indices : Type*} (family : indices → MvPolynomial indeterminates coefficientRing)
    (prime : PrimeSpectrum coefficientRing) :
    prime ∈ basisLocus ideal family ↔ ¬ basisCokernelAnnihilator ideal family ≤ prime.asIdeal :=
  Iff.rfl

/-- A family spans after base change exactly when its cokernel annihilator becomes the unit ideal. -/
lemma span_eq_top_iff_map_basisCokernelAnnihilator
    {targetRing : Type*} [CommRing targetRing] (scalarMap : coefficientRing →+* targetRing)
    (ideal : Ideal (MvPolynomial indeterminates coefficientRing))
    [Module.Finite coefficientRing (MvPolynomial indeterminates coefficientRing ⧸ ideal)]
    {indices : Type*} (family : indices → MvPolynomial indeterminates coefficientRing) :
    Submodule.span targetRing (Set.range fun index ↦
      Ideal.Quotient.mk (ideal.map (map scalarMap)) (map scalarMap (family index))) = ⊤ ↔
      (basisCokernelAnnihilator ideal family).map scalarMap = ⊤ :=
  span_range_mk_map_eq_top_iff scalarMap ideal family

/-- For a finite locally free quotient of rank `rank`, a family of that size is a basis
exactly when its cokernel annihilator is the unit ideal. -/
lemma isQuotientBasis_iff_basisCokernelAnnihilator_eq_top
    (ideal : Ideal (MvPolynomial indeterminates coefficientRing))
    [Module.FinitePresentation coefficientRing (MvPolynomial indeterminates coefficientRing ⧸ ideal)]
    [Module.Flat coefficientRing (MvPolynomial indeterminates coefficientRing ⧸ ideal)]
    {rank : ℕ} (family : Fin rank → MvPolynomial indeterminates coefficientRing)
    (constantRank : ∀ prime, Module.rankAtStalk (R := coefficientRing)
      (MvPolynomial indeterminates coefficientRing ⧸ ideal) prime = rank) :
    IsQuotientBasis family ideal ↔ basisCokernelAnnihilator ideal family = ⊤ := by
  have spanning : Submodule.span coefficientRing
      (Set.range fun index ↦ Ideal.Quotient.mk ideal (family index)) = ⊤ ↔
        basisCokernelAnnihilator ideal family = ⊤ := by
    rw [basisCokernelAnnihilator, Module.annihilator_eq_top_iff,
      Submodule.Quotient.subsingleton_iff]
  constructor
  · intro basis
    apply spanning.mp
    simpa [map_id] using basis.2
  · intro annihilator
    have spanEquality := spanning.mpr annihilator
    have independence := linearIndependent_of_span_eq_top_of_rankAtStalk
      (fun index ↦ Ideal.Quotient.mk ideal (family index)) spanEquality constantRank
    simpa [IsQuotientBasis, map_id] using And.intro independence spanEquality

/-- Every prime is contained in a basis locus defined by a monomial family. -/
lemma exists_mem_monomial_basisLocus (ideal : Ideal (MvPolynomial indeterminates coefficientRing))
    [Module.FinitePresentation coefficientRing (MvPolynomial indeterminates coefficientRing ⧸ ideal)]
    [Module.Flat coefficientRing (MvPolynomial indeterminates coefficientRing ⧸ ideal)]
    {rank : ℕ} (prime : PrimeSpectrum coefficientRing)
    (rankEquality : Module.rankAtStalk (MvPolynomial indeterminates coefficientRing ⧸ ideal)
      prime = rank) :
    ∃ monomials : Fin rank → (indeterminates →₀ ℕ),
      prime ∈ basisLocus ideal (fun index ↦ monomial (monomials index) 1) :=
  exists_monomials_annihilator_not_le ideal prime rankEquality

/-- Monomial basis loci cover the spectrum of a constant-rank finite locally free quotient. -/
lemma iSup_monomial_basisLocus_eq_top (ideal : Ideal (MvPolynomial indeterminates coefficientRing))
    [Module.FinitePresentation coefficientRing (MvPolynomial indeterminates coefficientRing ⧸ ideal)]
    [Module.Flat coefficientRing (MvPolynomial indeterminates coefficientRing ⧸ ideal)]
    {rank : ℕ} (constantRank : ∀ prime, Module.rankAtStalk (R := coefficientRing)
      (MvPolynomial indeterminates coefficientRing ⧸ ideal) prime = rank) :
    (⨆ monomials : Fin rank → (indeterminates →₀ ℕ),
      basisLocus ideal (fun index ↦ monomial (monomials index) 1)) = ⊤ := by
  apply top_unique
  intro prime membership
  obtain ⟨monomials, membership⟩ := exists_mem_monomial_basisLocus ideal prime (constantRank prime)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨monomials, membership⟩

end MvPolynomial
