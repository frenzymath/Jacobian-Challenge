import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Unramified.Field

/-!
# Reducedness of standard smooth algebras

A flat, formally unramified, essentially finite type algebra over a domain embeds
into its reduced fraction-field base change. Standard smooth algebras over domains
are therefore reduced: they are étale over a polynomial ring over the base.
-/

open TensorProduct

/-- A flat, formally unramified, essentially finite type algebra over a domain is reduced. -/
theorem Algebra.FormallyUnramified.isReduced_of_isDomain (Base Target : Type*)
    [CommRing Base] [CommRing Target] [IsDomain Base] [Algebra Base Target]
    [Algebra.FormallyUnramified Base Target] [Algebra.EssFiniteType Base Target]
    [Module.Flat Base Target] : IsReduced Target := by
  have : IsReduced (FractionRing Base ⊗[Base] Target) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing Base)
      (FractionRing Base ⊗[Base] Target)
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight (R := Base) (A := FractionRing Base) (B := Target))
    (Algebra.TensorProduct.includeRight_injective
      (IsFractionRing.injective Base (FractionRing Base)))

/-- An étale algebra over a domain is reduced. -/
theorem Algebra.Etale.isReduced_of_isDomain (Base Target : Type*)
    [CommRing Base] [CommRing Target] [IsDomain Base] [Algebra Base Target]
    [Algebra.Etale Base Target] : IsReduced Target :=
  Algebra.FormallyUnramified.isReduced_of_isDomain Base Target

/-- The target of a standard smooth ring homomorphism from a domain is reduced. -/
theorem RingHom.IsStandardSmooth.isReduced_of_isDomain {Base Target : Type*}
    [CommRing Base] [CommRing Target] [IsDomain Base] {morphism : Base →+* Target}
    (standardSmooth : morphism.IsStandardSmooth) : IsReduced Target := by
  obtain ⟨variableCount, etaleMap, _, etaleMap_etale⟩ :=
    standardSmooth.exists_etale_mvPolynomial
  algebraize [etaleMap]
  exact Algebra.Etale.isReduced_of_isDomain (MvPolynomial (Fin variableCount) Base) Target

/-- A standard smooth algebra over a domain is reduced. -/
theorem Algebra.IsStandardSmooth.isReduced_of_isDomain (Base Target : Type*)
    [CommRing Base] [CommRing Target] [IsDomain Base] [Algebra Base Target]
    [Algebra.IsStandardSmooth Base Target] : IsReduced Target :=
  RingHom.IsStandardSmooth.isReduced_of_isDomain
    (RingHom.isStandardSmooth_algebraMap.mpr ‹_›)
