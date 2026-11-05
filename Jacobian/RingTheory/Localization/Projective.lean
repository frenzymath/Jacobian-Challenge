import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.LocalRing.Module

/-!
# Local freeness of finite projective modules

A finite projective module becomes free after inverting an element outside a
given prime. Freeness persists on smaller basic opens, allowing finitely many
modules to be trivialized on a common neighbourhood.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open TensorProduct

namespace Module

variable {baseRing : Type u} [CommRing baseRing]

/-- Freeness after inverting `denominator` persists after inverting a multiple. -/
lemma free_away_tensor_of_dvd (moduleType : Type u) [AddCommGroup moduleType] [Module baseRing moduleType]
    {denominator multiple : baseRing} (divides : denominator ∣ multiple)
    [Module.Free (Localization.Away denominator) (Localization.Away denominator ⊗[baseRing] moduleType)] :
    Module.Free (Localization.Away multiple) (Localization.Away multiple ⊗[baseRing] moduleType) := by
  obtain ⟨factor, rfl⟩ := divides
  let : Algebra (Localization.Away denominator) (Localization.Away (denominator * factor)) :=
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away denominator)
      denominator factor).toAlgebra
  have : IsScalarTower baseRing (Localization.Away denominator)
      (Localization.Away (denominator * factor)) :=
    IsScalarTower.of_algebraMap_eq fun scalar ↦
      (IsLocalization.Away.awayToAwayRight_eq denominator factor scalar).symm
  exact Module.Free.of_equiv (AlgebraTensorModule.cancelBaseChange baseRing
    (Localization.Away denominator) (Localization.Away (denominator * factor))
    (Localization.Away (denominator * factor)) moduleType)

/-- A finite projective module is free on a basic neighbourhood of every prime. -/
lemma exists_free_away_tensor (moduleType : Type u) [AddCommGroup moduleType] [Module baseRing moduleType]
    [Module.Projective baseRing moduleType] [Module.Finite baseRing moduleType]
    (prime : Ideal baseRing) [prime.IsPrime] :
    ∃ denominator ∉ prime,
      Module.Free (Localization.Away denominator) (Localization.Away denominator ⊗[baseRing] moduleType) := by
  have := Module.finitePresentation_of_projective baseRing moduleType
  have : Module.Free (Localization.AtPrime prime) (LocalizedModule prime.primeCompl moduleType) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨denominator, not_mem, free, -⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers prime.primeCompl
      (LocalizedModule.mkLinearMap prime.primeCompl moduleType) (Localization.AtPrime prime)
  exact ⟨denominator, not_mem,
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (.powers denominator) moduleType)⟩

end Module
