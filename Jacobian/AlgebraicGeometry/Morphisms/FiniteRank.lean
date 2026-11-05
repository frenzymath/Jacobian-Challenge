import Jacobian.RingTheory.Spectrum.Prime.Cardinality
import Jacobian.AlgebraicGeometry.GlobalSections.Rank
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Flat.LocallyFree

/-!
# Cardinality bounds for finite flat fibers

A fiber of a finite flat morphism has at most as many points as the rank.
The field case follows from the decomposition of a finite algebra into its
Artinian localizations, and the general case follows by residue-field base change.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- A morphism out of an empty scheme has rank zero everywhere. -/
lemma Scheme.Hom.finrank_eq_zero_of_isEmpty {source target : Scheme.{u}}
    (morphism : source ⟶ target) [IsEmpty source] (point : target) :
    morphism.finrank point = 0 := by
  obtain ⟨ring, neighborhood, _, prime, rfl⟩ := target.exists_Spec_apply_eq point
  rw [← Scheme.Hom.finrank_pullback_snd]
  have : IsEmpty ↥(pullback morphism neighborhood) :=
    Function.isEmpty (pullback.fst morphism neighborhood)
  let scalarMap : ring ⟶ CommRingCat.of PUnit.{u + 1} := CommRingCat.punitIsTerminal.from ring
  have factorization : pullback.snd morphism neighborhood =
      isInitialOfIsEmpty.to (Spec (CommRingCat.of PUnit.{u + 1})) ≫ Spec.map scalarMap :=
    isInitialOfIsEmpty.hom_ext _ _
  rw [factorization, finrank_comp_left_of_isIso,
    finrank_SpecMap_eq_finrank ((IsFinite.SpecMap_iff scalarMap).mp inferInstance)
      (Flat.SpecMap_iff.mp inferInstance)]
  let := scalarMap.hom.toAlgebra
  exact congrFun Module.rankAtStalk_eq_zero_of_subsingleton prime

/-- A scheme which is finite and flat over the spectrum of a field `K` is finite, with at most
as many points as the rank. -/
lemma Scheme.Hom.finite_and_card_le_finrank_of_field {K : Type u} [Field K]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K)) [IsFinite g] [Flat g] (z : Spec (.of K)) :
    Finite Z ∧ Nat.card Z ≤ g.finrank z := by
  have : IsAffine Z := isAffine_of_isAffineHom g
  let e := Scheme.homeoOfIso Z.isoSpec
  rw [← finrank_comp_left_of_isIso Z.isoSpec.inv, Nat.card_congr e.toEquiv,
    e.toEquiv.finite_iff]
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ g)
  have h₁ : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have h₂ : φ.hom.Flat := by
    rw [← Flat.SpecMap_iff, hφ]
    infer_instance
  rw [← hφ, finrank_SpecMap_eq_finrank h₁ h₂]
  algebraize [φ.hom]
  have : IsArtinianRing Γ(Z, ⊤) := .of_finite K Γ(Z, ⊤)
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap,
    Module.rankAtStalk_eq_finrank_of_free]
  exact ⟨inferInstanceAs (Finite (PrimeSpectrum Γ(Z, ⊤))),
    IsArtinianRing.card_primeSpectrum_le_finrank K Γ(Z, ⊤)⟩

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (y : Y) :
    IsFinite (f.fiberToSpecResidueField y) :=
  inferInstanceAs (IsFinite (pullback.snd f (Y.fromSpecResidueField y)))

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (y : Y) :
    Flat (f.fiberToSpecResidueField y) :=
  inferInstanceAs (Flat (pullback.snd f (Y.fromSpecResidueField y)))

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]

/-- A fibre of a finite flat morphism `f` over `y` has at most `f.finrank y` points: it is the
spectrum of an algebra of dimension `f.finrank y` over the residue field of `y`. -/
lemma Scheme.Hom.ncard_preimage_singleton_le_finrank (y : Y) :
    (f ⁻¹' {y}).ncard ≤ f.finrank y := by
  have h := (finite_and_card_le_finrank_of_field (K := Y.residueField y)
    (f.fiberToSpecResidueField y) (IsLocalRing.closedPoint _)).2
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr (f.fiberHomeo y).toEquiv]
  exact h.trans_eq ((finrank_pullback_snd f (Y.fromSpecResidueField y) _).trans
    (congrArg f.finrank (Y.fromSpecResidueField_apply y _)))


/-- Over a field the rank of a finite flat morphism is the dimension of its global sections. -/
lemma Scheme.Hom.finrank_eq_finrankΓ_of_field {K : Type u} [Field K]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K)) [IsFinite g] [Flat g]
    (z : Spec (.of K)) : g.finrank z = g.finrankΓ := by
  wlog hZ : ∃ A, Z = Spec A generalizing Z with inductionHypothesis
  · have : IsAffine Z := isAffine_of_isAffineHom g
    have equality := inductionHypothesis (Z.isoSpec.inv ≫ g) ⟨_, rfl⟩
    rw [Scheme.Hom.finrank_comp_left_of_isIso] at equality
    exact equality.trans (Scheme.Hom.finrankΓ_eq_of_iso (Z.isoSpec.inv ≫ g) g
      Z.isoSpec.symm (Iso.refl _) (by simp))
  obtain ⟨A, rfl⟩ := hZ
  obtain ⟨scalarMap, rfl⟩ := Spec.map_surjective g
  have finiteMap : scalarMap.hom.Finite := (IsFinite.SpecMap_iff scalarMap).mp inferInstance
  have flatMap : scalarMap.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank finiteMap flatMap]
  algebraize [scalarMap.hom]
  have equality : scalarMap = CommRingCat.ofHom (algebraMap K A) := rfl
  conv_rhs => rw [equality, Scheme.Hom.finrankΓ_SpecMap]
  rw [← RingHom.algebraMap_toAlgebra scalarMap.hom, RingHom.finrank_algebraMap,
    Module.rankAtStalk_eq_finrank_of_free]
  rfl

end AlgebraicGeometry
