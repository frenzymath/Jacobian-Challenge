import Jacobian.RingTheory.FinitePresentation.Models
import Jacobian.RingTheory.Flat.Locus
import Jacobian.RingTheory.TensorProduct.FiniteGeneration
import Jacobian.RingTheory.TensorProduct.Pushout
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Finite presentation along faithfully flat source maps

A faithfully flat algebra of finite presentation descends to a faithfully flat
model over a finitely generated ring. Consequently, if `R → A → B` are algebra
maps with `B` finitely presented over `R` and faithfully flat and finitely
presented over `A`, then `A` is finitely presented over `R`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

section FaithfullyFlatModel

universe u

open PrimeSpectrum

namespace Algebra.FinitePresentation

variable {A₀ A B₀ : Type u} [CommRing A₀] [CommRing A] [CommRing B₀] [Algebra A₀ A]
  [Algebra A₀ B₀]

/-- Let `R₁ ≤ R` be subalgebras of an `A₀`-algebra `A` and `U` a set of points of
`Spec (R₁ ⊗[A₀] B₀)` at which `R₁ ⊗[A₀] B₀` is flat over `R₁`. If the basic opens contained in
`U` generate the unit ideal of `R ⊗[A₀] B₀`, then `R ⊗[A₀] B₀` is flat over `R`. -/
lemma flat_tensorProduct_of_map_eq_top {R₁ R : Subalgebra A₀ A} (h : R₁ ≤ R)
    (U : Set (PrimeSpectrum (R₁ ⊗[A₀] B₀)))
    (hU : ∀ q ∈ U, Module.Flat R₁ (Localization.AtPrime q.asIdeal))
    (hI : (Ideal.span {f | (basicOpen f : Set _) ⊆ U}).map
      (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id A₀ B₀)) = ⊤) :
    Module.Flat R (R ⊗[A₀] B₀) := by
  have H (Q : Ideal (R ⊗[A₀] B₀)) [Q.IsPrime] : Module.Flat R (Localization.AtPrime Q) := by
    obtain ⟨f, hfU, hfP⟩ : ∃ f, (basicOpen f : Set _) ⊆ U ∧ f ∉ Q.comap
        (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id A₀ B₀)).toRingHom := by
      by_contra! H
      have hle : Ideal.span {f | (basicOpen f : Set _) ⊆ U} ≤
          Q.comap (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id A₀ B₀)) :=
        Ideal.span_le.mpr fun f hf ↦ H f hf
      have := Ideal.map_le_iff_le_comap.mpr hle
      rw [hI] at this
      exact Ideal.IsPrime.ne_top ‹_› (top_le_iff.mp this)
    have hP := hU ⟨_, Ideal.comap_isPrime _ Q⟩ (hfU hfP)
    exact Module.Flat.localization_tensorProduct_map (Subalgebra.inclusion h) Q _ rfl hP
  exact Module.flat_of_isLocalized_maximal (R ⊗[A₀] B₀) (R ⊗[A₀] B₀)
    (fun P ↦ Localization.AtPrime P) (fun P ↦ Algebra.linearMap _ _) fun Q _ ↦ H Q

/-- The core of `Algebra.FinitePresentation.exists_isPushout_faithfullyFlat`: if `B₀` is a
finitely presented algebra over a noetherian ring `A₀` and `A ⊗[A₀] B₀` is faithfully flat over
`A`, then `R ⊗[A₀] B₀` is faithfully flat over some finitely generated `A₀`-subalgebra `R` of
`A`. -/
theorem exists_fg_faithfullyFlat_tensorProduct [IsNoetherianRing A₀]
    [Algebra.FinitePresentation A₀ B₀] [Module.FaithfullyFlat A (A ⊗[A₀] B₀)] :
    ∃ R : Subalgebra A₀ A, R.FG ∧ Module.FaithfullyFlat R (R ⊗[A₀] B₀) := by
  classical
  let ι (R : Subalgebra A₀ A) : R ⊗[A₀] B₀ →ₐ[A₀] A ⊗[A₀] B₀ :=
    Algebra.TensorProduct.map R.val (AlgHom.id A₀ B₀)
  let κ {R R' : Subalgebra A₀ A} (h : R ≤ R') : R ⊗[A₀] B₀ →ₐ[A₀] R' ⊗[A₀] B₀ :=
    Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id A₀ B₀)
  have hmapκ {R R' R'' : Subalgebra A₀ A} (h : R ≤ R') (h' : R' ≤ R'')
      (J : Ideal (R ⊗[A₀] B₀)) : (J.map (κ h)).map (κ h') = J.map (κ (h.trans h')) := by
    have hA : (κ h').comp (κ h) = κ (h.trans h') := by ext <;> rfl
    have : (κ h').toRingHom.comp (κ h).toRingHom = (κ (h.trans h')).toRingHom :=
      RingHom.ext fun x ↦ DFunLike.congr_fun hA x
    exact (Ideal.map_map (κ h).toRingHom (κ h').toRingHom).trans (by rw [this]; rfl)
  obtain ⟨R₁, hR₁, hflat⟩ := exists_fg_forall_flat_localization_tensor_of_isCompact
    (R₀ := A₀) (S₀ := B₀) (A := A) (K := Set.univ) isCompact_univ
  have : Algebra.FiniteType A₀ R₁ := (Subalgebra.fg_iff_finiteType _).mp hR₁
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing A₀ R₁
  let U := {q : PrimeSpectrum (R₁ ⊗[A₀] B₀) | Module.Flat R₁ (Localization.AtPrime q.asIdeal)}
  have hU : IsOpen U := isOpen_setOf_flat_localization
  let I : Ideal (R₁ ⊗[A₀] B₀) := Ideal.span {f | (basicOpen f : Set _) ⊆ U}
  have hI : I.map (ι R₁) = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    let P : PrimeSpectrum (R₁ ⊗[A₀] B₀) := comap (ι R₁).toRingHom ⟨m, hm.isPrime⟩
    have hP : P ∈ U := hflat _ trivial
    obtain ⟨_, ⟨f, rfl⟩, hPf, hfU⟩ :=
      isTopologicalBasis_basic_opens.exists_subset_of_mem_open hP hU
    exact hPf (hle (Ideal.mem_map_of_mem _ (Ideal.subset_span hfU)))
  obtain ⟨R₂, h₁₂, hR₂, hI₂⟩ := Subalgebra.exists_map_tensorProduct_inclusion_eq_top hR₁ I hI
  have hflat₂ {R : Subalgebra A₀ A} (h : R₂ ≤ R) : Module.Flat R (R ⊗[A₀] B₀) :=
    flat_tensorProduct_of_map_eq_top (h₁₂.trans h) U (fun _ hq ↦ hq) (by
      rw [← hmapκ h₁₂ h, hI₂, Ideal.map_top])
  have : Module.Flat R₂ (R₂ ⊗[A₀] B₀) := hflat₂ le_rfl
  let V := Set.range (comap (algebraMap R₂ (R₂ ⊗[A₀] B₀)))
  have hV : IsOpen V := isOpenMap_comap_of_hasGoingDown_of_finitePresentation.isOpen_range
  let J : Ideal R₂ := Ideal.span {g | (basicOpen g : Set _) ⊆ V}
  have hJ : J.map R₂.val = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A)
      (B := A ⊗[A₀] B₀) ⟨m, hm.isPrime⟩
    have hcomp : (ι R₂).toRingHom.comp (algebraMap R₂ (R₂ ⊗[A₀] B₀)) =
        (algebraMap A (A ⊗[A₀] B₀)).comp R₂.val.toRingHom := by
      ext x
      simp [ι, Algebra.TensorProduct.algebraMap_apply]
    have hp : comap R₂.val.toRingHom ⟨m, hm.isPrime⟩ ∈ V :=
      ⟨comap (ι R₂).toRingHom q, by rw [← comap_comp_apply, hcomp, comap_comp_apply, hq]⟩
    obtain ⟨_, ⟨g, rfl⟩, hpg, hgV⟩ :=
      isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hV
    exact hpg (hle (Ideal.mem_map_of_mem _ (Ideal.subset_span hgV)))
  obtain ⟨R₃, h₂₃, hR₃, hJ₃⟩ := Subalgebra.exists_map_inclusion_eq_top hR₂ J hJ
  have : Module.Flat R₃ (R₃ ⊗[A₀] B₀) := hflat₂ h₂₃
  refine ⟨R₃, hR₃, .of_comap_surjective fun P ↦ ?_⟩
  obtain ⟨g, hgV, hgp⟩ : ∃ g, (basicOpen g : Set _) ⊆ V ∧
      g ∉ P.asIdeal.comap (Subalgebra.inclusion h₂₃) := by
    by_contra! H
    have hle : J ≤ P.asIdeal.comap (Subalgebra.inclusion h₂₃) :=
      Ideal.span_le.mpr fun g hg ↦ H g hg
    have := Ideal.map_le_iff_le_comap.mpr hle
    rw [hJ₃] at this
    exact P.isPrime.ne_top (top_le_iff.mp this)
  obtain ⟨q₂, hq₂⟩ := hgV (show (⟨_, Ideal.comap_isPrime _ _⟩ : PrimeSpectrum R₂) ∈ basicOpen g
    from hgp)
  let : Algebra R₂ R₃ := (Subalgebra.inclusion h₂₃).toAlgebra
  have : IsScalarTower A₀ R₂ R₃ := .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra (R₂ ⊗[A₀] B₀) (R₃ ⊗[A₀] B₀) := (κ h₂₃).toAlgebra
  have : IsScalarTower R₂ (R₂ ⊗[A₀] B₀) (R₃ ⊗[A₀] B₀) :=
    IsScalarTower.of_algebraMap_eq (R := R₂) (S := R₂ ⊗[A₀] B₀) (A := R₃ ⊗[A₀] B₀) fun _ ↦ rfl
  have : Algebra.IsPushout R₂ R₃ (R₂ ⊗[A₀] B₀) (R₃ ⊗[A₀] B₀) :=
    Algebra.IsPushout.tensorProduct_tensorProduct A₀ B₀ R₂ R₃ (by ext; rfl)
  obtain ⟨q, hq, -⟩ := exists_comap_eq_of_isPushout (A₁ := R₂) (A := R₃)
    (B₁ := R₂ ⊗[A₀] B₀) (B := R₃ ⊗[A₀] B₀) P.asIdeal.ResidueField
    (Ideal.ker_algebraMap_residueField _) q₂ hq₂
  exact ⟨q, hq⟩

omit [CommRing A₀] [CommRing B₀] [Algebra A₀ A] [Algebra A₀ B₀] in
/-- **A faithfully flat model over a finitely generated `ℤ`-algebra** (the absolute case of
Stacks, Tag 034Y). A faithfully flat `A`-algebra `B` of finite presentation is the base change
of a faithfully flat algebra of finite presentation `B₁` over a finitely presented `ℤ`-algebra
`A₁` mapping to `A`.

`B` first descends to a finitely generated subring `A₀` of `A`; the flat locus of a model over a
noetherian ring is open (Stacks, Tag 00RC) and contains every point coming from `B` after a
finitely generated enlargement (Stacks, Tag 00R6), and a further enlargement makes the model flat
everywhere. Its image in the spectrum of the base is open (Stacks, Tag 00I1) and contains the
image of `Spec A`, so a last enlargement makes it surjective. -/
theorem exists_isPushout_faithfullyFlat (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] [Module.FaithfullyFlat A B] :
    ∃ (A₁ B₁ : Type u) (_ : CommRing A₁) (_ : CommRing B₁) (_ : Algebra A₁ A)
      (_ : Algebra A₁ B₁) (_ : Algebra B₁ B) (_ : Algebra A₁ B) (_ : IsScalarTower A₁ A B)
      (_ : IsScalarTower A₁ B₁ B),
      Algebra.FinitePresentation ℤ A₁ ∧ Algebra.FinitePresentation A₁ B₁ ∧
        Module.FaithfullyFlat A₁ B₁ ∧ Algebra.IsPushout A₁ A B₁ B := by
  classical
  obtain ⟨A₀, B₀, _, _, _, _, hA₀, hB₀, hpush⟩ := exists_fg_subalgebra_isPushout A B
  have : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  let e₀ : A ⊗[A₀] B₀ ≃ₐ[A] B := Algebra.IsPushout.equiv A₀ A B₀ B
  have : Module.FaithfullyFlat A (A ⊗[A₀] B₀) :=
    Module.FaithfullyFlat.of_linearEquiv _ _ e₀.toLinearEquiv
  obtain ⟨R, hR, hff⟩ := exists_fg_faithfullyFlat_tensorProduct (A₀ := A₀) (A := A) (B₀ := B₀)
  let := Algebra.IsPushout.tensorProductAlgebra A₀ R A B₀ B
  have := Algebra.IsPushout.isScalarTower_tensorProductAlgebra A₀ R A B₀ B
  have hpush' := Algebra.IsPushout.tensorProduct A₀ R A B₀ B
  have hfin : Algebra.FiniteType ℤ R :=
    .trans (S := A₀) inferInstance ((Subalgebra.fg_iff_finiteType _).mp hR)
  exact ⟨R, R ⊗[A₀] B₀, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.FinitePresentation.of_finiteType.mp hfin, inferInstance, hff, hpush'⟩

omit [CommRing A₀] [CommRing B₀] [Algebra A₀ A] [Algebra A₀ B₀] in
/-- **Finite presentation descends along faithfully flat maps of finite presentation** (Stacks,
Tag 02KK). Let `R → A → B` be ring maps such that `B` is of finite presentation over `R` and
faithfully flat and of finite presentation over `A`. Then `A` is of finite presentation over `R`.

By `Algebra.FinitePresentation.exists_isPushout_faithfullyFlat`, `A → B` is the base change of a
faithfully flat map of finite presentation `A₁ → B₁` with `A₁` of finite presentation over `ℤ`.
Base changing further to `A₀ = R ⊗[ℤ] A₁`, which is of finite presentation over `R`, `A → B` is
the base change along `A₀ → A` of the faithfully flat map `A₀ → A₀ ⊗[A₁] B₁`, and `B` is of finite
presentation over `A₀ ⊗[A₁] B₁`. So `A` is of finite presentation over `A₀` by faithfully flat
descent (`RingHom.FinitePresentation.codescendsAlong_faithfullyFlat`), hence over `R`. -/
@[stacks 02KK]
theorem of_finitePresentation_of_faithfullyFlat (R B : Type u) [CommRing R] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FinitePresentation R B] [Algebra.FinitePresentation A B]
    [Module.FaithfullyFlat A B] : Algebra.FinitePresentation R A := by
  obtain ⟨A₁, B₁, _, _, _, _, _, _, _, _, hA₁, hB₁, hff, hpush⟩ :=
    exists_isPushout_faithfullyFlat (A := A) B
  let A₀ := R ⊗[ℤ] A₁
  let : Algebra A₁ A₀ := Algebra.TensorProduct.rightAlgebra
  let f : A₀ →ₐ[R] A := Algebra.TensorProduct.lift (Algebra.ofId R A)
    (algebraMap A₁ A).toIntAlgHom fun _ _ ↦ Commute.all _ _
  let : Algebra A₀ A := f.toRingHom.toAlgebra
  have : IsScalarTower R A₀ A := .of_algebraMap_eq fun r ↦ (f.commutes r).symm
  have : IsScalarTower A₁ A₀ A := .of_algebraMap_eq fun a ↦ by
    rw [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.right_algebraMap_apply]
    change _ = f (1 ⊗ₜ a)
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  let : Algebra A₀ B := ((algebraMap A B).comp (algebraMap A₀ A)).toAlgebra
  have : IsScalarTower A₀ A B := .of_algebraMap_eq fun _ ↦ rfl
  let := Algebra.IsPushout.tensorProductAlgebra A₁ A₀ A B₁ B
  have := Algebra.IsPushout.isScalarTower_tensorProductAlgebra A₁ A₀ A B₁ B
  have hpush₀ := Algebra.IsPushout.tensorProduct A₁ A₀ A B₁ B
  have : IsScalarTower R A₀ B := IsScalarTower.of_algebraMap_eq (R := R) (S := A₀) (A := B)
      fun r ↦ by
    rw [IsScalarTower.algebraMap_apply A₀ A B, ← IsScalarTower.algebraMap_apply R A₀ A,
      ← IsScalarTower.algebraMap_apply R A B]
  have : Algebra.FinitePresentation A₀ B := .of_restrict_scalars_finitePresentation R A₀ B
  have : Algebra.FinitePresentation (A₀ ⊗[A₁] B₁) B :=
    .of_restrict_scalars_finitePresentation A₀ (A₀ ⊗[A₁] B₁) B
  have : Algebra.FinitePresentation A₀ A := by
    rw [← RingHom.finitePresentation_algebraMap]
    exact RingHom.FinitePresentation.codescendsAlong_faithfullyFlat (R := A₀) (S := A)
      (R' := A₀ ⊗[A₁] B₁) (S' := B) (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  exact .trans R A₀ A

end Algebra.FinitePresentation

end FaithfullyFlatModel
