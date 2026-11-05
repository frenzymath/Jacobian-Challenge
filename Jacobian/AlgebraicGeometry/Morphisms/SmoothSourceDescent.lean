import Jacobian.AlgebraicGeometry.Morphisms.FinitePresentationSourceDescent
import Jacobian.AlgebraicGeometry.Morphisms.FlatSourceDescent
import Jacobian.AlgebraicGeometry.Morphisms.QuasiFiniteDimension
import Jacobian.RingTheory.RegularLocalRing.ProjectiveDimension
import Jacobian.RingTheory.Smooth.RegularLocalRing
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Smoothness under faithfully flat source maps

Smoothness descends along flat surjections locally of finite presentation.
Over a field this follows by descending regularity of local rings after passage
to an algebraic closure. For finite flat source covers, the relative dimension
also descends, since finite surjections preserve fiber dimensions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace AlgebraicGeometry
/-- A smooth morphism is, locally on the source and on the target, smooth of some relative
dimension: every point `x` has affine open neighbourhoods `V ∋ x` and `U ∋ f.base x` with
`V ≤ f ⁻¹ᵁ U` such that `f.resLE U V` is smooth of relative dimension `d` for some `d`.
Thus the relative dimension may be chosen constant near each point. -/
theorem Smooth.exists_smoothOfRelativeDimension_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) :
    ∃ (U : Y.Opens) (V : X.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V) (_ : x ∈ V)
      (e : V ≤ f ⁻¹ᵁ U) (d : ℕ), SmoothOfRelativeDimension d (f.resLE U V e) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := (Smooth.iff_forall_exists_isStandardSmooth f).mp ‹_› x
  let := (f.appLE U V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hf.out
  have hd : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension P.dimension :=
    P.isStandardSmoothOfRelativeDimension rfl
  refine ⟨U, V, hU, hV, hx, e, P.dimension, ?_⟩
  have : IsAffine U := hU
  have : IsAffine V := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)]
  have : (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension P.dimension))).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp <|
      (HasRingHomProperty.isLocal_ringHomProperty
        (@SmoothOfRelativeDimension P.dimension)).respectsIso
  exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension P.dimension)))
      (arrowResLEAppIso f U V e)).mpr
    (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hd)

/-- Smoothness of relative dimension `n` is local on the source: if every point of `X` has an
open neighbourhood `V` such that `V ⟶ Y` is smooth of relative dimension `n`, then so is
`f : X ⟶ Y`. -/
theorem smoothOfRelativeDimension_of_forall_exists_mem {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (H : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ f)) :
    SmoothOfRelativeDimension n f := by
  choose V hxV hV using H
  exact IsZariskiLocalAtSource.of_iSup_eq_top V
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩) hV

/-- The relative dimension of a smooth morphism from a nonempty scheme to the spectrum of a
field is unique: it is the dimension of the source. -/
theorem SmoothOfRelativeDimension.eq_of_field {K : Type u} [Field K] {X : Scheme.{u}}
    [Nonempty X] (f : X ⟶ Spec (.of K)) {m n : ℕ} (hm : SmoothOfRelativeDimension m f)
    (hn : SmoothOfRelativeDimension n f) : m = n := by
  have h₁ := topologicalKrullDim_eq_of_smoothOfRelativeDimension f m
  have h₂ := topologicalKrullDim_eq_of_smoothOfRelativeDimension f n
  exact_mod_cast h₁.symm.trans h₂

/-- **The relative dimension of a smooth morphism is read off its fibres.** A smooth morphism
`f : X ⟶ Y` whose fibres `X_y ⟶ Spec κ(y)` are all smooth of relative dimension `n` is smooth of
relative dimension `n`. -/
theorem smoothOfRelativeDimension_of_fiberToSpecResidueField {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] (n : ℕ) (h : ∀ y, SmoothOfRelativeDimension n (f.fiberToSpecResidueField y)) :
    SmoothOfRelativeDimension n f := by
  refine smoothOfRelativeDimension_of_forall_exists_mem f n fun x ↦ ?_
  obtain ⟨U, V, -, -, hx, e, d, hd⟩ := Smooth.exists_smoothOfRelativeDimension_resLE f x
  have : SmoothOfRelativeDimension d (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e]
    have : SmoothOfRelativeDimension (d + 0) (f.resLE U V e ≫ U.ι) := inferInstance
    simpa using this
  let W := (f.fiberι (f x)) ⁻¹ᵁ V
  have hW : f.asFiber x ∈ W := by
    change f.fiberι _ (f.asFiber x) ∈ V
    rwa [Scheme.Hom.fiberι_asFiber]
  have : Nonempty W := ⟨⟨_, hW⟩⟩
  have hpb : IsPullback (f.fiberι (f x) ∣_ V) (W.ι ≫ f.fiberToSpecResidueField (f x))
      (V.ι ≫ f) (Y.fromSpecResidueField (f x)) :=
    (isPullback_morphismRestrict (f.fiberι (f x)) V).paste_vert (IsPullback.of_hasPullback _ _)
  have h₁ : SmoothOfRelativeDimension d (W.ι ≫ f.fiberToSpecResidueField (f x)) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    exact MorphismProperty.of_isPullback hpb inferInstance
  have h₂ : SmoothOfRelativeDimension n (W.ι ≫ f.fiberToSpecResidueField (f x)) := by
    have := h (f x)
    have : SmoothOfRelativeDimension (0 + n) (W.ι ≫ f.fiberToSpecResidueField (f x)) :=
      inferInstance
    simpa using this
  obtain rfl := SmoothOfRelativeDimension.eq_of_field _ h₁ h₂
  exact ⟨V, hx, inferInstance⟩

/-- Over a field, the relative dimension of a smooth morphism `f : X ⟶ Spec K` can be computed
after composing with a universally closed, locally quasi-finite surjection `u : X' ⟶ X`: such
a `u` preserves the dimension of open subschemes. -/
theorem smoothOfRelativeDimension_of_comp_of_surjective_of_field {K : Type u} [Field K]
    {X' X : Scheme.{u}} (u : X' ⟶ X) (f : X ⟶ Spec (.of K)) [Smooth f] [UniversallyClosed u]
    [LocallyQuasiFinite u] [Surjective u] (n : ℕ) [SmoothOfRelativeDimension n (u ≫ f)] :
    SmoothOfRelativeDimension n f := by
  refine smoothOfRelativeDimension_of_forall_exists_mem f n fun x ↦ ?_
  obtain ⟨U, V, -, -, hx, e, d, hd⟩ := Smooth.exists_smoothOfRelativeDimension_resLE f x
  have : SmoothOfRelativeDimension d (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e]
    have : SmoothOfRelativeDimension (d + 0) (f.resLE U V e ≫ U.ι) := inferInstance
    simpa using this
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  obtain ⟨x', hx'⟩ := u.surjective x
  have : Nonempty (u ⁻¹ᵁ V) := ⟨⟨x', by simpa [hx'] using hx⟩⟩
  have : SmoothOfRelativeDimension n ((u ⁻¹ᵁ V).ι ≫ u ≫ f) := by
    have : SmoothOfRelativeDimension (0 + n) ((u ⁻¹ᵁ V).ι ≫ u ≫ f) := inferInstance
    simpa using this
  have : Surjective (u ∣_ V) :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict u V).flip ‹_›
  have h := (u ∣_ V).topologicalKrullDim_eq_of_surjective
  rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension ((u ⁻¹ᵁ V).ι ≫ u ≫ f) n,
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (V.ι ≫ f) d] at h
  obtain rfl : n = d := by exact_mod_cast h
  exact ⟨V, hx, inferInstance⟩

/-- The local rings of a scheme smooth over a field `k` are regular local rings: near any point
the scheme is étale over an affine space `𝔸ⁿ_k`, whose local rings are regular, and étale maps
preserve regularity. -/
theorem Smooth.isRegularLocalRing_stalk {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, V, -, -, hx, e, d, hd⟩ := Smooth.exists_smoothOfRelativeDimension_resLE f x
  have : SmoothOfRelativeDimension d (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e]
    exact smoothOfRelativeDimension_comp (n := d) (m := 0) _ _
  obtain ⟨W, hW, hxW, φ, hφ⟩ :=
    SmoothOfRelativeDimension.exists_etale_mvPolynomial_of_field (V.ι ≫ f) d ⟨x, hx⟩
  have := hW.isRegularLocalRing_stalk_of_etale φ hφ _ hxW
  exact .of_ringEquiv (V.stalkIso ⟨x, hx⟩).commRingCatIsoToRingEquiv

/-- Over an algebraically closed field `K`, a scheme locally of finite type over `K` is smooth at
every closed point whose local ring is regular. -/
theorem Scheme.Hom.mem_smoothLocus_of_isRegularLocalRing {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {x : X} (hx : IsClosed {x})
    [IsRegularLocalRing (X.presheaf.stalk x)] : x ∈ f.smoothLocus := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen (⊤ : (Spec (.of K)).Opens) := isAffineOpen_top _
  have hVU : V ≤ f ⁻¹ᵁ ⊤ := le_top
  have hft := f.finiteType_appLE hU hV hVU
  algebraize [(f.appLE ⊤ V hVU).hom]
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff ⊤ hU V hV hVU hxV]
  set q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : q.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  have : IsRegularLocalRing (Localization.AtPrime q) := by
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
    have := hV.isLocalization_stalk ⟨x, hxV⟩
    exact .of_ringEquiv (IsLocalization.algEquiv q.primeCompl (X.presheaf.stalk x)
      (Localization.AtPrime q)).toRingEquiv
  let e : K ≃+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  let : Algebra K Γ(X, V) := ((f.appLE ⊤ V hVU).hom.comp e.toRingHom).toAlgebra
  have : Algebra.FiniteType K Γ(X, V) :=
    RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ e.surjective)
  have h : Algebra.FormallySmooth K (Localization.AtPrime q) :=
    Algebra.IsSmoothAt.of_isRegularLocalRing_of_isAlgClosed (k := K) q
  change Algebra.FormallySmooth Γ(Spec (.of K), ⊤) (Localization.AtPrime q)
  rw [← RingHom.formallySmooth_algebraMap] at h ⊢
  have heq : algebraMap K (Localization.AtPrime q) =
      (algebraMap Γ(Spec (.of K), ⊤) (Localization.AtPrime q)).comp e.toRingHom := by
    rw [IsScalarTower.algebraMap_eq K Γ(X, V), IsScalarTower.algebraMap_eq Γ(Spec (.of K), ⊤)
      Γ(X, V)]
    rfl
  rw [heq] at h
  have := RingHom.FormallySmooth.respectsIso.2 _ e.symm h
  convert this using 1
  refine RingHom.ext fun a ↦ ?_
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply]

open Limits in
/-- **Smoothness over a field descends along flat surjections** (Stacks, Tag 05AX). Let
`u : X' ⟶ X` be flat and surjective, and let `f : X ⟶ Spec K` be locally of finite type. If
`u ≫ f` is smooth, then so is `f`.

After base change to an algebraic closure of `K` (smoothness descends along the fpqc covering
`Spec K̄ ⟶ Spec K`), it suffices to show that `f` is smooth at the closed points, as the smooth
locus is open and `X` is a Jacobson space. At a closed point `x = u x'`, the local ring `𝒪_{X,x}`
is regular since `𝒪_{X,x} ⟶ 𝒪_{X',x'}` is a flat local homomorphism and `𝒪_{X',x'}` is regular
(`IsRegularLocalRing.of_flat`), and a regular point with residue field `K` is smooth. -/
@[stacks 05AX]
theorem Smooth.of_comp_of_flat_of_surjective_of_field {K : Type u} [Field K] {X' X : Scheme.{u}}
    (u : X' ⟶ X) (f : X ⟶ Spec (.of K)) [Flat u] [Surjective u] [LocallyOfFiniteType f]
    [Smooth (u ≫ f)] : Smooth f := by
  wlog hK : IsAlgClosed K generalizing K X X' with H
  · let g : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
    have h₁ : Smooth (pullback.snd (u ≫ f) g) := MorphismProperty.pullback_snd _ _ ‹_›
    have : Smooth (pullback.snd u (pullback.fst f g) ≫ pullback.snd f g) := by
      rw [← pullbackRightPullbackFstIso_hom_snd]
      have h₂ : Smooth (pullbackRightPullbackFstIso f g u).hom := inferInstance
      exact MorphismProperty.comp_mem _ _ _ h₂ h₁
    have hsnd := H (pullback.snd u (pullback.fst f g)) (pullback.snd f g)
      (AlgebraicClosure.isAlgClosed K)
    have : Surjective g := ⟨fun _ ↦ ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
    have : Flat g := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 inferInstance
    exact MorphismProperty.of_pullback_snd_of_descendsAlong
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨‹_›, ‹_›⟩, inferInstance⟩ hsnd
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  rw [← f.smoothLocus_eq_top_iff]
  by_contra hne
  obtain ⟨x, hxZ, hx⟩ := nonempty_inter_closedPoints (Z := (f.smoothLocus : Set X)ᶜ)
    (Set.nonempty_compl.2 fun h ↦ hne (TopologicalSpace.Opens.ext
      (h.trans TopologicalSpace.Opens.coe_top.symm)))
    f.smoothLocus.isOpen.isClosed_compl.isLocallyClosed
  obtain ⟨x', rfl⟩ := u.surjective x
  have : IsRegularLocalRing (X'.presheaf.stalk x') := Smooth.isRegularLocalRing_stalk (u ≫ f) x'
  have : IsRegularLocalRing (X.presheaf.stalk (u x')) := by
    let := (u.stalkMap x').hom.toAlgebra
    have : IsLocalHom (algebraMap (X.presheaf.stalk (u x')) (X'.presheaf.stalk x')) :=
      inferInstanceAs (IsLocalHom (u.stalkMap x').hom)
    have : Module.Flat (X.presheaf.stalk (u x')) (X'.presheaf.stalk x') := Flat.stalkMap u x'
    exact IsRegularLocalRing.of_flat (S := X'.presheaf.stalk x')
  exact hxZ (f.mem_smoothLocus_of_isRegularLocalRing hx)

open Limits in
/-- **Smoothness descends along flat surjections** (Stacks, Tag 05B5). Let `u : X' ⟶ X` be
flat, surjective and locally of finite presentation, and let `f : X ⟶ S`. If `u ≫ f` is smooth,
then so is `f`: the morphism `f` is flat and locally of finite presentation by descent, and its
fibres are smooth by `AlgebraicGeometry.Smooth.of_comp_of_flat_of_surjective_of_field` applied
to the base change of `u` to the fibres. -/
@[stacks 05B5]
theorem Smooth.of_comp_of_flat_of_surjective {X' X S : Scheme.{u}} (u : X' ⟶ X) (f : X ⟶ S)
    [Flat u] [Surjective u] [LocallyOfFinitePresentation u] [Smooth (u ≫ f)] : Smooth f := by
  have : LocallyOfFinitePresentation f := .of_comp_of_flat_of_surjective u f
  have : Flat f := Flat.of_comp_of_flat_of_surjective u f
  refine Smooth.of_smooth_fiberToSpecResidueField f fun s ↦ ?_
  let g := S.fromSpecResidueField s
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f g))
  have : Smooth (pullback.snd u (pullback.fst f g) ≫ f.fiberToSpecResidueField s) := by
    change Smooth (pullback.snd u (pullback.fst f g) ≫ pullback.snd f g)
    rw [← pullbackRightPullbackFstIso_hom_snd]
    infer_instance
  exact Smooth.of_comp_of_flat_of_surjective_of_field (pullback.snd u (pullback.fst f g)) _

open Limits in
/-- **Smoothness descends along finite locally free surjections.** Let `u : X' ⟶ X` be finite,
flat, locally of finite presentation and surjective, and let `f : X ⟶ S`. If `u ≫ f` is smooth of
relative dimension `n`, then so is `f`.

Smoothness descends along flat surjective morphisms locally of finite presentation (Stacks, Tag
05B5), and the relative dimension is preserved since `u` is finite flat surjective, so that
fibres of `u ≫ f` and of `f` have the same local dimensions. -/
theorem smoothOfRelativeDimension_of_comp_of_isFinite_of_surjective {X' X S : Scheme.{u}}
    (u : X' ⟶ X) (f : X ⟶ S) [IsFinite u] [Flat u] [LocallyOfFinitePresentation u]
    [Surjective u] (n : ℕ) [SmoothOfRelativeDimension n (u ≫ f)] :
    SmoothOfRelativeDimension n f := by
  have : Smooth (u ≫ f) := SmoothOfRelativeDimension.smooth n _
  have : Smooth f := Smooth.of_comp_of_flat_of_surjective u f
  refine smoothOfRelativeDimension_of_fiberToSpecResidueField f n fun s ↦ ?_
  let g := S.fromSpecResidueField s
  have : Smooth (f.fiberToSpecResidueField s) := inferInstanceAs (Smooth (pullback.snd f g))
  have : SmoothOfRelativeDimension n
      (pullback.snd u (pullback.fst f g) ≫ f.fiberToSpecResidueField s) := by
    change SmoothOfRelativeDimension n (pullback.snd u (pullback.fst f g) ≫ pullback.snd f g)
    rw [← pullbackRightPullbackFstIso_hom_snd]
    have : SmoothOfRelativeDimension n (pullback.snd (u ≫ f) g) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
        (IsPullback.of_hasPullback (u ≫ f) g) ‹_›
    have : SmoothOfRelativeDimension (0 + n)
        ((pullbackRightPullbackFstIso f g u).hom ≫ pullback.snd (u ≫ f) g) := inferInstance
    simpa using this
  exact smoothOfRelativeDimension_of_comp_of_surjective_of_field
    (pullback.snd u (pullback.fst f g)) (f.fiberToSpecResidueField s) n

end AlgebraicGeometry
