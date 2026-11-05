import Jacobian.RingTheory.FaithfullyFlat.AlgebraFinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Finite presentation under faithfully flat source maps

Local finite presentation descends along flat surjections locally of finite
presentation. The affine case follows from descent of algebra presentations;
finite affine covers reduce the general case to the affine case.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry
/-- The affine case of
`AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_flat_of_surjective`:
on global sections it is `Algebra.FinitePresentation.of_finitePresentation_of_faithfullyFlat`. -/
theorem LocallyOfFinitePresentation.of_comp_of_flat_of_surjective_of_isAffine
    {X' X S : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine S] (u : X' ⟶ X) (f : X ⟶ S)
    [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    [LocallyOfFinitePresentation (u ≫ f)] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  have hu : u.appTop.hom.Flat := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp ‹_›
  have hu' : u.appTop.hom.FinitePresentation :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mp ‹_›
  have huf : (u.appTop.hom.comp f.appTop.hom).FinitePresentation :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation) (f := u ≫ f)).mp ‹_›
  have hsurj : Function.Surjective (PrimeSpectrum.comap u.appTop.hom) := by
    intro p
    let p' : Spec Γ(X, ⊤) := p
    obtain ⟨w, hw⟩ := u.surjective (X.isoSpec.inv p')
    refine ⟨X'.isoSpec.hom w, ?_⟩
    have h₁ : (X'.isoSpec.hom ≫ Spec.map u.appTop) w = (u ≫ X.isoSpec.hom) w := by
      rw [Scheme.isoSpec_hom_naturality]
    have h₂ : X.isoSpec.hom (X.isoSpec.inv p') = p' := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw, h₂] at h₁
    exact h₁
  algebraize [f.appTop.hom, u.appTop.hom, u.appTop.hom.comp f.appTop.hom]
  have : Module.FaithfullyFlat Γ(X, ⊤) Γ(X', ⊤) := .of_comap_surjective hsurj
  exact Algebra.FinitePresentation.of_finitePresentation_of_faithfullyFlat (A := Γ(X, ⊤))
    Γ(S, ⊤) Γ(X', ⊤)

/-- The case of affine `X` and `S` of
`AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_flat_of_surjective`: since `u` is open,
finitely many affine opens of `X'` have images covering `X`, and their disjoint union is affine. -/
theorem LocallyOfFinitePresentation.of_comp_of_flat_of_surjective_of_isAffine_of_isAffine
    {X' X S : Scheme.{u}} [IsAffine X] [IsAffine S] (u : X' ⟶ X) (f : X ⟶ S)
    [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    [LocallyOfFinitePresentation (u ≫ f)] : LocallyOfFinitePresentation f := by
  classical
  have hcov (x : X) : ∃ W : X'.affineOpens, x ∈ u '' (W : Set X') := by
    obtain ⟨w, rfl⟩ := u.surjective x
    obtain ⟨W, hW, hwW, -⟩ := (Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens)
      (show w ∈ (⊤ : X'.Opens) from trivial)
    exact ⟨⟨W, hW⟩, w, hwW, rfl⟩
  choose W hW using hcov
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ u '' (W x : Set X'))
    (fun x ↦ u.isOpenMap _ (W x).1.isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hW x⟩)
  let Y (i : s) : Scheme.{u} := (W i.1 : X'.Opens)
  have (i : s) : IsAffine (Y i) := (W i.1).2
  let g : ∐ Y ⟶ X := Sigma.desc fun i : s ↦ (W i.1 : X'.Opens).ι ≫ u
  have : Flat g := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have : LocallyOfFinitePresentation g := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have : LocallyOfFinitePresentation (g ≫ f) := by
    have : g ≫ f = Sigma.desc fun i : s ↦ (W i.1 : X'.Opens).ι ≫ u ≫ f := by
      ext i
      simp [g, Sigma.ι_desc]
    rw [this]
    exact IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have : Surjective g := Surjective.sigmaDesc_of_union_range_eq_univ <|
    Set.eq_univ_of_forall fun x ↦ by
      obtain ⟨i, hi, w, hw, rfl⟩ : ∃ i ∈ s, ∃ w ∈ (W i : Set X'), u w = x := by
        simpa using hs (Set.mem_univ x)
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, ⟨w, hw⟩, rfl⟩
  exact of_comp_of_flat_of_surjective_of_isAffine g f

/-- **Local finite presentation descends along flat surjections of finite presentation.** Let
`u : X' ⟶ X` be surjective, flat and locally of finite presentation, and let `f : X ⟶ S`. If
`u ≫ f` is locally of finite presentation, then so is `f`. -/
@[stacks 02KL]
theorem LocallyOfFinitePresentation.of_comp_of_flat_of_surjective {X' X S : Scheme.{u}}
    (u : X' ⟶ X) (f : X ⟶ S) [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    [LocallyOfFinitePresentation (u ≫ f)] : LocallyOfFinitePresentation f := by
  have key (x : X) : ∃ (U : S.Opens) (V : X.Opens) (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U),
      LocallyOfFinitePresentation (f.resLE U V e) := by
    obtain ⟨U, hU, hfxU, -⟩ := (Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
      (show f x ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show x ∈ f ⁻¹ᵁ U from hfxU)
    refine ⟨U, V, hxV, hVU, ?_⟩
    have : IsAffine U := hU
    have : IsAffine V := hV
    have : Flat (u ∣_ V) := IsZariskiLocalAtTarget.restrict ‹_› V
    have : Surjective (u ∣_ V) := IsZariskiLocalAtTarget.restrict ‹_› V
    have : LocallyOfFinitePresentation (u ∣_ V) := IsZariskiLocalAtTarget.restrict ‹_› V
    have : LocallyOfFinitePresentation (u ∣_ V ≫ f.resLE U V hVU) := by
      rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
      exact IsZariskiLocalAtSource.resLE _ ‹_›
    exact of_comp_of_flat_of_surjective_of_isAffine_of_isAffine (u ∣_ V) (f.resLE U V hVU)
  choose U V hxV e hf using key
  refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top (fun x : X ↦ V x)
    (P := @LocallyOfFinitePresentation) ?_).mpr fun x ↦ ?_
  · exact eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxV x⟩
  · rw [← Scheme.Hom.resLE_comp_ι _ (e x)]
    infer_instance

end AlgebraicGeometry
