import Jacobian.RingTheory.RingHom.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Faithfully flat descent of morphism properties

Flatness, affineness, finiteness and closed immersions descend along surjective
flat quasi-compact morphisms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

/-- Quasi-separatedness of schemes descends along surjective quasi-compact morphisms: the
intersection of two quasi-compact opens of `Y` is the image of the intersection of their
quasi-compact preimages. -/
lemma quasiSeparatedSpace_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    [QuasiCompact f] [QuasiSeparatedSpace X] : QuasiSeparatedSpace Y := by
  refine ⟨fun U V hU hUc hV hVc ↦ ?_⟩
  have h := QuasiSeparatedSpace.inter_isCompact _ _ (hU.preimage f.continuous)
    (QuasiCompact.isCompact_preimage (f := f) U hU hUc) (hV.preimage f.continuous)
    (QuasiCompact.isCompact_preimage (f := f) V hV hVc)
  rw [← Set.preimage_inter] at h
  simpa [Set.image_preimage_eq _ f.surjective] using h.image f.continuous
set_option backward.isDefEq.respectTransparency.types false in
/-- Flatness satisfies fpqc descent. -/
@[stacks 02L2]
instance Flat.descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @Flat (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.Flat.codescendsAlong_faithfullyFlat

set_option backward.isDefEq.respectTransparency.types false in
/-- **Being affine satisfies fpqc descent.** If the base change of `f : X ⟶ Y` along a
faithfully flat quasi-compact morphism is affine, then `f` is affine.

The question is local on `Y`, so let `Y = Spec R` and let `Spec S ⟶ Spec R` be faithfully flat
with `X' = X ×_R Spec S` affine. Then `X` is quasi-compact and quasi-separated, as `X' ⟶ X` is
surjective and quasi-compact, so `Γ(X') = Γ(X) ⊗_R S` by flat base change. Hence the canonical
morphism `X' ⟶ Spec Γ(X')`, an isomorphism, is the base change of `X ⟶ Spec Γ(X)` along the
faithfully flat `Spec Γ(X') ⟶ Spec Γ(X)`, and isomorphisms descend. -/
@[stacks 02L5]
theorem IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong (@IsAffineHom : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  intro R S Y φ g ⟨hsurj, hflat⟩ hf
  let Q : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact
  have hQ : Q (Spec.map φ) := ⟨⟨hsurj, hflat⟩, inferInstance⟩
  have hsq := IsPullback.of_hasPullback (Spec.map φ) g
  set π := pullback.snd (Spec.map φ) g
  set f' := pullback.fst (Spec.map φ) g
  have : IsAffine (pullback (Spec.map φ) g) := isAffine_of_isAffineHom f'
  have hπ : Q π := Q.pullback_snd _ _ hQ
  have : Surjective π := hπ.1.1
  have : QuasiCompact π := hπ.2
  have : CompactSpace Y := π.surjective.compactSpace π.continuous
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_surjective π
  suffices IsAffine Y from inferInstance
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right hsq.flip
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) le_top le_top (by simp)
    (isAffineOpen_top _) (isAffineOpen_top _) isCompact_univ isQuasiSeparated_univ
  have happ {A B : Scheme.{u}} (h : A ⟶ B) (e) : h.appLE ⊤ ⊤ e = h.appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hpo : IsPushout g.appTop (Spec.map φ).appTop π.appTop f'.appTop := by
    have := (isIso_pushoutSection_iff ..).mp this
    rwa [happ, happ, happ, happ] at this
  have t := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  have hR : IsPullback (Spec.map φ) (Spec S).toSpecΓ (Spec R).toSpecΓ
      (Spec.map (Spec.map φ).appTop) :=
    .of_vert_isIso ⟨Scheme.toSpecΓ_naturality _⟩
  have s := hsq.flip.paste_vert hR
  rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality] at s
  have top := IsPullback.of_bot s (Scheme.toSpecΓ_naturality π) t
  have hQ' : Q (Spec.map (Spec.map φ).appTop) := by
    have e : Spec.map (Spec.map φ).appTop =
        inv (Spec S).toSpecΓ ≫ Spec.map φ ≫ (Spec R).toSpecΓ := by
      rw [Scheme.toSpecΓ_naturality (Spec.map φ), IsIso.inv_hom_id_assoc]
    rw [e, Q.cancel_left_of_respectsIso, Q.cancel_right_of_respectsIso]
    exact hQ
  have : IsIso Y.toSpecΓ :=
    DescendsAlong.of_isPullback (P := isomorphisms Scheme.{u}) top.flip (Q.of_isPullback t.flip hQ')
      (inferInstanceAs (IsIso (pullback (Spec.map φ) g).toSpecΓ))
  exact ⟨this⟩

/-- **Being finite satisfies fpqc descent.** A morphism is finite if and only if it is
universally closed, affine and locally of finite type, and each of these properties descends. -/
@[stacks 02LA]
theorem IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @IsFinite (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasicompact
  rw [IsFinite.eq_inf, IsIntegralHom.eq_universallyClosed_inf_isAffineHom]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- **Monomorphisms satisfy fpqc descent**: a morphism is a monomorphism if and only if its
diagonal is an isomorphism, and isomorphisms descend. -/
theorem descendsAlong_monomorphisms_surjective_inf_flat_inf_quasicompact :
    DescendsAlong (monomorphisms Scheme.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [← diagonal_isomorphisms]
  infer_instance

/-- **Being a closed immersion satisfies fpqc descent**: a closed immersion is the same as a
finite monomorphism (`AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono`), and both
properties descend. -/
theorem IsClosedImmersion.descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong (@IsClosedImmersion : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact
  have := descendsAlong_monomorphisms_surjective_inf_flat_inf_quasicompact.{u}
  refine ⟨fun {A X Y Z fst snd f g} h hf hfst ↦ ?_⟩
  rw [IsClosedImmersion.iff_isFinite_and_mono] at hfst ⊢
  have hmono : monomorphisms _ fst := hfst.2
  exact ⟨of_isPullback_of_descendsAlong h hf hfst.1,
    of_isPullback_of_descendsAlong (P := monomorphisms _) h hf hmono⟩

end AlgebraicGeometry
