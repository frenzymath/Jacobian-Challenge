import Jacobian.AlgebraicGeometry.IdealSheaf.Affine
import Jacobian.AlgebraicGeometry.IdealSheaf.Image
import Jacobian.RingTheory.Ideal.Flat

/-!
# Flat pullback of ideal sheaves

Flat pullback commutes with quasi-compact pushforward and finite intersections.
A compatible finite flat family is recovered by intersecting its pushforwards.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- Pulling an ideal sheaf back to its own closed subscheme gives zero. -/
lemma comap_subschemeι (I : X.IdealSheafData) : I.comap I.subschemeι = ⊥ :=
  Scheme.Hom.ker_eq_bot_of_isIso (pullback.fst I.subschemeι I.subschemeι)


/-- An ideal sheaf pulling back to zero is contained in the kernel. -/
theorem le_ker_of_comap_eq_bot {J : Y.IdealSheafData} (g : X ⟶ Y) (h : J.comap g = ⊥) :
    J ≤ g.ker := by
  rw [← map_bot g]
  exact le_map_iff_comap_le.mpr h.le

/-- Flat base change commutes with pushforward along a quasi-compact morphism. -/
theorem map_comap_of_isPullback {X' Y' : Scheme.{u}} (B : Y.IdealSheafData) {g : Y ⟶ X}
    [QuasiCompact g] {q : X' ⟶ X} [Flat q] {g' : Y' ⟶ X'} {p : Y' ⟶ Y}
    (h : IsPullback p g' g q) : (B.map g).comap q = (B.comap p).map g' := by
  have hker : ∀ {Z W : Scheme.{u}} (C : Z.IdealSheafData) (φ : Z ⟶ W),
      C.map φ = (C.subschemeι ≫ φ).ker := fun C φ ↦ by
    rw [Scheme.Hom.ker_comp, ker_subschemeι]
  have H := ((IsPullback.of_hasPullback p B.subschemeι).paste_horiz h.flip).flip
  have hsub : (B.comap p).subschemeι = (B.comapIso p).hom ≫ pullback.fst p B.subschemeι :=
    (comapIso_hom_fst _ _).symm
  rw [hker B g, hker (B.comap p) g', ← Scheme.Hom.ker_pullback_snd (B.subschemeι ≫ g) q,
    hsub, Category.assoc, Scheme.Hom.ker_comp_of_isIso, ← H.isoPullback_hom_snd,
    Scheme.Hom.ker_comp_of_isIso]

/-- Restriction of a pushforward to an open subscheme, the case of
`AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_isPullback` for the open immersion
`O.ι`, which is flat. -/
theorem map_comap_opens (g : Y ⟶ X) [QuasiCompact g] (B : Y.IdealSheafData) (O : X.Opens) :
    (B.map g).comap O.ι = (B.comap (g ⁻¹ᵁ O).ι).map (g ∣_ O) :=
  map_comap_of_isPullback B (isPullback_morphismRestrict g O).flip

/-- The pushforward of an ideal sheaf along a quasi-compact flat monomorphism — for
instance the inclusion of a quasi-compact open — restricts back to the original ideal
sheaf. This is the case of
`AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_isPullback` for the kernel pair of a
monomorphism. -/
theorem comap_map (f : X ⟶ Y) [QuasiCompact f] [Flat f] [Mono f] (J : X.IdealSheafData) :
    (J.map f).comap f = J := by
  rw [map_comap_of_isPullback J (IsKernelPair.id_of_mono f), comap_id, map_id]
/-- Pullback of ideal sheaves along a flat morphism commutes with finite intersections: on affine
opens it is the extension of ideals along a flat ring map (`Ideal.map_iInf_of_flat`). -/
lemma comap_iInf_of_flat (f : X ⟶ Y) [Flat f] {ι : Type*} [Finite ι]
    (I : ι → Y.IdealSheafData) : (⨅ i, I i).comap f = ⨅ i, (I i).comap f := by
  refine ext_of_iSup_eq_top (ι := {p : Y.affineOpens × X.affineOpens // p.2.1 ≤ f ⁻¹ᵁ p.1.1})
    (fun p ↦ p.1.2) ?_ fun p ↦ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (a := x) hxV (f ⁻¹ᵁ V).2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(⟨V, hV⟩, ⟨W, hW⟩), hWV⟩, hxW⟩
  · obtain ⟨⟨V, W⟩, h⟩ := p
    have := f.flat_appLE V.2 W.2 h
    algebraize [(f.appLE V.1 W.1 h).hom]
    simp only [ideal_iInf, iInf_apply, ideal_comap_appLE _ f V W h]
    exact Ideal.map_iInf_of_flat (S := Γ(X, W.1)) _

/-- **Descent of ideal sheaves along a finite flat quasi-compact family.** Let `q k : W k ⟶ V`
be finitely many flat quasi-compact morphisms and `I k` ideal sheaves on the `W k` whose
pullbacks to every `W k ×_V W l` agree. Then the pullback of `⨅ k, (I k).map (q k)` along
each `q l` is `I l`.

The formula uses flat base change (`map_comap_of_isPullback`) and that flat pullback commutes with finite
intersections (`comap_iInf_of_flat`). -/
theorem comap_iInf_map_of_flat {V : Scheme.{u}} {κ : Type*} [Finite κ] {W : κ → Scheme.{u}}
    (q : ∀ k, W k ⟶ V) [∀ k, Flat (q k)] [∀ k, QuasiCompact (q k)]
    (I : ∀ k, (W k).IdealSheafData)
    (hcompat : ∀ k l, (I k).comap (pullback.fst (q k) (q l)) =
      (I l).comap (pullback.snd (q k) (q l))) (l : κ) :
    (⨅ k, (I k).map (q k)).comap (q l) = I l := by
  refine le_antisymm ((comap_mono _ (iInf_le _ l)).trans (comap_map_le _ _)) ?_
  rw [comap_iInf_of_flat]
  refine le_iInf fun k ↦ ?_
  rw [map_comap_of_isPullback (I k) (IsPullback.of_hasPullback (q k) (q l)), hcompat]
  exact le_map_comap _ _

end AlgebraicGeometry.Scheme.IdealSheafData
