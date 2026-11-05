import Jacobian.AlgebraicGeometry.IdealSheaf.Flat
import Jacobian.AlgebraicGeometry.IdealSheaf.Gluing
import Jacobian.AlgebraicGeometry.Sites.FpqcPropertyDescent
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Fpqc descent of ideal sheaves and finite locally free subschemes

Ideal sheaves satisfy effective fpqc descent. The descended closed subscheme
retains a finite locally free projection of prescribed constant rank.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
variable {T : Scheme.{u}} {ι : Type w} {T' : ι → Scheme.{u}} (g : ∀ i, T' i ⟶ T)

namespace Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency.types false in

theorem eq_bot_of_comap_eq_bot_of_mem_fpqcTopology {X : Scheme.{u}} {S : Sieve X}
    (hS : S ∈ Scheme.fpqcTopology X) (K : X.IdealSheafData)
    (hK : ∀ ⦃Y : Scheme.{u}⦄ (h : Y ⟶ X), S h → K.comap h = ⊥) : K = ⊥ := by
  rw [← isIso_subschemeι_iff_eq_bot]
  refine Scheme.of_isPullback_of_mem_fpqcTopology (P := MorphismProperty.isomorphisms Scheme)
    hS K.subschemeι fun Y W h a b hh hab ↦ ?_
  have : IsIso (K.comap h).subschemeι := by
    rw [isIso_subschemeι_iff_eq_bot]
    exact hK h hh
  have : IsIso (pullback.fst h K.subschemeι) := by
    rw [← comapIso_inv_subschemeι]
    infer_instance
  change IsIso b
  rw [← hab.flip.isoPullback_hom_fst]
  infer_instance

theorem eq_of_forall_comap_eq_of_mem_fpqcTopology {X : Scheme.{u}} {S : Sieve X}
    (hS : S ∈ Scheme.fpqcTopology X) {J J' : X.IdealSheafData}
    (h : ∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ X), S f → J.comap f = J'.comap f) : J = J' := by
  suffices H : ∀ J J' : X.IdealSheafData,
      (∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ X), S f → J.comap f = J'.comap f) → J' ≤ J from
    le_antisymm (H J' J fun _ f hf ↦ (h f hf).symm) (H J J' h)
  intro J J' h
  rw [← J.ker_subschemeι]
  refine le_ker_of_comap_eq_bot _ (eq_bot_of_comap_eq_bot_of_mem_fpqcTopology
    (Scheme.fpqcTopology.pullback_stable J.subschemeι hS) _ fun Y k hk ↦ ?_)
  rw [← comap_comp, ← h _ hk, comap_comp, comap_subschemeι, comap_bot]

/-- Ideal sheaves are equal if their pullbacks to an fpqc covering family are equal. -/
theorem eq_of_comap_eq_of_mem_fpqcTopology {X : Scheme.{u}} {X' : ι → Scheme.{u}}
    (p : ∀ i, X' i ⟶ X) (hp : Sieve.ofArrows X' p ∈ Scheme.fpqcTopology X)
    {J J' : X.IdealSheafData} (h : ∀ i, J.comap (p i) = J'.comap (p i)) : J = J' := by
  refine eq_of_forall_comap_eq_of_mem_fpqcTopology hp fun Y f hf ↦ ?_
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff ..).mp hf
  rw [comap_comp, comap_comp, h i]

/-- Compatible ideal sheaves on an fpqc covering descend to an ideal sheaf.
Over affine opens the descended ideal is the intersection of the direct images
along a finite affine flat refinement; uniqueness permits gluing these ideals. -/
theorem exists_comap_eq_of_mem_fpqcTopology {X : Scheme.{u}} {X' : ι → Scheme.{u}}
    (p : ∀ i, X' i ⟶ X) (hp : Sieve.ofArrows X' p ∈ Scheme.fpqcTopology X)
    (I : ∀ i, (X' i).IdealSheafData)
    (hcompat : ∀ ⦃Y : Scheme.{u}⦄ ⦃i j : ι⦄ (a : Y ⟶ X' i) (b : Y ⟶ X' j),
      a ≫ p i = b ≫ p j → (I i).comap a = (I j).comap b) :
    ∃ J : X.IdealSheafData, ∀ i, J.comap (p i) = I i := by
  let Good (V : Scheme.{u}) (v : V ⟶ X) (K : V.IdealSheafData) : Prop :=
    ∀ ⦃Y : Scheme.{u}⦄ (h : Y ⟶ V) (i : ι) (a : Y ⟶ X' i), h ≫ v = a ≫ p i →
      K.comap h = (I i).comap a
  have huniq {V : Scheme.{u}} (v : V ⟶ X) {K K' : V.IdealSheafData} (hK : Good V v K)
      (hK' : Good V v K') : K = K' := by
    refine eq_of_forall_comap_eq_of_mem_fpqcTopology
      (Scheme.fpqcTopology.pullback_stable v hp) fun Y h hh ↦ ?_
    obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff ..).mp hh
    rw [hK h i a ha, hK' h i a ha]
  have hcomap {V : Scheme.{u}} (v : V ⟶ X) {K : V.IdealSheafData} (hK : Good V v K)
      {W : Scheme.{u}} (w : W ⟶ V) : Good W (w ≫ v) (K.comap w) := by
    intro Y h i a ha
    rw [← comap_comp]
    exact hK _ i a (by rw [Category.assoc, ha])
  have hex (V : Scheme.{u}) [IsAffine V] (v : V ⟶ X) : ∃ K, Good V v K := by
    obtain ⟨κ, W, f, _, _, _, hS, hcov⟩ := Scheme.exists_finite_affine_flat_of_mem_fpqcTopology
      (Scheme.fpqcTopology.pullback_stable v hp)
    choose i a ha using fun j ↦ (Sieve.mem_ofArrows_iff ..).mp (hS j)
    let K := ⨅ j, ((I (i j)).comap (a j)).map (f j)
    have hKf (l : κ) : K.comap (f l) = (I (i l)).comap (a l) := by
      refine comap_iInf_map_of_flat f _ (fun k l ↦ ?_) l
      rw [← comap_comp, ← comap_comp]
      apply hcompat
      rw [Category.assoc, Category.assoc, ← ha, ← ha, pullback.condition_assoc]
    refine ⟨K, fun Y h i' a' hh ↦ ?_⟩
    refine eq_of_forall_comap_eq_of_mem_fpqcTopology
      (Scheme.fpqcTopology.pullback_stable h hcov) fun Z c hc ↦ ?_
    obtain ⟨j, d, hd⟩ := (Sieve.mem_ofArrows_iff ..).mp hc
    rw [← comap_comp, hd, comap_comp, hKf, ← comap_comp, ← comap_comp]
    apply hcompat
    rw [Category.assoc, ← ha, ← Category.assoc, ← hd, Category.assoc, hh, Category.assoc]
  have hex' (U : X.affineOpens) : ∃ K, Good U.1.toScheme U.1.ι K :=
    haveI : IsAffine U.1.toScheme := U.2
    hex _ _
  choose K hK using hex'
  obtain ⟨J, hJ⟩ := exists_comap_ι_eq K fun U f ↦ huniq (X.affineBasicOpen f).1.ι
    (by
      have := hcomap _ (hK U) (X.homOfLE (X.basicOpen_le f))
      rw [Scheme.homOfLE_ι] at this
      exact this) (hK _)
  refine ⟨J, fun i ↦ eq_of_comap_ι_eq (p i) fun U W hW ↦ ?_⟩
  rw [← comap_comp, ← Scheme.Hom.resLE_comp_ι (p i) hW, comap_comp, hJ]
  exact hK U _ i _ (Scheme.Hom.resLE_comp_ι (p i) hW)

end Scheme.IdealSheafData

/-- A compatible fpqc family of finite locally free closed subschemes of constant
rank descends uniquely, with finiteness, flatness, finite presentation and rank. -/
theorem isSheaf_fpqc_finiteLocallyFreeSubscheme (hg : Sieve.ofArrows T' g ∈ Scheme.fpqcTopology T)
    {X : Scheme.{u}} (f : X ⟶ T) (d : ℕ)
    {X' : ι → Scheme.{u}} (p : ∀ i, X' i ⟶ X) (q : ∀ i, X' i ⟶ T' i)
    (hp : ∀ i, IsPullback (p i) (q i) f (g i)) (I : ∀ i, (X' i).IdealSheafData)
    (hfin : ∀ i, IsFinite ((I i).subschemeι ≫ q i))
    (hflat : ∀ i, Flat ((I i).subschemeι ≫ q i))
    (hfp : ∀ i, LocallyOfFinitePresentation ((I i).subschemeι ≫ q i))
    (hdeg : ∀ i (t : T' i), ((I i).subschemeι ≫ q i).finrank t = d)
    (hcompat : ∀ ⦃Y : Scheme.{u}⦄ ⦃i j : ι⦄ (a : Y ⟶ X' i) (b : Y ⟶ X' j),
      a ≫ p i = b ≫ p j → (I i).comap a = (I j).comap b) :
    ∃ J : X.IdealSheafData, (∀ i, J.comap (p i) = I i) ∧
      IsFinite (J.subschemeι ≫ f) ∧ Flat (J.subschemeι ≫ f) ∧
      LocallyOfFinitePresentation (J.subschemeι ≫ f) ∧
      (∀ t : T, (J.subschemeι ≫ f).finrank t = d) ∧
      ∀ J' : X.IdealSheafData, (∀ i, J'.comap (p i) = I i) → J' = J := by
  have hpX : Sieve.ofArrows X' p ∈ Scheme.fpqcTopology X := by
    refine Scheme.fpqcTopology.superset_covering ?_ (Scheme.fpqcTopology.pullback_stable f hg)
    intro Y h hh
    obtain ⟨i, k, hk⟩ := (Sieve.mem_ofArrows_iff ..).mp hh
    exact (Sieve.mem_ofArrows_iff ..).mpr ⟨i, (hp i).lift h k hk, ((hp i).lift_fst _ _ _).symm⟩
  obtain ⟨J, hJ⟩ := Scheme.IdealSheafData.exists_comap_eq_of_mem_fpqcTopology p hpX I hcompat
  obtain rfl : I = fun i ↦ J.comap (p i) := funext fun i ↦ (hJ i).symm
  have hsq : ∀ i, IsPullback ((J.comapIso (p i)).hom ≫ pullback.snd _ _)
      ((J.comap (p i)).subschemeι ≫ q i) (J.subschemeι ≫ f) (g i) := fun i ↦
    ((IsPullback.of_hasPullback (p i) J.subschemeι).flip.paste_vert (hp i)).of_iso'
      (J.comapIso (p i)) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp)
  have : MorphismProperty.DescendsAlong @IsFinite (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact
  have hfin' : IsFinite (J.subschemeι ≫ f) :=
    Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology hg _ _ _ hsq hfin
  have hflat' : Flat (J.subschemeι ≫ f) :=
    Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology hg _ _ _ hsq hflat
  have hfp' : LocallyOfFinitePresentation (J.subschemeι ≫ f) :=
    Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology hg _ _ _ hsq hfp
  refine ⟨J, fun _ ↦ rfl, hfin', hflat', hfp', fun t ↦ ?_, fun J' hJ' ↦
    Scheme.IdealSheafData.eq_of_comap_eq_of_mem_fpqcTopology p hpX hJ'⟩
  obtain ⟨Y, h, hh, y, rfl⟩ := Scheme.exists_mem_of_mem_fpqcTopology hg t
  obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff ..).mp hh
  rw [Scheme.Hom.comp_apply, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ (hsq i) (k y)]
  exact hdeg i (k y)

end AlgebraicGeometry
