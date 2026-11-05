import Jacobian.AlgebraicGeometry.Morphisms.FlatDescent
import Jacobian.AlgebraicGeometry.Sites.Fpqc

/-!
# Fpqc descent of morphism properties

Target-local properties which descend along faithfully flat quasi-compact morphisms
also descend along fpqc covering sieves and covering families.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme

section Descent

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
  [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]

set_option backward.isDefEq.respectTransparency.types false in

private lemma of_isPullback_of_mem_fpqcTopology_of_isAffine {T Z : Scheme.{u}} [IsAffine T]
    {S : Sieve T} (hS : S ∈ fpqcTopology T) (f : Z ⟶ T)
    (H : ∀ ⦃Y W : Scheme.{u}⦄ (h : Y ⟶ T) (a : W ⟶ Z) (b : W ⟶ Y), S h →
      IsPullback a b f h → P b) : P f := by
  rw [fpqcTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨R, hR, hle⟩ := hS
  obtain ⟨𝒰, _, rfl⟩ := mem_propQCPrecoverage_iff_exists_quasiCompactCover.mp hR
  obtain ⟨𝒱, φ, _, -⟩ : ∃ (𝒱 : Scheme.AffineCover.{u} @Flat T) (φ : 𝒱.cover ⟶ 𝒰.qculift),
      Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (φ.h₀ j) := QuasiCompactCover.exists_hom _
  have h𝒰 (index : 𝒰.qculift.I₀) : 𝒰.presieve₀ (𝒰.qculift.f index) := by
    rcases index with index | index
    · exact 𝒰.toPreZeroHypercover.presieve₀_f _
    · exact 𝒰.toPreZeroHypercover.presieve₀_f _
  have : Small.{u} 𝒱.cover.I₀ := Countable.toSmall (α := 𝒱.I₀)
  let p : ∐ 𝒱.cover.X ⟶ T := Sigma.desc 𝒱.cover.f
  have hflat : Flat p := by
    have : ∀ j, Flat (𝒱.cover.f j) := 𝒱.map_prop
    infer_instance
  have : Finite 𝒱.cover.I₀ := ‹Finite 𝒱.I₀›
  have : IsAffine (∐ 𝒱.cover.X) := inferInstance
  have hp : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) p :=
    ⟨⟨Surjective.sigmaDesc_of_union_range_eq_univ 𝒱.cover.iUnion_range, hflat⟩, inferInstance⟩
  refine MorphismProperty.of_pullback_fst_of_descendsAlong (P := P) hp ?_
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) (sigmaOpenCover _)]
  intro j
  have hsq := (IsPullback.of_hasPullback (pullback.fst p f) (Sigma.ι 𝒱.cover.X j)).paste_horiz
    (IsPullback.of_hasPullback p f).flip
  have hj : Sigma.ι 𝒱.cover.X j ≫ p = 𝒱.cover.f j := Sigma.ι_desc _ _
  rw [hj] at hsq
  refine H _ _ _ ?_ hsq
  rw [← φ.w₀ j]
  exact S.downward_closed (hle _ _ (h𝒰 (φ.s₀ j))) _

set_option backward.isDefEq.respectTransparency.types false in

/-- A target-local morphism property descending along faithfully flat quasi-compact
morphisms descends along every fpqc covering sieve. -/
lemma of_isPullback_of_mem_fpqcTopology {T Z : Scheme.{u}} {S : Sieve T}
    (hS : S ∈ fpqcTopology T) (f : Z ⟶ T)
    (H : ∀ ⦃Y W : Scheme.{u}⦄ (h : Y ⟶ T) (a : W ⟶ Z) (b : W ⟶ Y), S h →
      IsPullback a b f h → P b) : P f := by
  refine IsZariskiLocalAtTarget.of_openCover T.affineCover fun i ↦ ?_
  refine of_isPullback_of_mem_fpqcTopology_of_isAffine
    (fpqcTopology.pullback_stable (T.affineCover.f i) hS) _ fun Y W h a b hh hab ↦ ?_
  exact H _ _ _ hh (hab.paste_horiz (IsPullback.of_hasPullback f (T.affineCover.f i)))

set_option backward.isDefEq.respectTransparency.types false in

/-- Descent of a base-change-stable morphism property along an fpqc covering family. -/
lemma of_isPullback_of_ofArrows_mem_fpqcTopology [P.IsStableUnderBaseChange] {T Z : Scheme.{u}}
    {ι : Type*} {T' : ι → Scheme.{u}} {g : ∀ i, T' i ⟶ T}
    (hg : Sieve.ofArrows T' g ∈ fpqcTopology T) (f : Z ⟶ T) {Z' : ι → Scheme.{u}}
    (a : ∀ i, Z' i ⟶ Z) (b : ∀ i, Z' i ⟶ T' i) (hab : ∀ i, IsPullback (a i) (b i) f (g i))
    (H : ∀ i, P (b i)) : P f := by
  refine of_isPullback_of_mem_fpqcTopology hg f fun Y W h a' b' hh hpb ↦ ?_
  obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hh
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_right' hpb (hab i)) (H i)

end Descent

end AlgebraicGeometry.Scheme
