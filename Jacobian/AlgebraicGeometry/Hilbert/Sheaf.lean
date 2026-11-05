import Jacobian.AlgebraicGeometry.Hilbert.Basic
import Jacobian.AlgebraicGeometry.IdealSheaf.Descent
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over

/-!
# The Hilbert functor is an fppf sheaf

Effective descent of ideal sheaves glues compatible finite flat closed subschemes.
Finiteness, flatness, finite presentation and constant rank descend fpqc-locally.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- Finite flat closed subschemes of constant rank form an fppf sheaf. -/
theorem isSheaf_hilbertPresheaf (f : X ⟶ S) (d : ℕ) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (hilbertPresheaf f d) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro T R hR x hx
  let ι := { p : Σ Y : Over S, Y ⟶ T // R p.2 }
  let g : ∀ i : ι, i.1.1.left ⟶ T.left := fun i ↦ i.1.2.left
  have hg : Sieve.ofArrows _ g ∈ Scheme.fpqcTopology T.left := by
    refine Scheme.fpqcTopology.superset_covering ?_
      (Scheme.fppfTopology_le_fpqcTopology _ ((GrothendieckTopology.mem_over_iff _ _).1 hR))
    rintro Y h ⟨Z, k, l, hk, rfl⟩
    exact (Sieve.mem_ofArrows_iff ..).mpr ⟨⟨⟨Z, k⟩, hk⟩, l, rfl⟩
  let I : ∀ i : ι, (pullback f i.1.1.hom).IdealSheafData := fun i ↦ (x i.1.2 i.2).1
  have hI (i : ι) : IsHilbertSubscheme f d i.1.1 (I i) := (x i.1.2 i.2).2
  have hcompat : ∀ ⦃W : Scheme.{u}⦄ ⦃i j : ι⦄ (a : W ⟶ pullback f i.1.1.hom)
      (b : W ⟶ pullback f j.1.1.hom), a ≫ baseChangeMap f i.1.2 = b ≫ baseChangeMap f j.1.2 →
      (I i).comap a = (I j).comap b := by
    intro W i j a b hab
    have hfst {Y Y' : Over S} (φ : Y ⟶ Y') :
        baseChangeMap f φ ≫ pullback.fst f Y'.hom = pullback.fst f Y.hom :=
      pullback.lift_fst _ _ _
    have hsnd {Y Y' : Over S} (φ : Y ⟶ Y') :
        baseChangeMap f φ ≫ pullback.snd f Y'.hom = pullback.snd f Y.hom ≫ φ.left :=
      pullback.lift_snd _ _ _
    have hab₁ : a ≫ pullback.fst f i.1.1.hom = b ≫ pullback.fst f j.1.1.hom := by
      simpa only [Category.assoc, hfst] using congrArg (· ≫ pullback.fst f T.hom) hab
    have hab₂ : (a ≫ pullback.snd f i.1.1.hom) ≫ i.1.2.left =
        (b ≫ pullback.snd f j.1.1.hom) ≫ j.1.2.left := by
      simpa only [Category.assoc, hsnd] using congrArg (· ≫ pullback.snd f T.hom) hab
    have hW : (a ≫ pullback.snd f i.1.1.hom) ≫ i.1.1.hom =
        (b ≫ pullback.snd f j.1.1.hom) ≫ j.1.1.hom := by
      simpa only [Category.assoc, Over.w] using congrArg (· ≫ T.hom) hab₂
    let Z : Over S := Over.mk ((a ≫ pullback.snd f i.1.1.hom) ≫ i.1.1.hom)
    let g₁ : Z ⟶ i.1.1 := Over.homMk (a ≫ pullback.snd f i.1.1.hom)
    let g₂ : Z ⟶ j.1.1 := Over.homMk (b ≫ pullback.snd f j.1.1.hom) hW.symm
    have hcomm : g₁ ≫ i.1.2 = g₂ ≫ j.1.2 := by
      ext
      exact hab₂
    have key := congrArg Subtype.val (hx g₁ g₂ i.2 j.2 hcomm)
    let s : W ⟶ pullback f Z.hom := pullback.lift (a ≫ pullback.fst f i.1.1.hom) (𝟙 W) (by
      simp [Z, pullback.condition])
    have hs₁ : s ≫ baseChangeMap f g₁ = a := by
      apply pullback.hom_ext
      · rw [Category.assoc, hfst g₁]
        exact pullback.lift_fst _ _ _
      · rw [Category.assoc, hsnd g₁]
        exact pullback.lift_snd_assoc _ _ _ _ |>.trans (Category.id_comp _)
    have hs₂ : s ≫ baseChangeMap f g₂ = b := by
      apply pullback.hom_ext
      · rw [Category.assoc, hfst g₂]
        exact (pullback.lift_fst _ _ _).trans hab₁
      · rw [Category.assoc, hsnd g₂]
        exact pullback.lift_snd_assoc _ _ _ _ |>.trans (Category.id_comp _)
    rw [← hs₁, ← hs₂, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    exact congrArg (Scheme.IdealSheafData.comap · s) key
  obtain ⟨J, hJ, hfin, hflat, hfp, hdeg, huniq⟩ := isSheaf_fpqc_finiteLocallyFreeSubscheme g hg
    (pullback.snd f T.hom) d (fun i ↦ baseChangeMap f i.1.2) (fun i ↦ pullback.snd f i.1.1.hom)
    (fun i ↦ isPullback_baseChangeMap f i.1.2) I (fun i ↦ (hI i).1) (fun i ↦ (hI i).2.1)
    (fun i ↦ (hI i).2.2.1) (fun i ↦ (hI i).2.2.2) hcompat
  refine ⟨⟨J, hfin, hflat, hfp, hdeg⟩, fun Y h hh ↦ Subtype.ext (hJ ⟨⟨Y, h⟩, hh⟩), ?_⟩
  intro y hy
  refine Subtype.ext (huniq _ fun i ↦ ?_)
  exact congrArg Subtype.val (hy i.1.2 i.2)

/-- The Hilbert presheaf is a sheaf for the Zariski topology. -/
lemma isSheaf_zariskiTopology_hilbertPresheaf (f : X ⟶ S) (d : ℕ) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S) (hilbertPresheaf f d) := by
  have h := isSheaf_hilbertPresheaf f d
  rw [isSheaf_iff_isSheaf_of_type] at h ⊢
  refine Presieve.isSheaf_of_le _ (fun T R hR ↦ ?_) h
  rw [GrothendieckTopology.mem_over_iff] at hR ⊢
  exact Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage _ hR

end AlgebraicGeometry
