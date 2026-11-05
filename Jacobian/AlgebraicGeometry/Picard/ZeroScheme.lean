import Jacobian.AlgebraicGeometry.IdealSheaf.CanonicalSection
import Jacobian.AlgebraicGeometry.Picard.Counit
import Jacobian.AlgebraicGeometry.Picard.Descent
import Jacobian.AlgebraicGeometry.Picard.Divisors

/-!
# Recovering normalized Picard classes from zero schemes

If evaluation of a line bundle has an effective Cartier zero scheme, the
normalized class of the corresponding divisor line bundle is the original
class. Thus zero schemes distinguish normalized classes whenever their
direct images are invertible. This also gives the inverse identity for the
Abel map on zero schemes lying in a finite flat Hilbert functor.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme

variable {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

/-- Normalization fixes classes already trivial along the section. -/
lemma normalizePicardClass_eq_self (T : Over S)
    (L : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T)) :
    normalizePicardClass f σ hσ T L.1 = L := by
  apply Subtype.ext
  dsimp only [normalizePicardClass]
  rw [L.2, inv_one, Pic.map_one, mul_one]

/-- Tensoring by a line bundle pulled back from the base does not change normalization. -/
lemma normalizePicardClass_mul_map (T : Over S) (L : (pullback f T.hom).Pic)
    (A : T.left.Pic) :
    normalizePicardClass f σ hσ T (L * Pic.map (pullback.snd f T.hom) A) =
      normalizePicardClass f σ hσ T L := by
  apply Subtype.ext
  let restriction := Pic.mapHom (sectionBaseChange f σ hσ T)
  let fromBase := Pic.mapHom (pullback.snd f T.hom)
  have retract : restriction (fromBase A) = A := by
    simp only [restriction, fromBase, Pic.mapHom_apply, ← Pic.map_comp,
      sectionBaseChange_snd, Pic.map_id]
  change (L * fromBase A) * fromBase ((restriction (L * fromBase A))⁻¹) =
    L * fromBase ((restriction L)⁻¹)
  simp only [map_mul, retract, mul_inv_rev, map_inv]
  simp [mul_assoc]

/-- A normalized class presented by a line bundle with a base twist is the
normalization of that line bundle. -/
theorem normalizePicardClass_eq_of_iso_tensorObj (T : Over S)
    (L : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T))
    (P : (pullback f T.hom).Modules) (N : T.left.Modules) [P.IsInvertible] [N.IsInvertible]
    (comparison : (fromSkeleton _).obj L.1.val ≅
      P ⊗ (Modules.pullback (pullback.snd f T.hom)).obj N) :
    normalizePicardClass f σ hσ T (Pic.mk P) = L := by
  have classEquality : L.1 = Pic.mk P * Pic.map (pullback.snd f T.hom) (Pic.mk N) := by
    rw [Pic.map_mk, ← Pic.mk_tensorObj, ← Pic.mk_fromSkeleton L.1]
    exact (Pic.mk_eq_mk_iff _ _).mpr ⟨comparison⟩
  have normalizedEquality := congrArg (normalizePicardClass f σ hσ T) classEquality
  rw [normalizePicardClass_eq_self f σ hσ T L,
    normalizePicardClass_mul_map] at normalizedEquality
  exact normalizedEquality.symm

/-- The divisor line bundle of a regular evaluation map recovers the normalized class. -/
theorem normalize_zeroLocus_directImageCounit (T : Over S)
    (L : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T))
    [((Modules.pushforward (pullback.snd f T.hom)).obj
      ((fromSkeleton _).obj L.1.val)).IsInvertible]
    (regular : (Pic.directImageCounit f T L.1).zeroLocus.IsInvertible) :
    letI := regular.isInvertible_toModules
    normalizePicardClass f σ hσ T
      (Pic.mk (Pic.directImageCounit f T L.1).zeroLocus.toModulesᵛ) = L := by
  letI := regular.isInvertible_toModules
  obtain ⟨comparison⟩ :=
    Modules.Hom.nonempty_iso_dual_toModules_tensorObj (Pic.directImageCounit f T L.1) regular
  exact normalizePicardClass_eq_of_iso_tensorObj f σ hσ T L _ _ comparison

/-- Equal regular evaluation zero schemes give equal normalized Picard classes. -/
theorem eq_of_zeroLocus_directImageCounit_eq (T : Over S)
    (L L' : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T))
    [((Modules.pushforward (pullback.snd f T.hom)).obj
      ((fromSkeleton _).obj L.1.val)).IsInvertible]
    [((Modules.pushforward (pullback.snd f T.hom)).obj
      ((fromSkeleton _).obj L'.1.val)).IsInvertible]
    (regular : (Pic.directImageCounit f T L.1).zeroLocus.IsInvertible)
    (equality : (Pic.directImageCounit f T L.1).zeroLocus =
      (Pic.directImageCounit f T L'.1).zeroLocus) : L = L' := by
  obtain ⟨comparison⟩ :=
    Modules.Hom.nonempty_iso_dual_toModules_tensorObj (Pic.directImageCounit f T L.1) regular
  obtain ⟨comparison'⟩ := Modules.Hom.nonempty_iso_dual_toModules_tensorObj
    (Pic.directImageCounit f T L'.1) (equality ▸ regular)
  rw [← equality] at comparison'
  exact picardFunctorNormalized_eq_of_iso_tensorObj f σ hσ L L' _ _ _ comparison comparison'

/-- The Abel map sends a regular evaluation zero scheme back to its normalized class. -/
theorem hilbertToPicardNormalized_zeroLocus [SmoothOfRelativeDimension 1 f]
    (d : ℕ) (T : Over S)
    (L : (picardFunctorNormalized f σ hσ).toFunctor.obj (.op T))
    [((Modules.pushforward (pullback.snd f T.hom)).obj
      ((fromSkeleton _).obj L.1.val)).IsInvertible]
    (D : (hilbertPresheaf f d).obj (.op T))
    (equality : (Pic.directImageCounit f T L.1).zeroLocus = D.1) :
    hilbertToPicardNormalized f σ hσ d T D = L := by
  letI : D.1.toModules.IsInvertible := D.2.isInvertible.isInvertible_toModules
  have regular : (Pic.directImageCounit f T L.1).zeroLocus.IsInvertible :=
    equality.symm ▸ D.2.isInvertible
  change normalizePicardClass f σ hσ T (Pic.mk D.1.toModulesᵛ) = L
  simpa only [equality] using normalize_zeroLocus_directImageCounit f σ hσ T L regular

end AlgebraicGeometry
