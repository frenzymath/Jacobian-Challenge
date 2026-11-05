import Jacobian.AlgebraicGeometry.IdealSheaf.Curve
import Jacobian.AlgebraicGeometry.IdealSheaf.RelativeCartierFiber

/-!
# Finiteness of divisors on proper relative curves

A relative effective Cartier divisor on a proper smooth relative curve is
finite, flat and locally of finite presentation over the base.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}}

/-- A flat effective Cartier divisor on a smooth relative curve is locally quasi-finite. -/
theorem IsInvertible.locallyQuasiFinite_subschemeι_comp_of_flat (π : X ⟶ S)
    [SmoothOfRelativeDimension 1 π] {J : X.IdealSheafData} (hJ : J.IsInvertible)
    (hflat : Flat (J.subschemeι ≫ π)) : LocallyQuasiFinite (J.subschemeι ≫ π) := by
  refine LocallyQuasiFinite.of_fiberToSpecResidueField _ fun s ↦ ?_
  have h := IsPullback.of_hasPullback π (S.fromSpecResidueField s)
  have sq : IsPullback (pullback.snd (pullback.fst π (S.fromSpecResidueField s)) J.subschemeι)
      (pullback.fst (pullback.fst π (S.fromSpecResidueField s)) J.subschemeι ≫
        pullback.snd π (S.fromSpecResidueField s))
      (J.subschemeι ≫ π) (S.fromSpecResidueField s) :=
    (IsPullback.of_hasPullback _ J.subschemeι).flip.paste_vert h
  have : SmoothOfRelativeDimension 1 (pullback.snd π (S.fromSpecResidueField s)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback h ‹_›
  have := (hJ.comap_of_isPullback hflat h).locallyQuasiFinite_subschemeι_comp
    (K := S.residueField s) (pullback.snd π (S.fromSpecResidueField s))
  have H : LocallyQuasiFinite (pullback.fst (pullback.fst π (S.fromSpecResidueField s))
      J.subschemeι ≫ pullback.snd π (S.fromSpecResidueField s)) := by
    rw [← comapIso_inv_subschemeι, Category.assoc]
    infer_instance
  rw [Scheme.Hom.fiberToSpecResidueField, ← sq.isoPullback_inv_snd]
  have : IsOpenImmersion sq.isoPullback.inv := inferInstance
  have H' : LocallyQuasiFinite sq.isoPullback.inv := inferInstance
  exact MorphismProperty.comp_mem @LocallyQuasiFinite _ _ H' H

/-- A flat effective Cartier divisor on a proper smooth relative curve is finite
and locally of finite presentation over the base. -/
theorem IsInvertible.isFinite_and_locallyOfFinitePresentation (π : X ⟶ S)
    [IsProper π] [SmoothOfRelativeDimension 1 π] {J : X.IdealSheafData} (hJ : J.IsInvertible)
    (hflat : Flat (J.subschemeι ≫ π)) :
    IsFinite (J.subschemeι ≫ π) ∧ LocallyOfFinitePresentation (J.subschemeι ≫ π) := by
  have := SmoothOfRelativeDimension.smooth 1 π
  have := hJ.locallyQuasiFinite_subschemeι_comp_of_flat π hflat
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _,
    hJ.isLocallyPrincipal.locallyOfFinitePresentation_subschemeι_comp π⟩

end AlgebraicGeometry.Scheme.IdealSheafData
