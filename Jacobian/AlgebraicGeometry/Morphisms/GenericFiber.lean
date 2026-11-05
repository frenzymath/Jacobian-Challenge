import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Flat morphisms with reduced generic fibre

A flat scheme over an integral base is reduced if its generic fibre is reduced.
Morphisms from it to a separated target are determined by their generic-fibre
restrictions. No condition is required on the special fibres.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry

/-- The function-field point is a quasi-compact, scheme-theoretically
dominant test map of any integral scheme. -/
theorem genericPointMap_properties (Y : Scheme.{u}) [IsIntegral Y] :
    QuasiCompact (Y.fromSpecStalk (genericPoint Y)) ∧
      IsSchemeTheoreticallyDominant (Y.fromSpecStalk (genericPoint Y)) := by
  let g := Y.fromSpecStalk (genericPoint Y)
  haveI : Finite (Spec Y.functionField) := inferInstance
  haveI : QuasiCompact g := ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
  haveI : IsDominant g := by
    rw [isDominant_iff, denseRange_iff_closure_range, Set.eq_univ_iff_forall]
    intro y
    have hy : g (IsLocalRing.closedPoint Y.functionField) ⤳ y := by
      simpa only [g, Scheme.fromSpecStalk_closedPoint] using
        (genericPoint_spec Y).specializes (Set.mem_univ y)
    exact hy.mem_closed isClosed_closure (subset_closure ⟨_, rfl⟩)
  exact ⟨inferInstance, IsSchemeTheoreticallyDominant.of_isDominant g⟩

/-- A flat scheme over an integral base is reduced if its generic
base change is reduced. No condition is imposed on special fibres. -/
theorem isReduced_of_flat_genericPullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [IsIntegral Y]
    [IsReduced (pullback f (Y.fromSpecStalk (genericPoint Y)))] : IsReduced X := by
  obtain ⟨hqc, hdom⟩ := genericPointMap_properties Y
  letI := hqc
  letI := hdom
  exact IsSchemeTheoreticallyDominant.isReduced
    (pullback.fst f (Y.fromSpecStalk (genericPoint Y)))

/-- Maps into a separated target agree globally if they agree after the
generic base change of a flat scheme with reduced generic fibre. -/
theorem ext_of_flat_genericPullback {X Y Z S : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [IsIntegral Y]
    [IsReduced (pullback f (Y.fromSpecStalk (genericPoint Y)))]
    {a b : X ⟶ Z} (s : Z ⟶ S) [IsSeparated s]
    (hs : a ≫ s = b ≫ s)
    (hab : pullback.fst f (Y.fromSpecStalk (genericPoint Y)) ≫ a =
      pullback.fst f (Y.fromSpecStalk (genericPoint Y)) ≫ b) : a = b := by
  obtain ⟨hqc, hdom⟩ := genericPointMap_properties Y
  letI := hqc
  letI := hdom
  letI := isReduced_of_flat_genericPullback f
  exact ext_of_isDominant_of_isSeparated s hs
    (pullback.fst f (Y.fromSpecStalk (genericPoint Y))) hab

end AlgebraicGeometry
