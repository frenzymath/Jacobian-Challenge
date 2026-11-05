import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Functions at field-valued points

A global function is nonzero at a field-valued point exactly when the point lies in its basic open.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace AlgebraicGeometry.Scheme

lemma isField_Γ_Spec {R : CommRingCat.{u}} (hR : IsField R) : IsField Γ(Spec R, ⊤) :=
  (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv.isField hR

/-- For a point `g : Spec R ⟶ Y` of a scheme with values in a field, a global function `a` of `Y`
does not vanish at the point, `g^♯ a ≠ 0`, if and only if the point lies in `D(a)`. -/
lemma Hom.appTop_ne_zero_iff_mem_basicOpen {R : CommRingCat.{u}} {Y : Scheme.{u}}
    (hR : IsField Γ(Spec R, ⊤)) (g : Spec R ⟶ Y) (a : Γ(Y, ⊤)) (x : Spec R) :
    g.appTop a ≠ 0 ↔ g.base x ∈ Y.basicOpen a := by
  rw [← Scheme.Hom.mem_preimage, Scheme.preimage_basicOpen_top]
  let := hR.toField
  by_cases h : g.appTop a = 0
  · rw [h, Scheme.basicOpen_zero]
    simp
  · rw [Scheme.basicOpen_of_isUnit (X := Spec R) (Ne.isUnit h)]
    simpa using h

end AlgebraicGeometry.Scheme
