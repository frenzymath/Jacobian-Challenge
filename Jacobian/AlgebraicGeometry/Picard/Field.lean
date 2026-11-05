import Jacobian.AlgebraicGeometry.Picard.Group

/-!
# Picard classes on one-point schemes

An invertible module sheaf on a one-point scheme is globally trivial, since
every neighborhood of the unique point is the whole scheme. In particular,
the Picard group of a field is trivial.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

namespace Modules

variable {X : Scheme.{u}}

/-- Every invertible module sheaf on a one-point scheme is trivial. -/
theorem nonempty_iso_unit_of_subsingleton [Subsingleton X] (x : X) (M : X.Modules)
    [invertible : M.IsInvertible] : Nonempty (M ≅ SheafOfModules.unit X.ringCatSheaf) := by
  obtain ⟨U, hx, ⟨e⟩⟩ := invertible.exists_isoUnit x
  obtain rfl : U = ⊤ := eq_top_iff.mpr fun y _ ↦ by rwa [Subsingleton.elim y x]
  exact ⟨((pullbackId X).app M).symm ≪≫
    (pullbackCongr (Scheme.toIso_inv_ι X).symm).app M ≪≫
    (pullbackComp _ _).symm.app M ≪≫
    (pullback X.topIso.inv).mapIso e ≪≫ pullbackObjUnitIso _⟩

end Modules

namespace Pic

/-- The Picard group of a field is trivial. -/
instance subsingleton_spec_field (k : Type u) [Field k] :
    Subsingleton (Spec (.of k)).Pic := by
  refine ⟨fun L L' ↦ eq_iff_nonempty_iso.2 ?_⟩
  obtain ⟨e⟩ := Modules.nonempty_iso_unit_of_subsingleton default
    ((fromSkeleton (Spec (.of k)).Modules).obj L.val)
  obtain ⟨e'⟩ := Modules.nonempty_iso_unit_of_subsingleton default
    ((fromSkeleton (Spec (.of k)).Modules).obj L'.val)
  exact ⟨e ≪≫ e'.symm⟩

end Pic

end AlgebraicGeometry.Scheme
