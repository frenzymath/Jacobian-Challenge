import Jacobian.AlgebraicGeometry.Picard.Group

/-!
# Local triviality of Picard classes

Every Picard class is trivial on an open neighborhood of each point. Equality
of a pullback class with the identity is equivalent to triviality of the
pullback of its chosen invertible representative.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Pic

variable {source target : Scheme.{schemeUniverse}}

/-- A trivial pullback class has a representative isomorphic to the structure sheaf. -/
lemma nonempty_iso_unit_of_map_eq_one (morphism : source ⟶ target) {picardClass : target.Pic}
    (trivial : map morphism picardClass = 1) :
    Nonempty ((Modules.pullback morphism).obj
      ((fromSkeleton target.Modules).obj picardClass.val) ≅
        SheafOfModules.unit source.ringCatSheaf) := by
  obtain ⟨trivialization⟩ := eq_iff_nonempty_iso.mp trivial
  exact ⟨(mkIso _).symm ≪≫ trivialization ≪≫ oneIso⟩

/-- A Picard class restricts to the identity on an open neighborhood of every point. -/
lemma exists_map_iota_eq_one (picardClass : target.Pic) (point : target) :
    ∃ openSubset : target.Opens, point ∈ openSubset ∧ map openSubset.ι picardClass = 1 := by
  obtain ⟨openSubset, membership, ⟨trivialization⟩⟩ := picardClass.isInvertible.exists_isoUnit point
  exact ⟨openSubset, membership, ext (congr_toSkeleton_of_iso trivialization)⟩

end AlgebraicGeometry.Scheme.Pic
