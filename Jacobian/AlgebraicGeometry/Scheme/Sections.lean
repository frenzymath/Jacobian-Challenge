import Mathlib.AlgebraicGeometry.Restrict

/-!
# Restrictions of sections to open subschemes

Restriction to nested open subsets is compatible with the canonical description
of global sections on an open subscheme. Sections become units on basic opens.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicGeometry

lemma Scheme.homOfLE_appTop_topIso_inv {scheme : Scheme} {smaller larger : scheme.Opens}
    (inclusion : smaller ≤ larger) (sectionValue : Γ(scheme, larger)) :
    (scheme.homOfLE inclusion).appTop (larger.topIso.inv sectionValue) =
      smaller.topIso.inv (scheme.presheaf.map (homOfLE inclusion).op sectionValue) := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
  change (scheme.presheaf.map _ ≫ scheme.presheaf.map _) sectionValue =
    (scheme.presheaf.map _ ≫ scheme.presheaf.map _) sectionValue
  rw [← Functor.map_comp]
  erw [← Functor.map_comp]
  rfl

lemma Scheme.presheaf_map_map {scheme : Scheme} {larger middle smaller : scheme.Opens}
    (first : middle ≤ larger) (second : smaller ≤ middle) (sectionValue : Γ(scheme, larger)) :
    scheme.presheaf.map (homOfLE second).op
        (scheme.presheaf.map (homOfLE first).op sectionValue) =
      scheme.presheaf.map (homOfLE (second.trans first)).op sectionValue := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma Scheme.isUnit_map_of_le_basicOpen {scheme : Scheme} {larger smaller : scheme.Opens}
    (sectionValue : Γ(scheme, larger)) (inclusion : smaller ≤ scheme.basicOpen sectionValue) :
    IsUnit (scheme.presheaf.map
      (homOfLE (inclusion.trans (scheme.basicOpen_le sectionValue))).op sectionValue) := by
  have unit := (RingedSpace.isUnit_res_basicOpen scheme.toRingedSpace sectionValue).map
    (scheme.presheaf.map (homOfLE inclusion).op).hom
  exact (scheme.presheaf_map_map (scheme.basicOpen_le sectionValue) inclusion sectionValue) ▸ unit

lemma Scheme.eq_of_map_eq_of_eq {scheme : Scheme} {larger smaller : scheme.Opens}
    (equality : smaller = larger) {first second : Γ(scheme, larger)}
    (restricted : scheme.presheaf.map (homOfLE equality.le).op first =
      scheme.presheaf.map (homOfLE equality.le).op second) : first = second := by
  subst equality
  simpa using restricted

end AlgebraicGeometry
