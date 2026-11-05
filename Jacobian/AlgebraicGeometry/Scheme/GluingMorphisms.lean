import Jacobian.AlgebraicGeometry.Gluing

/-!
# Gluing morphisms on open subsets

Morphisms agreeing on intersections glue on the union; the resulting morphism
is characterized by its restrictions to the members of the cover.
-/

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {indexType : Type*} {scheme source : Scheme.{schemeUniverse}} (opens : indexType → scheme.Opens)

noncomputable def Scheme.Opens.glueMorphismsOfTop (hU : ⨆ index, opens index = ⊤)
    (function : ∀ index, (opens index).toScheme ⟶ source)
    (hf : ∀ index secondIndex, scheme.homOfLE (inf_le_left : opens index ⊓ opens secondIndex ≤ opens index) ≫ function index =
      scheme.homOfLE (inf_le_right : opens index ⊓ opens secondIndex ≤ opens secondIndex) ≫ function secondIndex) :
    scheme ⟶ source :=
  (scheme.isoOfEq hU ≪≫ scheme.topIso).inv ≫ Scheme.Opens.glueMorphisms opens function hf

@[reassoc (attr := simp)]
lemma Scheme.Opens.ι_glueMorphismsOfTop (hU : ⨆ index, opens index = ⊤) (function : ∀ index, (opens index).toScheme ⟶ source)
    (hf : ∀ index secondIndex, scheme.homOfLE (inf_le_left : opens index ⊓ opens secondIndex ≤ opens index) ≫ function index =
      scheme.homOfLE (inf_le_right : opens index ⊓ opens secondIndex ≤ opens secondIndex) ≫ function secondIndex) (index : indexType) :
    (opens index).ι ≫ Scheme.Opens.glueMorphismsOfTop opens hU function hf = function index := by
  have hhom : (scheme.isoOfEq hU ≪≫ scheme.topIso).hom = (⨆ index, opens index).ι := by simp
  rw [glueMorphismsOfTop, ← scheme.homOfLE_ι (le_iSup opens index), ← hhom, Category.assoc,
    Iso.hom_inv_id_assoc, homOfLE_glueMorphisms]

lemma Scheme.Opens.hom_ext_of_iSup_eq_top (hU : ⨆ index, opens index = ⊤) (g₁ g₂ : scheme ⟶ source)
    (compatibility : ∀ index, (opens index).ι ≫ g₁ = (opens index).ι ≫ g₂) : g₁ = g₂ := by
  have hhom : (scheme.isoOfEq hU ≪≫ scheme.topIso).hom = (⨆ index, opens index).ι := by simp
  rw [← cancel_epi (scheme.isoOfEq hU ≪≫ scheme.topIso).hom]
  refine hom_ext_iSup opens _ _ fun index ↦ ?_
  rw [hhom, scheme.homOfLE_ι_assoc, scheme.homOfLE_ι_assoc, compatibility]

end AlgebraicGeometry
