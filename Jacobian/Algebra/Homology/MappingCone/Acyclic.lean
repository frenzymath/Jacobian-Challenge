import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Quasi-isomorphisms and acyclic mapping cones

A map of cochain complexes is a quasi-isomorphism precisely when its mapping cone is acyclic.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CochainComplex.mappingCone

open CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]

/-- A morphism `φ : K ⟶ L` of `ℤ`-indexed cochain complexes is a quasi-isomorphism if and only
if its mapping cone `mappingCone φ` is acyclic. The proof uses the distinguished triangle
```
  K ──φ──▶ L ──inr φ──▶ mappingCone φ ──triangle δ──▶ K⟦1⟧     (distinguished in K(C))
```
in the homotopy category: `φ` is a quasi-isomorphism if and only if the third vertex of this
triangle is acyclic. -/
lemma quasiIso_iff_acyclic {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    QuasiIso φ ↔ (mappingCone φ).Acyclic := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic,
    ← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact (HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ)

end CochainComplex.mappingCone
