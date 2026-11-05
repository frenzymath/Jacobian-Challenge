import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# Vanishing of cohomology on finite unions by Mayer-Vietoris

Let `F` be an abelian sheaf on a topological space `X` and `B` a class of open subsets of `X`
which is stable under binary intersections, such that the cohomology `H^q(U, F)` vanishes for
`q > 0` and `U` in `B`. Then the cohomology of `F` on a union of `n` members of `B` vanishes in
degrees `q ≥ n`.

The proof is by induction on `n`, using the Mayer-Vietoris sequence of the union
`U ∪ W` of a member `U` of `B` and a union `W` of `n - 1` members of `B`:
```
  H^{q - 1}(U ∩ W, F) ⟶ H^q(U ∪ W, F) ⟶ H^q(U, F) ⊕ H^q(W, F),
```
where `U ∩ W` is again a union of `n - 1` members of `B`.

For a quasi-coherent module on a separated scheme, with `B` the affine opens, this gives
the vanishing of its cohomology above the number of affine opens needed to cover the scheme.

## Main statements

- `TopCat.Sheaf.subsingleton_H'_finsetSup`: the vanishing on finite unions.
-/



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits TopologicalSpace

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- In the Mayer-Vietoris sequence of two opens `U` and `V`, if `H^q(U ∩ V, F)`,
`H^{q + 1}(U, F)` and `H^{q + 1}(V, F)` vanish, then so does `H^{q + 1}(U ∪ V, F)`. -/
lemma subsingleton_H'_sup {U V : Opens X} {q : ℕ}
    (h₁ : Subsingleton (F.H' q (U ⊓ V) : AddCommGrpCat.{u}))
    (h₂ : Subsingleton (F.H' (q + 1) U : AddCommGrpCat.{u}))
    (h₃ : Subsingleton (F.H' (q + 1) V : AddCommGrpCat.{u})) :
    Subsingleton (F.H' (q + 1) (U ⊔ V) : AddCommGrpCat.{u}) := by
  let S := Opens.mayerVietorisSquare U V
  have hex := (ShortComplex.ab_exact_iff _).1 ((S.sequence_exact F q (q + 1) rfl).exact 2)
  have h₂' : Subsingleton ↑(F.H' (q + 1) S.X₂ : AddCommGrpCat.{u}) := h₂
  have h₃' : Subsingleton ↑(F.H' (q + 1) S.X₃ : AddCommGrpCat.{u}) := h₃
  have hb : Subsingleton ↑(F.H' (q + 1) S.X₂ ⊞ F.H' (q + 1) S.X₃ : AddCommGrpCat.{u}) :=
    (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.subsingleton_congr.2
      inferInstance
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, hy⟩ := hex x (@Subsingleton.elim _ hb _ _)
  rw [← hy, @Subsingleton.elim _ h₁ y 0, map_zero]

/-- **Vanishing of cohomology on finite unions.** Let `B` be a class of opens stable under
binary intersections on which the cohomology of `F` vanishes in positive degrees. Then for a
nonempty finite family `U i`, `i ∈ s`, of members of `B`, the cohomology of `F` on the union of
the `U i` vanishes in degrees `q ≥ #s`. -/
theorem subsingleton_H'_finsetSup (B : Opens X → Prop) (hB : ∀ U V, B U → B V → B (U ⊓ V))
    (hF : ∀ U, B U → ∀ q, Subsingleton (F.H' (q + 1) U : AddCommGrpCat.{u}))
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) :
    ∀ (U : ι → Opens X), (∀ i ∈ s, B (U i)) → ∀ q, s.card ≤ q →
      Subsingleton (F.H' q (s.sup U) : AddCommGrpCat.{u}) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro U hU q hq
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by simp at hq; omega⟩
    rw [Finset.sup_singleton]
    exact hF _ (hU a (Finset.mem_singleton_self a)) q
  | cons a s ha hs ih =>
    intro U hU q hq
    rw [Finset.card_cons] at hq
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [Finset.sup_cons]
    refine subsingleton_H'_sup F ?_ (hF _ (hU a (Finset.mem_cons_self a s)) q) ?_
    · rw [Finset.sup_inf_distrib_left]
      exact ih (fun i ↦ U a ⊓ U i)
        (fun i hi ↦ hB _ _ (hU a (Finset.mem_cons_self a s)) (hU i (Finset.mem_cons_of_mem hi)))
        q (by omega)
    · exact ih U (fun i hi ↦ hU i (Finset.mem_cons_of_mem hi)) (q + 1) (by omega)

section Free

open Opposite Abelian

/-- The free abelian sheaf `ℤ_U` on an open subset `U`, the sheafification of
`V ↦ ℤ[Hom(V, U)]`. It corepresents the sections over `U`
(`TopCat.Sheaf.homFreeSheafEquiv`), and `H^n(U, F) = Ext^n(ℤ_U, F)` is
`CategoryTheory.Sheaf.H' F n U`. -/
noncomputable abbrev freeSheaf (U : Opens X) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (presheafToSheaf _ _).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- The morphisms `ℤ_U ⟶ G` are the sections of `G` over `U`. -/
noncomputable def homFreeSheafEquiv (U : Opens X)
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (freeSheaf U ⟶ G) ≃ G.obj.obj (op U) :=
  ((sheafificationAdjunction _ _).homEquiv _ _).trans
    (((AddCommGrpCat.adj.whiskerRight (C := (Opens X)ᵒᵖ)).homEquiv _ _).trans yonedaEquiv)

lemma homFreeSheafEquiv_comp (U : Opens X)
    {G G' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (φ : freeSheaf U ⟶ G)
    (g : G ⟶ G') :
    homFreeSheafEquiv U G' (φ ≫ g) = g.hom.app (op U) (homFreeSheafEquiv U G φ) := by
  simp only [homFreeSheafEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
  rfl

/-- If `g : I ⟶ Q` is surjective on the sections over `U`, then the induced map
`H^0(U, I) ⟶ H^0(U, Q)` is surjective. -/
lemma surjective_comp_mk₀_of_surjective
    {I Q : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (g : I ⟶ Q) (U : Opens X)
    (hg : Function.Surjective (g.hom.app (op U))) :
    Function.Surjective fun x : Ext (freeSheaf U) I 0 ↦ x.comp (Ext.mk₀ g) (add_zero 0) := by
  intro y
  obtain ⟨t, ht⟩ := hg (homFreeSheafEquiv U Q (Ext.homEquiv₀ y))
  refine ⟨Ext.mk₀ ((homFreeSheafEquiv U I).symm t), ?_⟩
  dsimp only
  rw [Ext.mk₀_comp_mk₀, ← Ext.mk₀_homEquiv₀_apply y]
  congr 1
  apply (homFreeSheafEquiv U Q).injective
  rw [homFreeSheafEquiv_comp, Equiv.apply_symm_apply, ht]

/-- The free abelian sheaf on the whole space is the constant sheaf `ℤ`. -/
noncomputable def freeSheafTopIso :
    freeSheaf (⊤ : Opens X) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  (presheafToSheaf _ _).mapIso <|
    Functor.isoWhiskerRight (NatIso.ofComponents (fun V ↦ Equiv.toIso
        { toFun := fun _ ↦ PUnit.unit
          invFun := fun _ ↦ homOfLE le_top
          left_inv := fun _ ↦ Subsingleton.elim (α := V.unop ⟶ (⊤ : Opens X)) _ _
          right_inv := fun _ ↦ rfl }) :
          yoneda.obj (⊤ : Opens X) ≅ (Functor.const _).obj PUnit.{u + 1})
      AddCommGrpCat.free ≪≫
      Functor.constComp _ _ _ ≪≫
      (Functor.const _).mapIso ((FreeAbelianGroup.uniqueEquiv PUnit).trans
        AddEquiv.ulift.symm).toAddCommGrpIso

/-- The cohomology `H^n(X, F)` of the whole space is the cohomology `H^n(⊤, F)` of the open
subset `⊤`: the constant sheaf `ℤ` is the free abelian sheaf on `⊤`. -/
lemma subsingleton_H_of_subsingleton_H' {n : ℕ}
    (h : Subsingleton (F.H' n ⊤ : AddCommGrpCat.{u})) :
    Subsingleton (CategoryTheory.Sheaf.H F n) := by
  have h' : Subsingleton (Ext (freeSheaf (⊤ : Opens X)) F n) := h
  refine ⟨fun x y ↦ ?_⟩
  let e := freeSheafTopIso (X := X)
  have key (z : CategoryTheory.Sheaf.H F n) :
      z = (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp z (zero_add n)) (zero_add n) := by
    rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Iso.inv_hom_id,
      Ext.mk₀_id_comp]
  rw [key x, key y, Subsingleton.elim ((Ext.mk₀ e.hom).comp x (zero_add n))
    ((Ext.mk₀ e.hom).comp y (zero_add n))]

end Free

end TopCat.Sheaf
