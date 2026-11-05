import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Explicit cohomology of complexes of abelian groups

The homology object identifies with the quotient of cocycles by
coboundaries. A cycle maps to the class of its underlying element.
-/

noncomputable section
universe u

open CategoryTheory Limits

namespace CochainComplex

/-- The cohomology of a complex `C` of abelian groups in degree `n + 1`, as the explicit quotient
of the cocycles by the coboundaries. -/
noncomputable def abHomologySuccAddEquiv (C : CochainComplex Ab.{u} ℕ) (n : ℕ) :
    C.homology (n + 1) ≃+ AddMonoidHom.ker (C.sc' n (n + 1) (n + 2)).g.hom ⧸
      AddMonoidHom.range (C.sc' n (n + 1) (n + 2)).abToCycles :=
  (C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp) ≪≫
    (C.sc' n (n + 1) (n + 2)).abHomologyIso).addCommGroupIsoToAddEquiv

lemma abHomologySuccAddEquiv_homologyπ (C : CochainComplex Ab.{u} ℕ) (n : ℕ)
    (c : C.cycles (n + 1)) :
    abHomologySuccAddEquiv C n (C.homologyπ (n + 1) c) =
      QuotientAddGroup.mk ⟨C.iCycles (n + 1) c, by
        change (C.iCycles (n + 1) ≫ C.d (n + 1) (n + 2)) c = 0
        rw [HomologicalComplex.iCycles_d]; rfl⟩ := by
  let S := C.sc' n (n + 1) (n + 2)
  have key : C.homologyπ (n + 1) ≫
      (C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom ≫ S.abHomologyIso.hom =
      (C.cyclesIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom ≫
        S.abLeftHomologyData.cyclesIso.hom ≫ S.abLeftHomologyData.π := by
    have h1 : C.homologyπ (n + 1) ≫
        (C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom =
        (C.cyclesIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom ≫ S.homologyπ :=
      ShortComplex.homologyπ_naturality _
    rw [← Category.assoc, h1, Category.assoc]
    exact congrArg _ S.abLeftHomologyData.homologyπ_comp_homologyIso_hom
  have hi : (S.abLeftHomologyData.cyclesIso.hom ≫ S.abLeftHomologyData.i)
      ((C.cyclesIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom c) = C.iCycles (n + 1) c := by
    rw [S.abLeftHomologyData.cyclesIso_hom_comp_i, ← ConcreteCategory.comp_apply,
      HomologicalComplex.cyclesIsoSc'_hom_iCycles]
    rfl
  calc abHomologySuccAddEquiv C n (C.homologyπ (n + 1) c)
      = (C.homologyπ (n + 1) ≫
          (C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).hom ≫
            S.abHomologyIso.hom) c := rfl
    _ = _ := by
      rw [key]
      exact congrArg (QuotientAddGroup.mk' _) (Subtype.ext hi)

end CochainComplex
