import Jacobian.AlgebraicGeometry.Modules.FreeComplex
import Jacobian.AlgebraicGeometry.Modules.LocallyFree

/-!
# Rank of a module sheaf over a field

A module sheaf on the spectrum of a field whose global sections are finite
dimensional is finite locally free of rank `r` exactly when its global sections
have dimension `r`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Module

namespace AlgebraicGeometry.Scheme.Modules

/-- Over a field, finite local freeness of a fixed rank is detected by global sections. -/
theorem isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj {R : CommRingCat.{u}}
    (hR : IsField R) (M : (Spec R).Modules)
    [Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M)] (r : ℕ) :
    M.IsFiniteLocallyFreeOfRank r ↔
      finrank R ((moduleSpecΓFunctor (R := R)).obj M) = r := by
  have := isEquivalence_moduleSpecΓFunctor hR
  let := hR.toField
  obtain ⟨hN, hNfin⟩ := finrank_moduleSpecΓFunctor_obj_free hR
    (Iso.refl (SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin r))))
  simp only [Fintype.card_ulift, Fintype.card_fin] at hN
  constructor
  · intro h
    obtain ⟨ι, U, hU, e⟩ := IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := r)
    obtain ⟨x⟩ : Nonempty (Spec R) := inferInstance
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hU.ge (Set.mem_univ x) : x ∈ ⨆ i, U i)
    have : Subsingleton (Spec (.of R)) := inferInstance
    have hUi : U i = ⊤ := by
      refine eq_top_iff.2 fun y _ ↦ ?_
      rwa [Subsingleton.elim y x]
    have he := e i
    rw [hUi] at he
    let inclusion := (⊤ : (Spec R).Opens).ι
    have : IsIso inclusion := inferInstanceAs (IsIso (Spec R).topIso.hom)
    let φ : M ≅ SheafOfModules.free (ULift.{u} (Fin r)) :=
      (restrictFunctorId.app M).symm ≪≫
        restrictCompIso M inclusion (inv inclusion) (𝟙 _) (IsIso.inv_hom_id inclusion) ≪≫
        (restrictFunctor _).mapIso he.some ≪≫ restrictFreeIso _ _
    simpa using (finrank_moduleSpecΓFunctor_obj_free hR φ).1
  · intro h
    have : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj
      (SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin r)))) := hNfin
    let e := (LinearEquiv.ofFinrankEq _ _ (h.trans hN.symm)).toModuleIso
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      ((moduleSpecΓFunctor (R := R)).preimageIso e).symm

end AlgebraicGeometry.Scheme.Modules
