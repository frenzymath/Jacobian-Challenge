import Jacobian.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
import Jacobian.AlgebraicGeometry.Cohomology.Basic
import Jacobian.AlgebraicGeometry.Modules.Sections
import Jacobian.Topology.Sheaves.CechCohomology
import Jacobian.Topology.Sheaves.CechComparison
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Leray's theorem for affine covers

An open cover with affine finite intersections computes the actual cohomology of
a quasi-coherent module sheaf. The Čech-to-sheaf comparison is linear over the
global functions, so it can also be used over any affine base by restriction of
scalars.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{max u v}}

/-- The action of a global function on cohomology is the map induced by multiplication. -/
lemma H.smul_eq_map (ℱ : X.Modules) (q : ℕ) (r : Γ(X, ⊤)) (x : ℱ.H q) :
    r • x = H.map (ℱ.smulHom r) q x :=
  rfl

/-- The presheaf of abelian groups underlying `ℱ.presheafModuleCat` is that of `ℱ`. -/
noncomputable def presheafModuleCatCompForget₂Iso (ℱ : X.Modules) :
    ℱ.presheafModuleCat ⋙ forget₂
      (ModuleCat.{max u v} Γ(X, ⊤)) AddCommGrpCat.{max u v} ≅
      ((SheafOfModules.toSheaf.{max u v} X.ringCatSheaf).obj ℱ).obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl

/-- Multiplication by a global function on `ℱ.presheafModuleCat` is multiplication by it on
the underlying abelian sheaf of `ℱ`. -/
lemma whiskerRight_smul_presheafModuleCat (ℱ : X.Modules) (r : Γ(X, ⊤)) :
    Functor.whiskerRight (r • 𝟙 ℱ.presheafModuleCat)
      (forget₂ (ModuleCat.{max u v} Γ(X, ⊤)) AddCommGrpCat.{max u v}) ≫
        (presheafModuleCatCompForget₂Iso.{u, v} ℱ).hom =
      (presheafModuleCatCompForget₂Iso.{u, v} ℱ).hom ≫
        ((SheafOfModules.toSheaf.{max u v} X.ringCatSheaf).map (ℱ.smulHom r)).hom := by
  ext V x
  rfl

/-- The homology of Mathlib's Čech complex of `ℱ.presheafModuleCat` is the Čech cohomology of the
underlying abelian sheaf of `ℱ`. -/
noncomputable def cechComplexHomologyAddEquiv {ι : Type v} (U : ι → X.Opens)
    (ℱ : X.Modules)
    (q : ℕ) : ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃+
      (TopCat.Sheaf.cechCohomologyFunctor.{u, v} U q).obj
        ((SheafOfModules.toSheaf.{max u v} X.ringCatSheaf).obj ℱ) :=
  (TopCat.Presheaf.cechComplexFunctorHomologyIso.{v, u, max u v} U ℱ.presheafModuleCat q ≪≫
    HomologicalComplex.homologyMapIso ((TopCat.Presheaf.cechComplex U).mapIso
      (presheafModuleCatCompForget₂Iso.{u, v} ℱ)) q).addCommGroupIsoToAddEquiv

set_option maxHeartbeats 800000 in
/-- The identification `cechComplexHomologyAddEquiv` transports multiplication by a global
function to the map induced on Čech cohomology by multiplication on `ℱ`. -/
lemma cechComplexHomologyAddEquiv_smul {ι : Type v} (U : ι → X.Opens) (ℱ : X.Modules)
    (q : ℕ) (r : Γ(X, ⊤)) (x : ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) :
    cechComplexHomologyAddEquiv.{u, v} U ℱ q
        (r • x : ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) =
      (TopCat.Sheaf.cechCohomologyFunctor.{u, v} U q).map
        ((SheafOfModules.toSheaf.{max u v} X.ringCatSheaf).map (ℱ.smulHom r))
          (cechComplexHomologyAddEquiv.{u, v} U ℱ q x) := by
  have key : HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
      (Functor.whiskerRight (r • 𝟙 ℱ.presheafModuleCat)
        (forget₂ (ModuleCat.{max u v} Γ(X, ⊤)) AddCommGrpCat.{max u v}))) q ≫
      HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        (presheafModuleCatCompForget₂Iso.{u, v} ℱ).hom) q =
      HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        (presheafModuleCatCompForget₂Iso.{u, v} ℱ).hom) q ≫
      HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        ((SheafOfModules.toSheaf.{max u v} X.ringCatSheaf).map (ℱ.smulHom r)).hom) q := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, ← Functor.map_comp, whiskerRight_smul_presheafModuleCat.{u, v}]
  change HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
      (presheafModuleCatCompForget₂Iso.{u, v} ℱ).hom) q
      ((TopCat.Presheaf.cechComplexFunctorHomologyIso.{v, u, max u v}
        U ℱ.presheafModuleCat q).hom (r • x)) =
    HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
      ((SheafOfModules.toSheaf.{max u v} X.ringCatSheaf).map (ℱ.smulHom r)).hom) q
      (HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        (presheafModuleCatCompForget₂Iso.{u, v} ℱ).hom) q
        ((TopCat.Presheaf.cechComplexFunctorHomologyIso.{v, u, max u v}
          U ℱ.presheafModuleCat q).hom x))
  rw [TopCat.Presheaf.cechComplexFunctorHomologyIso_hom_smul.{v, u, max u v}]
  exact ConcreteCategory.congr_hom key _

set_option maxHeartbeats 800000 in
/-- An affine-intersection open cover computes quasi-coherent sheaf cohomology,
as a module over the global functions. -/
@[stacks 01XD]
theorem nonempty_cechComplex_linearEquiv_H {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty (((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃ₗ[Γ(X, ⊤)] ℱ.H q) := by
  classical
  have hU₀ (k : ℕ) (y : Fin (k + 1) → ι) : IsAffineOpen (⨅ l, U (y l)) := by
    have h := hU (Finset.univ.image y) (Finset.univ_nonempty.image y)
    convert h using 1
    refine le_antisymm (le_iInf₂ fun i hi ↦ ?_)
      (le_iInf fun l ↦ iInf₂_le (y l) (Finset.mem_image_of_mem y (Finset.mem_univ l)))
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hi
    exact iInf_le _ l
  obtain ⟨e⟩ := TopCat.Sheaf.nonempty_cechCohomologyFunctor_iso_functorH.{u, v} U hU'
    (cechAcyclicOnAffines X) (fun _ h ↦ cechAcyclicOnAffines_under_cokernel h)
    (fun _ hS h k y ↦ surjective_app_of_cechAcyclicOnAffines hS h (hU₀ k y)) q
  let F : (cechAcyclicOnAffines X).FullSubcategory :=
    ⟨(SheafOfModules.toSheaf.{max u v} X.ringCatSheaf).obj ℱ,
      cechAcyclicOnAffines_of_isQuasicoherent ℱ⟩
  let E : ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃+ ℱ.H q :=
    (cechComplexHomologyAddEquiv.{u, v} U ℱ q).trans (e.app F).addCommGroupIsoToAddEquiv
  have hE (r : Γ(X, ⊤)) (x : ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) :
      E (r • x) = H.map (ℱ.smulHom r) q (E x) := by
    have h := ConcreteCategory.congr_hom (e.hom.naturality (ObjectProperty.homMk
      ((SheafOfModules.toSheaf.{max u v} X.ringCatSheaf).map (ℱ.smulHom r)) : F ⟶ F))
        (cechComplexHomologyAddEquiv.{u, v} U ℱ q x)
    refine (congrArg (e.app F).hom
      (cechComplexHomologyAddEquiv_smul.{u, v} U ℱ q r x)).trans ?_
    exact h
  refine ⟨{ toAddEquiv := E, map_smul' := ?_ }⟩
  intro scalar cohomologyClass
  exact (hE scalar cohomologyClass).trans (H.smul_eq_map.{u, v} ℱ q scalar _).symm

/-- An affine open cover of a scheme separated over an affine base computes
quasi-coherent sheaf cohomology. -/
theorem nonempty_cechComplex_linearEquiv_H_of_isSeparated {S : Scheme.{max u v}}
    (f : X ⟶ S) [IsSeparated f] [IsAffine S] {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    (hU' : iSup U = ⊤) (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty (((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃ₗ[Γ(X, ⊤)] ℱ.H q) :=
  haveI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  nonempty_cechComplex_linearEquiv_H.{u, v} U
    (fun s hs ↦ IsAffineOpen.biInf (s : Set ι) s.finite_toSet hs (fun i _ ↦ hU i)) hU' ℱ q

end AlgebraicGeometry.Scheme.Modules
