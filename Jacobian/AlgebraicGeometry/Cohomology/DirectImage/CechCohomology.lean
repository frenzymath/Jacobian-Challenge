import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechComplex
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Jacobian.AlgebraicGeometry.Cohomology.Affine.Leray
import Jacobian.Algebra.Homology.CochainComplex.RestrictScalars
import Jacobian.Algebra.Homology.CochainComplex.Truncation

/-!
# Čech cohomology and higher direct images over affine bases

For a separated quasi-compact morphism to an affine scheme, an affine open cover
computes the global sections of higher direct images of quasi-coherent modules.
The comparison respects the scalar action from the base. Finite covers also give
an upper bound on the nonzero cohomology degrees, hence a bounded truncation
quasi-isomorphic to the explicit complex.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite TopCat.Presheaf

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
  {ι : Type u} (U : ι → X.Opens)

lemma cechModuleD_apply_forget (k : ℕ)
    (cochain : ∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) :
    cechModuleD f ℱ U k cochain = ((cechComplex U).obj
      (ℱ.presheafModuleCat ⋙ forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u})).d
        k (k + 1) cochain := by
  funext tuple
  rw [cechComplex_d_apply]
  simp only [cechModuleD, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    Function.comp_apply]
  rfl

/-- The cochains of the categorical Čech complex with scalars restricted from the base. -/
noncomputable def cechComplexFunctorXLinearEquiv (k : ℕ) :
    ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((cechComplexFunctor U).obj ℱ.presheafModuleCat).X k)) ≃ₗ[Γ(S, ⊤)]
      (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) :=
  { cechComplexFunctorXAddEquiv U ℱ.presheafModuleCat k with
    map_smul' a x := by
      funext y
      change ℱ.presheafModuleCat.map _ (cechComplexFunctorπ U ℱ.presheafModuleCat k y
        (f.appTop a • x)) = f.appTop a • ℱ.presheafModuleCat.map _
          (cechComplexFunctorπ U ℱ.presheafModuleCat k y x)
      rw [_root_.map_smul, _root_.map_smul] }


/-- The explicit and categorical Čech complexes agree after restricting scalars. -/
noncomputable def cechModuleComplexNatIso :
    ((ModuleCat.restrictScalars f.appTop.hom).mapHomologicalComplex _).obj
      ((cechComplexFunctor U).obj ℱ.presheafModuleCat) ≅ cechModuleComplexNat f ℱ U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ (cechComplexFunctorXLinearEquiv f ℱ U k).toModuleIso) (by
      rintro k _ rfl
      ext x : 2
      rw [cechModuleComplexNat_d]
      change cechModuleD f ℱ U k (cechComplexFunctorXLinearEquiv f ℱ U k x) =
        cechComplexFunctorXLinearEquiv f ℱ U (k + 1)
          ((((cechComplexFunctor U).obj ℱ.presheafModuleCat).d k (k + 1)).hom x)
      rw [cechModuleD_apply_forget]
      have h := congr($((cechComplexFunctorIso U ℱ.presheafModuleCat).hom.comm k (k + 1)) x)
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
      exact h)





/-- Homology of the explicit complex is the scalar restriction of categorical Čech homology. -/
noncomputable def cechModuleComplexHomologyIso (q : ℕ) :
    (cechModuleComplex f ℱ U).homology q ≅ (ModuleCat.restrictScalars f.appTop.hom).obj
      (((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) :=
  (cechModuleComplexNat f ℱ U).extendHomologyIso ComplexShape.embeddingUpNat rfl ≪≫
    HomologicalComplex.homologyMapIso (cechModuleComplexNatIso f ℱ U).symm q ≪≫
    ModuleCat.restrictScalarsHomologyIso _ _ q


/-- Leray comparison for the explicit complex, semilinear along the map on global functions. -/
theorem exists_homology_cechModuleComplex_equiv_H [IsAffine S] [IsSeparated f]
    (hU : ∀ i, IsAffineOpen (U i)) (hU' : iSup U = ⊤)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ∃ e : (cechModuleComplex f ℱ U).homology q ≃+ ℱ.H q,
      ∀ (a : Γ(S, ⊤)) x, e (a • x) = f.appTop a • e x := by
  obtain ⟨e₄⟩ := nonempty_cechComplex_linearEquiv_H_of_isSeparated f U hU hU' ℱ q
  let E := (cechModuleComplexHomologyIso f ℱ U q).toLinearEquiv
  refine ⟨E.toAddEquiv.trans e₄.toAddEquiv, fun a x ↦ ?_⟩
  change e₄ (E (a • x)) = f.appTop a • e₄ (E x)
  rw [E.map_smul]
  exact e₄.map_smul (f.appTop a) (E x)


/-- Over an affine base, explicit Čech homology is the sections of the higher direct image. -/
theorem nonempty_homology_cechModuleComplex_linearEquiv [IsAffine S] [QuasiCompact f]
    [IsSeparated f] [HasInjectiveResolutions X.Modules] (hU : ∀ i, IsAffineOpen (U i))
    (hU' : iSup U = ⊤) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty ((cechModuleComplex f ℱ U).homology q ≃ₗ[Γ(S, ⊤)]
      Γ((higherDirectImage f q).obj ℱ, ⊤)) := by
  obtain ⟨e, he⟩ := exists_homology_cechModuleComplex_equiv_H f ℱ U hU hU' q
  obtain ⟨g, hg⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H f ℱ q
  let G : Γ((higherDirectImage f q).obj ℱ, ⊤) ≃+ ℱ.H q := AddEquiv.ofBijective g.toAddMonoidHom hg
  have hG (y : Γ((higherDirectImage f q).obj ℱ, ⊤)) : G y = g y := rfl
  refine ⟨{ e.trans G.symm with
    map_smul' := fun a x ↦ G.injective ?_ }⟩
  change G (G.symm (e (a • x))) = G (a • G.symm (e x))
  rw [G.apply_symm_apply, hG, g.map_smulₛₗ, ← hG, G.apply_symm_apply, he]


/-- A nonempty finite affine cover makes the explicit complex exact outside its finite range. -/
theorem exactAt_cechModuleComplex [IsAffine S] [IsSeparated f] [Fintype ι] [Nonempty ι]
    (hU : ∀ i, IsAffineOpen (U i)) (hU' : iSup U = ⊤)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℤ)
    (hq : q < 0 ∨ Fintype.card ι ≤ q) : (cechModuleComplex f ℱ U).ExactAt q := by
  rcases hq with hq | hq
  · exact HomologicalComplex.extend_exactAt _ _ _ fun j hj ↦ by
      change (j : ℤ) = q at hj
      lia
  obtain ⟨q, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, by lia⟩
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  obtain ⟨e, -⟩ := exists_homology_cechModuleComplex_equiv_H f ℱ U hU hU' q
  have : Subsingleton (ℱ.H q) :=
    subsingleton_H_of_card_le Finset.univ Finset.univ_nonempty U (fun i _ ↦ hU i)
      (by rw [← hU', Finset.sup_univ_eq_iSup]) _
      (cechAcyclicOnAffines_of_isQuasicoherent ℱ) (by simpa using hq)
  have : Subsingleton ((cechModuleComplex f ℱ U).homology q) := e.injective.subsingleton
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ModuleCat.isZero_of_subsingleton _

section Truncation

variable [Fintype ι] [Nonempty ι]

/-- The bounded truncation of the explicit Čech complex at the affine-cover bound. -/
abbrev cechModuleComplexTrunc : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ :=
  (cechModuleComplex f ℱ U).truncLE ((Fintype.card ι : ℤ) - 1)

instance : (cechModuleComplexTrunc f ℱ U).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro degree degreeBound
  have coverCardPositive : (0 : ℤ) < Fintype.card ι := by
    have := Fintype.card_pos (α := ι)
    omega
  exact (((cechModuleComplex f ℱ U).truncLEXIso _ degree (by omega)).isZero_iff).2
    ((cechModuleComplex f ℱ U).isZero_of_isStrictlyGE 0 degree degreeBound)

/-- The inclusion of the bounded Čech truncation is a quasi-isomorphism. -/
theorem quasiIso_ιTruncLE_cechModuleComplex [IsAffine S] [IsSeparated f]
    (hU : ∀ index, IsAffineOpen (U index)) (hU_cover : iSup U = ⊤)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    QuasiIso ((cechModuleComplex f ℱ U).ιTruncLE ((Fintype.card ι : ℤ) - 1)) := by
  have : (cechModuleComplex f ℱ U).IsLE ((Fintype.card ι : ℤ) - 1) :=
    ((cechModuleComplex f ℱ U).isLE_iff _).2 fun degree degreeBound ↦
      exactAt_cechModuleComplex f ℱ U hU hU_cover degree (Or.inr (by omega))
  infer_instance

end Truncation

end AlgebraicGeometry.Scheme.Modules
