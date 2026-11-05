import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechComplex
import Jacobian.Algebra.Category.ModuleCat.ChangeOfRings
import Jacobian.Algebra.Homology.Embedding.Map
import Mathlib.Algebra.Homology.Embedding.Extend
import Jacobian.AlgebraicGeometry.Scheme.Opens

/-!
# Base change of affine Čech complexes

For a cartesian square with affine bases, the explicit module-valued Čech
complex is identified with the scalar extension of the original complex.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits TensorProduct Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules)
  [Algebra Γ(S, ⊤) Γ(T, ⊤)]
  (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)

section Cech

open TopCat.Presheaf

variable {ι : Type u} (U : ι → X.Opens)

omit [Algebra Γ(S, ⊤) Γ(T, ⊤)] in
/-- Restriction commutes with the pullback of sections and the action of `Γ(T, ⊤)`. -/
lemma presheaf_map_smul_pullbackSection {V W : X.Opens} (h : V ≤ W) (b : Γ(T, ⊤))
    (m : sectionsModule f ℱ W) :
    sectionsModuleRestrict f' ((pullback g').obj ℱ) (g'.preimage_mono h)
      (b • pullbackSectionAddHom (structureMap := f) (structureMap' := f')
        (baseChangeMap' := g') ℱ W m) =
      b • pullbackSectionAddHom (structureMap := f) (structureMap' := f')
        (baseChangeMap' := g') ℱ V
        (sectionsModuleRestrict f ℱ h m) := by
  rw [LinearMap.map_smul]
  congr 1
  exact (pullbackSection_map g' h m).symm

/-- The identification of sections over equal opens. -/
noncomputable def sectionsModuleEqLinearEquiv {M : Scheme.{u}} {p : M ⟶ T} (𝒢 : M.Modules)
    {V W : M.Opens} (h : V = W) : sectionsModule p 𝒢 W ≃ₗ[Γ(T, ⊤)] sectionsModule p 𝒢 V where
  __ := sectionsModuleRestrict p 𝒢 h.le
  invFun := sectionsModuleRestrict p 𝒢 h.ge
  left_inv m := by
    change sectionsModuleRestrict p 𝒢 h.ge (sectionsModuleRestrict p 𝒢 h.le m) = m
    rw [sectionsModuleRestrict_comp, sectionsModuleRestrict_self]
  right_inv m := by
    change sectionsModuleRestrict p 𝒢 h.le (sectionsModuleRestrict p 𝒢 h.ge m) = m
    rw [sectionsModuleRestrict_comp, sectionsModuleRestrict_self]

/-- The base change of Čech cochains `B ⊗[A] Č^k(U, ℱ) ⟶ Č^k(g'⁻¹ U, g'^* ℱ)`,
`b ⊗ c ↦ (y ↦ b • g'^* (c y))`. -/
noncomputable def cechModuleBaseChange (k : ℕ) :
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) →ₗ[Γ(T, ⊤)]
      (∀ y : Fin (k + 1) → ι, sectionsModule f' ((pullback g').obj ℱ) (⨅ l, g' ⁻¹ᵁ U (y l))) :=
  LinearMap.pi fun y ↦
    (sectionsModuleEqLinearEquiv (p := f') ((pullback g').obj ℱ)
      (g'.preimage_iInf (fun l : Fin (k + 1) ↦ U (y l))).symm).toLinearMap ∘ₗ
        sectionsModuleBaseChange H ℱ hg (⨅ l, U (y l)) ∘ₗ
          (LinearMap.proj (R := Γ(S, ⊤)) y).baseChange Γ(T, ⊤)

lemma cechModuleBaseChange_tmul (k : ℕ) (b : Γ(T, ⊤))
    (c : ∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) (y : Fin (k + 1) → ι) :
    cechModuleBaseChange H ℱ hg U k (b ⊗ₜ c) y =
      sectionsModuleRestrict f' ((pullback g').obj ℱ)
        (g'.preimage_iInf (fun l : Fin (k + 1) ↦ U (y l))).symm.le
        (b • pullbackSectionAddHom (structureMap := f) (structureMap' := f')
          (baseChangeMap' := g') ℱ _ (c y)) := by
  simp only [cechModuleBaseChange, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.baseChange_tmul, LinearMap.coe_proj, Function.eval, sectionsModuleBaseChange_tmul]
  rfl

/-- **Base change of Čech cochains commutes with the differentials.** -/
theorem cechModuleBaseChange_d (k : ℕ)
    (x : Γ(T, ⊤) ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l)))) :
    cechModuleBaseChange H ℱ hg U (k + 1) ((cechModuleD f ℱ U k).baseChange Γ(T, ⊤) x) =
      cechModuleD f' ((pullback g').obj ℱ) (fun i ↦ g' ⁻¹ᵁ U i) k
        (cechModuleBaseChange H ℱ hg U k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b c =>
    funext y
    rw [LinearMap.baseChange_tmul, cechModuleBaseChange_tmul, cechModuleD_apply_apply,
      cechModuleD_apply_apply, map_sum, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_zsmul, smul_comm, map_zsmul, cechModuleBaseChange_tmul]
    congr 1
    rw [← presheaf_map_smul_pullbackSection, sectionsModuleRestrict_comp,
      sectionsModuleRestrict_comp]

/-- **Base change of Čech cochains is bijective** when `S`, `T` are affine, `ℱ` is
quasi-coherent and the finite intersections of the finitely many opens `U i` are affine. -/
theorem bijective_cechModuleBaseChange [IsAffine S] [IsAffine T]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] [Finite ι]
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l))) (k : ℕ) :
    Function.Bijective (cechModuleBaseChange H ℱ hg U k) := by
  classical
  have := Fintype.ofFinite ι
  let e := (TensorProduct.piRight Γ(S, ⊤) Γ(T, ⊤) Γ(T, ⊤)
    (fun y : Fin (k + 1) → ι ↦ sectionsModule f ℱ (⨅ l, U (y l)))).trans
    (LinearEquiv.piCongrRight fun y ↦ (LinearEquiv.ofBijective _
      (bijective_sectionsModuleBaseChange H ℱ hg (hU k y))).trans
      (sectionsModuleEqLinearEquiv (p := f') ((pullback g').obj ℱ)
        (g'.preimage_iInf (fun l : Fin (k + 1) ↦ U (y l))).symm))
  suffices h : ∀ x, cechModuleBaseChange H ℱ hg U k x = e x by
    have : ⇑(cechModuleBaseChange H ℱ hg U k) = ⇑e := funext h
    rw [this]
    exact e.bijective
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b c =>
    funext y
    rw [cechModuleBaseChange_tmul]
    simp only [e, LinearEquiv.trans_apply, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul, LinearEquiv.piCongrRight_apply,
      LinearEquiv.ofBijective_apply, sectionsModuleBaseChange_tmul]
    rfl

variable [IsAffine S] [IsAffine T] [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
  [Finite ι] (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))

/-- The base change of the Čech complex, indexed by `ℕ`. -/
noncomputable def cechModuleComplexNatBaseChangeIso :
    ((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤))).mapHomologicalComplex _).obj
      (cechModuleComplexNat f ℱ U) ≅
      cechModuleComplexNat f' ((pullback g').obj ℱ) (fun i ↦ g' ⁻¹ᵁ U i) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun degree ↦
      ((ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
        ((cechModuleComplexNat f ℱ U).X degree)).symm.trans
        (LinearEquiv.ofBijective _
          (bijective_cechModuleBaseChange H ℱ hg U hU degree))).toModuleIso)
    (by
      rintro degree _ rfl
      apply ModuleCat.ExtendScalars.hom_ext
      intro cochain
      rw [Functor.mapHomologicalComplex_obj_d]
      erw [cechModuleComplexNat_d f' ((pullback g').obj ℱ)
        (fun index ↦ g' ⁻¹ᵁ U index) degree, cechModuleComplexNat_d f ℱ U degree]
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
      change cechModuleD f' ((pullback g').obj ℱ) (fun index ↦ g' ⁻¹ᵁ U index) degree
          (cechModuleBaseChange H ℱ hg U degree
            ((ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
              (ModuleCat.of Γ(S, ⊤)
                (∀ simplex : Fin (degree + 1) → ι,
                  sectionsModule f ℱ (⨅ position, U (simplex position))))).symm
              (TensorProduct.tmul (Γ(S, ⊤))
                (M := (ModuleCat.restrictScalars
                  (algebraMap (Γ(S, ⊤)) (Γ(T, ⊤)))).obj
                    (ModuleCat.of (Γ(T, ⊤)) (Γ(T, ⊤))))
                (1 : Γ(T, ⊤)) cochain))) =
        cechModuleBaseChange H ℱ hg U (degree + 1)
          ((ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
            (ModuleCat.of Γ(S, ⊤)
              (∀ simplex : Fin (degree + 1 + 1) → ι,
                sectionsModule f ℱ (⨅ position, U (simplex position))))).symm
            (((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤))).map
              (ModuleCat.ofHom (cechModuleD f ℱ U degree)))
              (TensorProduct.tmul (Γ(S, ⊤))
                (M := (ModuleCat.restrictScalars
                  (algebraMap (Γ(S, ⊤)) (Γ(T, ⊤)))).obj
                    (ModuleCat.of (Γ(T, ⊤)) (Γ(T, ⊤))))
                (1 : Γ(T, ⊤)) cochain)))
      rw [ModuleCat.ExtendScalars.map_tmul]
      rw [← ModuleCat.tensorEquivExtendScalars_tmul,
        ← ModuleCat.tensorEquivExtendScalars_tmul]
      erw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      change cechModuleD f' ((pullback g').obj ℱ) (fun index ↦ g' ⁻¹ᵁ U index) degree
          (cechModuleBaseChange H ℱ hg U degree ((1 : Γ(T, ⊤)) ⊗ₜ cochain)) =
        cechModuleBaseChange H ℱ hg U (degree + 1)
          ((1 : Γ(T, ⊤)) ⊗ₜ cechModuleD f ℱ U degree cochain)
      exact (cechModuleBaseChange_d H ℱ hg U degree ((1 : Γ(T, ⊤)) ⊗ₜ cochain)).symm)

/-- **Base change of the Čech complex.** For a cartesian square with affine bases
`S = Spec A` and `T = Spec B`, a quasi-coherent `𝒪_X`-module `ℱ` and a finite family `U` of
opens of `X` whose finite intersections are affine, the Čech complex of `g'^* ℱ` for the family
`g'⁻¹ U` is the base change `B ⊗[A] Č(U, ℱ)` of the Čech complex of `ℱ`. -/
noncomputable def cechModuleComplexBaseChangeIso :
    ((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤))).mapHomologicalComplex _).obj
      (cechModuleComplex f ℱ U) ≅
      cechModuleComplex f' ((pullback g').obj ℱ) (fun i ↦ g' ⁻¹ᵁ U i) :=
  (cechModuleComplexNat f ℱ U).mapExtendIso ComplexShape.embeddingUpNat
    (ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤))) ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor _).mapIso
      (cechModuleComplexNatBaseChangeIso H ℱ hg U hU)

end Cech

end AlgebraicGeometry.Scheme.Modules
