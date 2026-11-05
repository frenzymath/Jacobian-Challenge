import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechCohomology
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechBaseChange
import Jacobian.Algebra.Homology.CochainComplex.FlatTruncation

/-!
# Bounded flat Cech models over affine bases

For a quasi-coherent module flat over an affine base, a finite affine cover gives
a bounded complex of flat modules computing its higher direct images. Its
inclusion into the full Cech complex stays a quasi-isomorphism under arbitrary
extension of scalars. Flatness of the cycles follows from exactness modulo every
ideal and propagates down the exact tail.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens)

/-- Finite nonempty intersections of affine opens are affine over a separated affine base. -/
lemma isAffineOpen_iInf_of_isSeparated [IsAffine S] [IsSeparated f]
    (hU : ∀ index, IsAffineOpen (U index)) (degree : ℕ) (simplex : Fin (degree + 1) → ι) :
    IsAffineOpen (⨅ position, U (simplex position)) := by
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  exact IsAffineOpen.iInf fun position ↦ hU (simplex position)

variable [IsAffine S] [IsSeparated f] [Fintype ι] [Nonempty ι] (hU : ∀ i, IsAffineOpen (U i))
  (hU' : iSup U = ⊤) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

include hU hU' in
/-- **The Čech complex is exact in high degrees after any affine base change.** For a cartesian
square with `T = Spec B` affine, `B ⊗[A] Č(U, ℱ) ≅ Č(g'⁻¹ U, g'^* ℱ)` is exact in degrees
`≥ #ι`. -/
lemma exactAt_extendScalars_cechModuleComplex {T Y : Scheme.{u}} {g : T ⟶ S} {g' : Y ⟶ X}
    {f' : Y ⟶ T} (H : IsPullback g' f' f g) [IsAffine T] [Algebra Γ(S, ⊤) Γ(T, ⊤)]
    (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom) (k : ℤ) (hk : Fintype.card ι ≤ k) :
    (((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤))).mapHomologicalComplex _).obj
      (cechModuleComplex f ℱ U)).ExactAt k := by
  have : IsSeparated f' := MorphismProperty.of_isPullback H ‹IsSeparated f›
  have : IsAffineHom g' := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  refine HomologicalComplex.ExactAt.of_iso ?_
    (cechModuleComplexBaseChangeIso H ℱ hg U (isAffineOpen_iInf_of_isSeparated f U hU)).symm
  refine exactAt_cechModuleComplex f' _ _
    (fun i ↦ (hU i).preimage g') ?_ k (Or.inr hk)
  rw [← Scheme.Hom.preimage_iSup, hU', Scheme.Hom.preimage_top]

include hU hU' in
/-- **The Čech complex is exact in high degrees modulo any ideal.** For an ideal `I` of
`A = Γ(S, ⊤)`, the complex `A/I ⊗[A] Č(U, ℱ)` is exact in degrees `≥ #ι`: it is the Čech complex
of the restriction of `ℱ` to the closed subscheme `X ×_S Spec (A/I)`. -/
lemma exact_lTensor_quotient_cechModuleComplex (I : Ideal Γ(S, ⊤)) (k : ℤ)
    (hk : Fintype.card ι ≤ k + 1) :
    Function.Exact (((cechModuleComplex f ℱ U).d k (k + 1)).hom.lTensor (Γ(S, ⊤) ⧸ I))
      (((cechModuleComplex f ℱ U).d (k + 1) (k + 1 + 1)).hom.lTensor (Γ(S, ⊤) ⧸ I)) := by
  let φ : Γ(S, ⊤) ⟶ CommRingCat.of (Γ(S, ⊤) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let g : Spec (CommRingCat.of (Γ(S, ⊤) ⧸ I)) ⟶ S := Spec.map φ ≫ S.isoSpec.inv
  let : Algebra Γ(S, ⊤) Γ(Spec (CommRingCat.of (Γ(S, ⊤) ⧸ I)), ⊤) := g.appTop.hom.toAlgebra
  have h := exactAt_extendScalars_cechModuleComplex f ℱ U hU hU' (IsPullback.of_hasPullback f g)
    rfl (k + 1) hk
  rw [CochainComplex.exactAt_extendScalars_iff] at h
  have e : (Γ(S, ⊤) ⧸ I) ≃ₗ[Γ(S, ⊤)] Γ(Spec (CommRingCat.of (Γ(S, ⊤) ⧸ I)), ⊤) := by
    have h₁ : S.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(S, ⊤)).hom = 𝟙 _ := by
      rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv]
      rfl
    have h₂ : (Spec.map φ).appTop =
        (Scheme.ΓSpecIso Γ(S, ⊤)).hom ≫ φ ≫ (Scheme.ΓSpecIso _).inv := by
      rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
    have hg (a : Γ(S, ⊤)) : g.appTop a = (Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk I a) := by
      change (S.isoSpec.inv.appTop ≫ (Spec.map φ).appTop) a = _
      rw [h₂, ← Category.assoc, ← Category.assoc, h₁, Category.id_comp]
      rfl
    exact { (Scheme.ΓSpecIso (CommRingCat.of (Γ(S, ⊤) ⧸ I))).commRingCatIsoToRingEquiv.symm with
      map_smul' a x := by
        change (Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk I a * x) =
          g.appTop a * (Scheme.ΓSpecIso _).inv x
        rw [map_mul, hg] }
  exact (Function.Exact.iff_of_ladder_linearEquiv (e₁ := e.rTensor _) (e₂ := e.rTensor _)
    (e₃ := e.rTensor _) (by ext; simp) (by ext; simp)).1 h

include hU hU' in
/-- **Flatness of the Čech cycles in high degrees.** If `ℱ` is flat over `S`, the modules of
cycles of the Čech complex `Č(U, ℱ)` are flat in degrees `≥ #ι - 1`. In high degrees this
follows from the exactness of `A/I ⊗[A] Č(U, ℱ)` for every ideal `I`
(`AlgebraicGeometry.Scheme.Modules.exact_lTensor_quotient_cechModuleComplex`), and it propagates
down to degree `#ι - 1` along the exact part of the complex. -/
theorem flat_ker_d_cechModuleComplex (hℱ : ℱ.IsFlatOver f) (k : ℤ)
    (hk : (Fintype.card ι : ℤ) - 1 ≤ k) :
    Module.Flat Γ(S, ⊤) (LinearMap.ker ((cechModuleComplex f ℱ U).d k (k + 1)).hom) := by
  have hC := flat_cechModuleComplex_X f ℱ U hℱ (isAffineOpen_iInf_of_isSeparated f U hU)
  have hex (j : ℤ) (hj : (Fintype.card ι : ℤ) ≤ j) : (cechModuleComplex f ℱ U).ExactAt j :=
    exactAt_cechModuleComplex f ℱ U hU hU' j (Or.inr hj)
  exact CochainComplex.flat_ker_d_of_exactAt hC hex
    (CochainComplex.flat_ker_d_of_exact_lTensor_quotient hC hex fun I j hj ↦
      exact_lTensor_quotient_cechModuleComplex f ℱ U hU hU' I j hj) k hk

include hU hU' in
/-- The truncation of the Čech complex of a module flat over the base is a complex of flat
modules. -/
lemma flat_cechModuleComplexTrunc_X (hℱ : ℱ.IsFlatOver f) (i : ℤ) :
    Module.Flat Γ(S, ⊤) ((cechModuleComplexTrunc f ℱ U).X i) :=
  CochainComplex.flat_truncLE_X _ _
    (flat_cechModuleComplex_X f ℱ U hℱ (isAffineOpen_iInf_of_isSeparated f U hU))
    (flat_ker_d_cechModuleComplex f ℱ U hU hU' hℱ _ le_rfl) i

include hU hU' in
/-- **Base change of the truncated Čech complex.** If `ℱ` is flat over `S`, the inclusion of the
truncation `τ^{≤ #ι - 1} Č(U, ℱ) ⟶ Č(U, ℱ)` stays a quasi-isomorphism after any base change
`A ⟶ B`. -/
theorem quasiIso_extendScalars_ιTruncLE_cechModuleComplex (hℱ : ℱ.IsFlatOver f)
    (B : Type u) [CommRing B] [Algebra Γ(S, ⊤) B] :
    QuasiIso (((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) B)).mapHomologicalComplex _).map
      ((cechModuleComplex f ℱ U).ιTruncLE ((Fintype.card ι : ℤ) - 1))) :=
  CochainComplex.quasiIso_extendScalars_ιTruncLE B _ _
    (flat_cechModuleComplex_X f ℱ U hℱ (isAffineOpen_iInf_of_isSeparated f U hU))
    (fun k hk ↦ exactAt_cechModuleComplex f ℱ U hU hU' k (Or.inr (by omega)))
    (flat_ker_d_cechModuleComplex f ℱ U hU hU' hℱ)


end AlgebraicGeometry.Scheme.Modules
