import Jacobian.AlgebraicGeometry.Modules.BaseChange
import Jacobian.AlgebraicGeometry.Modules.Flat
import Jacobian.Topology.Sheaves.Cech
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Čech complexes over an affine base

For a morphism `f : X ⟶ S`, this file records the explicit module-valued Čech complex
of a module sheaf on a family of opens of `X`.  The scalar action is induced by
`f.appTop`, so the construction can be compared directly with affine base change.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
variable {ι : Type u} (U : ι → X.Opens)

open TopCat.Presheaf

/-- Restriction of sections as a module map over the base. -/
noncomputable def sectionsModuleRestrict {V W : X.Opens} (h : V ≤ W) :
    sectionsModule f ℱ W →ₗ[Γ(S, ⊤)] sectionsModule f ℱ V :=
  ((ModuleCat.restrictScalars f.appTop.hom).map
    (ℱ.presheafModuleCat.map (homOfLE h).op)).hom

lemma sectionsModuleRestrict_apply {V W : X.Opens} (h : V ≤ W)
    (m : sectionsModule f ℱ W) :
    sectionsModuleRestrict f ℱ h m = ℱ.presheaf.map (homOfLE h).op m :=
  rfl

lemma sectionsModuleRestrict_comp {V W Z : X.Opens} (h₁ : V ≤ W) (h₂ : W ≤ Z)
    (m : sectionsModule f ℱ Z) :
    sectionsModuleRestrict f ℱ h₁ (sectionsModuleRestrict f ℱ h₂ m) =
      sectionsModuleRestrict f ℱ (h₁.trans h₂) m :=
  TopCat.Presheaf.map_homOfLE_map_homOfLE_apply ℱ.presheaf h₁ h₂ m

lemma sectionsModuleRestrict_self {W : X.Opens} (h : W ≤ W)
    (m : sectionsModule f ℱ W) :
    sectionsModuleRestrict f ℱ h m = m :=
  TopCat.Presheaf.map_homOfLE_self_apply ℱ.presheaf h m

/-- The alternating differential on Čech cochains with coefficients in `ℱ`. -/
noncomputable def cechModuleD (k : ℕ) :
    (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) →ₗ[Γ(S, ⊤)]
      (∀ y : Fin (k + 1 + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) :=
  ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • LinearMap.pi fun y ↦
    sectionsModuleRestrict f ℱ (iInf_le_iInf_comp U y i.succAbove) ∘ₗ
      LinearMap.proj (y ∘ i.succAbove)

lemma cechModuleD_apply_apply (k : ℕ)
    (c : ∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l)))
    (y : Fin (k + 1 + 1) → ι) :
    cechModuleD f ℱ U k c y = ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) •
      sectionsModuleRestrict f ℱ (iInf_le_iInf_comp U y i.succAbove) (c (y ∘ i.succAbove)) := by
  simp only [cechModuleD, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply]
  rfl

lemma cechModuleD_apply (k : ℕ)
    (c : ∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) :
    cechModuleD f ℱ U k c = ((cechComplex U).obj ℱ.presheaf).d k (k + 1) c := by
  funext y
  rw [cechComplex_d_apply]
  simp only [cechModuleD, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    Function.comp_apply]
  rfl

/-- The nonnegative Čech complex with its scalar action from the base. -/
noncomputable def cechModuleComplexNat : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ :=
  CochainComplex.of
    (fun k ↦ ModuleCat.of Γ(S, ⊤)
      (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))))
    (fun k ↦ ModuleCat.ofHom (cechModuleD f ℱ U k))
    (fun k ↦ by
      ext c : 2
      change cechModuleD f ℱ U (k + 1) (cechModuleD f ℱ U k c) = 0
      rw [cechModuleD_apply, cechModuleD_apply]
      exact congr($(((cechComplex U).obj ℱ.presheaf).d_comp_d k (k + 1) (k + 1 + 1)) c))

lemma cechModuleComplexNat_d (k : ℕ) :
    (cechModuleComplexNat f ℱ U).d k (k + 1) = ModuleCat.ofHom (cechModuleD f ℱ U k) := by
  simp only [cechModuleComplexNat, CochainComplex.of_d]

/-- The integer-indexed Čech complex, concentrated in nonnegative degrees. -/
noncomputable def cechModuleComplex : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ :=
  (cechModuleComplexNat f ℱ U).extend ComplexShape.embeddingUpNat

instance : (cechModuleComplex f ℱ U).IsStrictlyGE 0 := by
  dsimp [cechModuleComplex]
  infer_instance

/-- Relatively flat coefficients have flat sections on affine opens over an affine base. -/
lemma flat_sectionsModule [IsAffine S] (hℱ : ℱ.IsFlatOver f) {W : X.Opens}
    (hW : IsAffineOpen W) : Module.Flat Γ(S, ⊤) (sectionsModule f ℱ W) :=
  hℱ ⟨⊤, isAffineOpen_top S⟩ ⟨W, hW⟩ (by simp)

/-- A finite affine-intersection Čech complex of relatively flat coefficients has flat terms. -/
theorem flat_cechModuleComplex_X [IsAffine S] (hℱ : ℱ.IsFlatOver f) [Finite ι]
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l))) (n : ℤ) :
    Module.Flat Γ(S, ⊤) ((cechModuleComplex f ℱ U).X n) := by
  by_cases hn : ∃ k : ℕ, (k : ℤ) = n
  · obtain ⟨k, rfl⟩ := hn
    have := Fintype.ofFinite ι
    have (y : Fin (k + 1) → ι) := flat_sectionsModule f ℱ hℱ (hU k y)
    have : Module.Flat Γ(S, ⊤)
        (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) :=
      Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := Γ(S, ⊤))).symm
    have : Module.Flat Γ(S, ⊤) ((cechModuleComplexNat f ℱ U).X k) := this
    exact Module.Flat.of_linearEquiv
      ((cechModuleComplexNat f ℱ U).extendXIso ComplexShape.embeddingUpNat rfl).toLinearEquiv
  · have hz := (cechModuleComplexNat f ℱ U).isZero_extend_X ComplexShape.embeddingUpNat n
      fun k hk ↦ hn ⟨k, hk⟩
    have : Subsingleton ((cechModuleComplex f ℱ U).X n) :=
      ModuleCat.subsingleton_of_isZero hz
    infer_instance

end AlgebraicGeometry.Scheme.Modules
