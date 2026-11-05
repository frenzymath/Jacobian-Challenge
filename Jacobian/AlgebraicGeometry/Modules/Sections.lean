import Jacobian.AlgebraicGeometry.Modules.Endomorphism
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Sections and linear maps of module sheaves

Sections on opens form modules over global functions. Morphisms and isomorphisms
induce linear maps and equivalences, and vanishing is detected on affine opens.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}}
/-- The structure sheaf, regarded as a sheaf of modules over itself. -/
noncomputable abbrev unit (scheme : Scheme.{u}) : scheme.Modules :=
  SheafOfModules.unit scheme.ringCatSheaf
variable {M N : X.Modules}

/-- Evaluating a finite sum of module-sheaf morphisms gives the sum of evaluations. -/
lemma Hom.sum_app_apply {M N : X.Modules} {indices : Type*} (summands : Finset indices)
    (morphisms : indices → (M ⟶ N)) (openSubset : X.Opens) (sectionValue : Γ(M, openSubset)) :
    (∑ index ∈ summands, morphisms index).app openSubset sectionValue =
      ∑ index ∈ summands, (morphisms index).app openSubset sectionValue := by
  classical
  induction summands using Finset.induction_on with
  | empty => simp
  | insert index summands notMem inductionHypothesis =>
    simp [Finset.sum_insert notMem, inductionHypothesis]

/-- The presheaf of `Γ(X, ⊤)`-modules underlying a sheaf of modules `ℱ`: its value on an open
`U` is `Γ(U, ℱ)`, a `Γ(X, ⊤)`-module by restriction of scalars along `Γ(X, ⊤) ⟶ Γ(X, U)`.
It is the image of `ℱ` under `PresheafOfModules.forgetToPresheafModuleCat`. -/
noncomputable def presheafModuleCat (ℱ : X.Modules) : X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).obj ℱ.val

@[simp]
lemma presheafModuleCat_obj (ℱ : X.Modules) (V : X.Opensᵒᵖ) :
    ℱ.presheafModuleCat.obj V = (ModuleCat.restrictScalars
      (X.ringCatSheaf.obj.map (homOfLE le_top : V.unop ⟶ ⊤).op).hom).obj (ℱ.val.obj V) :=
  rfl

lemma presheafModuleCat_obj_coe (ℱ : X.Modules) (V : X.Opensᵒᵖ) :
    (ℱ.presheafModuleCat.obj V : Type u) = ℱ.val.obj V :=
  rfl

/-- **A sheaf of modules vanishing on affine opens is zero.** If `Γ(M, V) = 0` for every affine
open `V`, then `M = 0`: the affine opens form a basis, so every section is locally zero. -/
lemma isZero_of_forall_affineOpens (M : X.Modules)
    (h : ∀ V : X.affineOpens, Subsingleton Γ(M, V.1)) : IsZero M := by
  refine (IsZero.iff_id_eq_zero M).2 (hom_ext _ _ fun U ↦ ?_)
  ext x
  change x = 0
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
    (fun i : {V : X.affineOpens // V.1 ≤ U} ↦ i.1.1) U (fun i ↦ homOfLE i.2) ?_ x 0
    fun i ↦ @Subsingleton.elim _ (h i.1) _ _
  intro y hy
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hy U.2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩

/-- Every sheaf of modules on an empty scheme is zero. -/
lemma isZero_of_isEmpty [IsEmpty X] (M : X.Modules) : IsZero M := by
  refine (IsZero.iff_id_eq_zero M).2 (hom_ext _ _ fun U ↦ ?_)
  ext x
  change x = 0
  exact TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ (fun i : Empty ↦ i.elim) U
    (fun i ↦ i.elim) (fun y _ ↦ isEmptyElim y) x 0 (fun i ↦ i.elim)

/-- The application `Γ(M, U) → Γ(N, U)` of a morphism of `𝒪_X`-modules, as a `Γ(X, U)`-linear
map. -/
noncomputable def Hom.appₗ {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun := φ.app U
  map_add' := map_add _
  map_smul' := Hom.app_smul φ

@[simp]
lemma Hom.appₗ_apply {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) (x : Γ(M, U)) :
    Hom.appₗ φ U x = φ.app U x :=
  rfl

/-- The `Γ(X, U)`-linear isomorphism `Γ(M, U) ≃ Γ(N, U)` induced by an isomorphism `M ≅ N` of
`𝒪_X`-modules. -/
noncomputable def appLinearEquivOfIso {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(N, U) where
  __ := Hom.appₗ e.hom U
  invFun := e.inv.app U
  left_inv x := by
    change Hom.app (e.hom ≫ e.inv) U x = x
    rw [e.hom_inv_id]
    rfl
  right_inv x := by
    change Hom.app (e.inv ≫ e.hom) U x = x
    rw [e.inv_hom_id]
    rfl

/-- Restricting a section of `M` twice is restricting it along the composite. -/
lemma presheaf_map_map_apply {U V W : X.Opens} (f : V ⟶ U) (g : W ⟶ V) (e : Γ(M, U)) :
    M.presheaf.map g.op (M.presheaf.map f.op e) = M.presheaf.map (g ≫ f).op e := by
  rw [op_comp, Functor.map_comp]
  rfl

/-- Restricting a section of `M` along an endomorphism of an open does nothing. -/
lemma presheaf_map_id_apply {U : X.Opens} (f : U ⟶ U) (e : Γ(M, U)) :
    M.presheaf.map f.op e = e := by
  rw [Subsingleton.elim f (𝟙 U), op_id, CategoryTheory.Functor.map_id]
  rfl


end AlgebraicGeometry.Scheme.Modules
