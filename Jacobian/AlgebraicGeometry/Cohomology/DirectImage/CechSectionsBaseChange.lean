import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.SectionsBaseChange
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechResolution

/-!
# Sections of the Čech resolution of a base change

Consider a cartesian square of schemes
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` affine, a finite family `U` of opens of `X` and an open `W` of `T`, with
`B = Γ(T, W)`. The sections over `f'⁻¹ W` of the sheafified Čech complex `Č(g'⁻¹ U, g'^* ℱ)` are
the explicit Čech complex of the presheaf `V ↦ Γ(f'⁻¹ W, j_{V,*} (g'^* ℱ)|_V)`
(`AlgebraicGeometry.Scheme.Modules.sectionsCechResolutionIso`). We construct the base change
map `B ⊗[A] Č(U, ℱ) ⟶ Γ(f'⁻¹ W, Č(g'⁻¹ U, g'^* ℱ))`, `b ⊗ c ↦ (y ↦ b • (g'^* c_y)|)`,
as a morphism of complexes of abelian groups
(`AlgebraicGeometry.Scheme.Modules.cechSectionsBaseChange`), and show that it is bijective in
each degree when `W` is affine, `ℱ` is quasi-coherent and the finite intersections of the `U i`
are affine (`AlgebraicGeometry.Scheme.Modules.bijective_cechSectionsBaseChangeX`).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe u

open CategoryTheory Limits TensorProduct Opposite TopCat.Presheaf

namespace AlgebraicGeometry.Scheme.Modules

/-- The presheaf `V ↦ Γ(Z, j_{V,*} M|_V)` of abelian groups, whose Čech complex is the complex
of sections over `Z` of the sheafified Čech complex of `M`. -/
noncomputable abbrev cechSectionsPresheaf {Y : Scheme.{u}} (M : Y.Modules) (Z : Y.Opens) :
    Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  cechPresheaf M ⋙ SheafOfModules.evaluation Y.ringCatSheaf (op Z) ⋙ forget₂ _ AddCommGrpCat.{u}

lemma cechSectionsPresheaf_map_apply {Y : Scheme.{u}} (M : Y.Modules) (Z : Y.Opens)
    {V V' : Y.Opens} (h : V' ≤ V) (x : (cechSectionsPresheaf M Z).obj (op V)) :
    (cechSectionsPresheaf M Z).map (homOfLE h).op x =
      (M.presheaf.map (homOfLE (ι_image_preimage_mono h Z)).op :
        Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ Z) ⟶ Γ(M, V'.ι ''ᵁ V'.ι ⁻¹ᵁ Z)) x :=
  ConcreteCategory.congr_hom (cechPresheaf_map_app M (homOfLE h).op Z) x

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules) {ι : Type u} (U : ι → X.Opens) (W : T.Opens)
  [Algebra Γ(S, ⊤) Γ(T, W)]
  (hg : algebraMap Γ(S, ⊤) Γ(T, W) = (g.appLE ⊤ W (le_top.trans g.preimage_top.ge)).hom)

omit [Algebra Γ(S, ⊤) Γ(T, W)] in
lemma cech_image_preimage_le {k : ℕ} (y : Fin (k + 1) → ι) :
    (⨅ l, g' ⁻¹ᵁ U (y l)).ι ''ᵁ (⨅ l, g' ⁻¹ᵁ U (y l)).ι ⁻¹ᵁ (f' ⁻¹ᵁ W) ≤
      g' ⁻¹ᵁ (⨅ l, U (y l)) ⊓ f' ⁻¹ᵁ W := by
  rw [ι_image_preimage, Scheme.Hom.preimage_iInf]

/-- The base change of Čech cochains `B ⊗[A] Č^k(U, ℱ) ⟶ Γ(f'⁻¹ W, Č^k(g'⁻¹ U, g'^* ℱ))`,
`b ⊗ c ↦ (y ↦ b • (g'^* c_y)|)`, in explicit cochains. -/
noncomputable def cechSectionsBaseChangeX (k : ℕ) :
    Γ(T, W) ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) →+
      CechCochain (fun i ↦ g' ⁻¹ᵁ U i) (cechSectionsPresheaf ((pullback g').obj ℱ) (f' ⁻¹ᵁ W))
        k :=
  AddMonoidHom.pi fun y ↦ (sectionsBaseChangeOpen H ℱ W hg (cech_image_preimage_le U W y)).comp
    ((LinearMap.proj (R := Γ(S, ⊤)) y).baseChange Γ(T, W)).toAddMonoidHom

lemma cechSectionsBaseChangeX_tmul (k : ℕ) (b : Γ(T, W))
    (c : ∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) (y : Fin (k + 1) → ι) :
    cechSectionsBaseChangeX H ℱ U W hg k (b ⊗ₜ c) y =
      sectionsBaseChangeOpen H ℱ W hg (cech_image_preimage_le U W y) (b ⊗ₜ c y) :=
  rfl

/-- **The base change of Čech cochains commutes with the differentials.** -/
lemma cechSectionsBaseChangeX_d (k : ℕ)
    (x : Γ(T, W) ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l)))) :
    cechSectionsBaseChangeX H ℱ U W hg (k + 1) ((cechModuleD f ℱ U k).baseChange Γ(T, W) x) =
      ((cechComplex (fun i ↦ g' ⁻¹ᵁ U i)).obj
        (cechSectionsPresheaf ((pullback g').obj ℱ) (f' ⁻¹ᵁ W))).d k (k + 1)
        (cechSectionsBaseChangeX H ℱ U W hg k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b c =>
    funext y
    rw [LinearMap.baseChange_tmul, cechSectionsBaseChangeX_tmul, cechComplex_d_apply,
      cechModuleD_apply_apply, TensorProduct.tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [TensorProduct.tmul_smul, map_zsmul, cechSectionsPresheaf_map_apply,
      cechSectionsBaseChangeX_tmul]
    congr 1
    rw [presheaf_map_sectionsBaseChangeOpen H ℱ W hg (iInf_le_iInf_comp U y i.succAbove),
      LinearMap.baseChange_tmul]

/-- **The base change map of Čech complexes on sections over `f'⁻¹ W`**:
`B ⊗[A] Č(U, ℱ) ⟶ Γ(f'⁻¹ W, Č(g'⁻¹ U, g'^* ℱ))` as a morphism of complexes of abelian groups,
the target in explicit cochains. -/
noncomputable def cechSectionsBaseChange :
    ((forget₂ (ModuleCat.{u} Γ(T, W)) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
      (((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, W))).mapHomologicalComplex _).obj
        (cechModuleComplexNat f ℱ U)) ⟶
      (cechComplex (fun i ↦ g' ⁻¹ᵁ U i)).obj
        (cechSectionsPresheaf ((pullback g').obj ℱ) (f' ⁻¹ᵁ W)) where
  f degree := AddCommGrpCat.ofHom ((cechSectionsBaseChangeX H ℱ U W hg degree).comp
    (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, W)
      ((cechModuleComplexNat f ℱ U).X degree)).symm.toAddEquiv.toAddMonoidHom)
  comm' := by
    rintro degree _ rfl
    ext element
    change ((cechComplex (fun i ↦ g' ⁻¹ᵁ U i)).obj
        (cechSectionsPresheaf ((pullback g').obj ℱ) (f' ⁻¹ᵁ W))).d degree (degree + 1)
          (cechSectionsBaseChangeX H ℱ U W hg degree
            ((ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, W)
              ((cechModuleComplexNat f ℱ U).X degree)).symm element)) =
      cechSectionsBaseChangeX H ℱ U W hg (degree + 1)
        ((ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, W)
          ((cechModuleComplexNat f ℱ U).X (degree + 1))).symm
            ((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, W))).map
              ((cechModuleComplexNat f ℱ U).d degree (degree + 1)) element))
    rw [ModuleCat.tensorEquivExtendScalars_symm_naturality]
    erw [cechModuleComplexNat_d]
    exact (cechSectionsBaseChangeX_d H ℱ U W hg degree _).symm

lemma cechSectionsBaseChange_f_apply (degree : ℕ) (element) :
    (cechSectionsBaseChange H ℱ U W hg).f degree element =
      cechSectionsBaseChangeX H ℱ U W hg degree
        ((ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, W)
          ((cechModuleComplexNat f ℱ U).X degree)).symm element) :=
  rfl

omit [Algebra Γ(S, ⊤) Γ(T, W)] in
lemma cech_image_preimage_eq {k : ℕ} (y : Fin (k + 1) → ι) :
    (⨅ l, g' ⁻¹ᵁ U (y l)).ι ''ᵁ (⨅ l, g' ⁻¹ᵁ U (y l)).ι ⁻¹ᵁ (f' ⁻¹ᵁ W) =
      g' ⁻¹ᵁ (⨅ l, U (y l)) ⊓ f' ⁻¹ᵁ W := by
  rw [ι_image_preimage, Scheme.Hom.preimage_iInf]

/-- **The base change map of Čech complexes is bijective** over an affine open `W` of `T`, for
`S` affine, `ℱ` quasi-coherent and a finite family `U` whose finite intersections are affine. -/
theorem bijective_cechSectionsBaseChangeX [IsAffine S]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] [Finite ι] (hW : IsAffineOpen W)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l))) (k : ℕ) :
    Function.Bijective (cechSectionsBaseChangeX H ℱ U W hg k) := by
  classical
  have := Fintype.ofFinite ι
  have hy (y : Fin (k + 1) → ι) :
      Function.Bijective (sectionsBaseChangeOpen H ℱ W hg (cech_image_preimage_le U W y)) := by
    have h := presheaf_map_sectionsBaseChangeOpen H ℱ W hg (le_refl (⨅ l, U (y l)))
      (le_refl _) (cech_image_preimage_le U W y) (cech_image_preimage_le U W y)
    have hid : (sectionsModuleRestrict f ℱ (le_refl (⨅ l, U (y l)))).baseChange Γ(T, W) =
        LinearMap.id := by
      rw [show sectionsModuleRestrict f ℱ (le_refl (⨅ l, U (y l))) = LinearMap.id from
        LinearMap.ext fun m ↦ sectionsModuleRestrict_self f ℱ _ m, LinearMap.baseChange_id]
    have : ⇑(sectionsBaseChangeOpen H ℱ W hg (cech_image_preimage_le U W y)) =
        ((pullback g').obj ℱ).presheaf.map (homOfLE (cech_image_preimage_le U W y)).op ∘
          sectionsBaseChangeOpen H ℱ W hg (le_refl _) := by
      funext x
      rw [Function.comp_apply, h, hid, LinearMap.id_apply]
    rw [this]
    have := isIso_presheaf_map_of_le ((pullback g').obj ℱ)
      (homOfLE (cech_image_preimage_le (f' := f') (g' := g') U W y))
      (cech_image_preimage_eq (f' := f') (g' := g') U W y).ge
    exact (ConcreteCategory.bijective_of_isIso _).comp
      (bijective_sectionsBaseChangeOpen H ℱ W hg hW (hU k y))
  let e := (TensorProduct.piRight Γ(S, ⊤) Γ(T, W) Γ(T, W)
    (fun y : Fin (k + 1) → ι ↦ sectionsModule f ℱ (⨅ l, U (y l)))).toAddEquiv.trans
    (AddEquiv.piCongrRight fun y ↦ AddEquiv.ofBijective _ (hy y))
  suffices h : ∀ x, cechSectionsBaseChangeX H ℱ U W hg k x = e x by
    have : ⇑(cechSectionsBaseChangeX H ℱ U W hg k) = ⇑e := funext h
    rw [this]
    exact e.bijective
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b c =>
    funext y
    rw [cechSectionsBaseChangeX_tmul]
    rfl

/-! ### Linearity and restriction of the base change map -/

section Linear

/-- **The base change map of Čech cochains is semilinear**, once identified with the sections of
the Čech resolution: `b • w ↦ f'^♯ b • (…)`. -/
lemma sectionsCechResolutionIso_inv_cechSectionsBaseChangeX_smul (k : ℕ) (b : Γ(T, W))
    (w : Γ(T, W) ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l)))) :
    (sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ) (f' ⁻¹ᵁ W)).inv.f k
        (cechSectionsBaseChangeX H ℱ U W hg k (b • w)) =
      (show Γ((cechResolution (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)).X k, f' ⁻¹ᵁ W) from
        f'.app W b •
          (show Γ((cechResolution (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)).X k, f' ⁻¹ᵁ W)
            from (sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)
              (f' ⁻¹ᵁ W)).inv.f k (cechSectionsBaseChangeX H ℱ U W hg k w))) := by
  set iso := sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ) (f' ⁻¹ᵁ W)
  set s : Γ((cechResolution (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)).X k, f' ⁻¹ᵁ W) :=
    iso.inv.f k (cechSectionsBaseChangeX H ℱ U W hg k w)
  have hs : iso.hom.f k s = cechSectionsBaseChangeX H ℱ U W hg k w :=
    sectionsCechResolutionIso_hom_inv_f_apply _ _ _ _ _
  have key : cechSectionsBaseChangeX H ℱ U W hg k (b • w) = iso.hom.f k (f'.app W b • s) := by
    funext y
    rw [sectionsCechResolutionIso_hom_f_smul, hs]
    change sectionsBaseChangeOpen H ℱ W hg (cech_image_preimage_le U W y)
      (((LinearMap.proj (R := Γ(S, ⊤)) y).baseChange Γ(T, W)) (b • w)) = _
    rw [LinearMap.map_smul, sectionsBaseChangeOpen_smul]
    exact (extendRestrict_smul _ _ _ _ _).symm
  rw [key]
  exact sectionsCechResolutionIso_inv_hom_f_apply _ _ _ _ _

/-- **The base change map of Čech cochains is compatible with restriction** from `W'` to
`W ≤ W'`, on the cochains `1 ⊗ m`. -/
lemma presheaf_map_sectionsCechResolutionIso_inv_one_tmul {W' : T.Opens} (hW : W ≤ W')
    [Algebra Γ(S, ⊤) Γ(T, W')]
    (hg' : algebraMap Γ(S, ⊤) Γ(T, W') = (g.appLE ⊤ W' (le_top.trans g.preimage_top.ge)).hom)
    (k : ℕ) (m : ∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) :
    ((cechResolution (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)).X k).presheaf.map
        (homOfLE (f'.preimage_mono hW)).op
        ((sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)
          (f' ⁻¹ᵁ W')).inv.f k (cechSectionsBaseChangeX H ℱ U W' hg' k (1 ⊗ₜ m))) =
      (sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)
          (f' ⁻¹ᵁ W)).inv.f k (cechSectionsBaseChangeX H ℱ U W hg k (1 ⊗ₜ m)) := by
  set iso' := sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ) (f' ⁻¹ᵁ W')
  set s' : Γ((cechResolution (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)).X k, f' ⁻¹ᵁ W') :=
    iso'.inv.f k (cechSectionsBaseChangeX H ℱ U W' hg' k (1 ⊗ₜ m))
  have hs' : iso'.hom.f k s' = cechSectionsBaseChangeX H ℱ U W' hg' k (1 ⊗ₜ m) :=
    sectionsCechResolutionIso_hom_inv_f_apply _ _ _ _ _
  set iso := sectionsCechResolutionIso (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ) (f' ⁻¹ᵁ W)
  have key : iso.hom.f k
      (((cechResolution (fun i ↦ g' ⁻¹ᵁ U i) ((pullback g').obj ℱ)).X k).presheaf.map
        (homOfLE (f'.preimage_mono hW)).op s') =
      cechSectionsBaseChangeX H ℱ U W hg k (1 ⊗ₜ m) := by
    funext y
    rw [sectionsCechResolutionIso_hom_f_presheaf_map, hs', cechSectionsBaseChangeX_tmul,
      cechSectionsBaseChangeX_tmul]
    erw [sectionsBaseChangeOpen_tmul, sectionsBaseChangeOpen_tmul]
    simp only [map_one, one_smul]
    erw [cechPresheaf_obj_presheaf_map_apply]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [← key]
  exact (sectionsCechResolutionIso_inv_hom_f_apply _ _ _ _ _).symm

end Linear

end AlgebraicGeometry.Scheme.Modules
