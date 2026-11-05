import Jacobian.Algebra.Homology.CochainComplex.Resolution
import Jacobian.Algebra.Category.ModuleCat.Sheaf.Evaluation
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Affine
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Composition
import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechFlat
import Jacobian.AlgebraicGeometry.Cohomology.Flasque
import Jacobian.AlgebraicGeometry.Modules.Exactness
import Jacobian.CategoryTheory.Sites.CechComplex
import Jacobian.Topology.Sheaves.CechComparison
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Cech resolutions of sheaves of modules

For an open cover, the augmented Cech complex of the sheaves
`j_* (ℱ|_U)` resolves `ℱ`. Affine intersections make its terms acyclic for
pushforward along a separated morphism, so it computes higher direct images.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits Opposite ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section ExtendRestrict

lemma ι_image_preimage (V T : X.Opens) : V.ι ''ᵁ V.ι ⁻¹ᵁ T = V ⊓ T := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

lemma ι_image_preimage_mono {V W : X.Opens} (h : W ≤ V) (T : X.Opens) :
    W.ι ''ᵁ W.ι ⁻¹ᵁ T ≤ V.ι ''ᵁ V.ι ⁻¹ᵁ T := by
  rw [ι_image_preimage, ι_image_preimage]
  exact inf_le_inf_right T h

/-- The functor `ℱ ↦ j_* (ℱ|_V)` for the inclusion `j : V ⟶ X` of an open `V`. -/
noncomputable abbrev extendRestrictFunctor (V : X.Opens) : X.Modules ⥤ X.Modules :=
  restrictFunctor V.ι ⋙ pushforward V.ι

/-- The restriction `j_{V,*} (ℱ|_V) ⟶ j_{W,*} (ℱ|_W)` for opens `W ≤ V`. -/
noncomputable def extendRestrictMap {V W : X.Opens} (h : W ≤ V) :
    extendRestrictFunctor V ⟶ extendRestrictFunctor W :=
  let a : restrictFunctor V.ι ⋙ pushforward V.ι ⟶
      (restrictFunctor V.ι ⋙ restrictFunctor (X.homOfLE h)) ⋙
        (pushforward (X.homOfLE h) ⋙ pushforward V.ι) :=
    Functor.whiskerLeft (restrictFunctor V.ι)
      (Functor.whiskerRight (restrictAdjunction (X.homOfLE h)).unit (pushforward V.ι))
  let b : (restrictFunctor V.ι ⋙ restrictFunctor (X.homOfLE h)) ⋙
      (pushforward (X.homOfLE h) ⋙ pushforward V.ι) ⟶
        restrictFunctor (X.homOfLE h ≫ V.ι) ⋙ pushforward (X.homOfLE h ≫ V.ι) :=
    (restrictFunctorComp (X.homOfLE h) V.ι).inv ◫ (pushforwardComp (X.homOfLE h) V.ι).hom
  let c : restrictFunctor (X.homOfLE h ≫ V.ι) ⋙ pushforward (X.homOfLE h ≫ V.ι) ⟶
      restrictFunctor W.ι ⋙ pushforward W.ι :=
    (restrictFunctorCongr (X.homOfLE_ι h)).hom ◫ (pushforwardCongr (X.homOfLE_ι h)).hom
  a ≫ b ≫ c

lemma extendRestrictMap_app_app {V W : X.Opens} (h : W ≤ V) (ℱ : X.Modules) (T : X.Opens) :
    ((extendRestrictMap h).app ℱ).app T =
      (ℱ.presheaf.map (homOfLE (ι_image_preimage_mono h T)).op :
        Γ(ℱ, V.ι ''ᵁ V.ι ⁻¹ᵁ T) ⟶ Γ(ℱ, W.ι ''ᵁ W.ι ⁻¹ᵁ T)) := by
  simp only [extendRestrictMap, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.hcomp_app, Hom.comp_app, pushforward_map_app,
    restrictAdjunction_unit_app_app, pushforwardComp_hom_app_app, restrictFunctorComp_inv_app_app,
    pushforwardCongr_hom_app_app, restrictFunctorCongr_hom_app_app, restrict_map,
    ← Functor.map_comp]
  erw [Category.id_comp]
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

end ExtendRestrict

section Complex

variable (X) in
/-- The presheaf of functors `V ↦ (ℱ ↦ j_{V,*} (ℱ|_V))` on the opens of `X`. -/
noncomputable def extendRestrictPresheaf : X.Opensᵒᵖ ⥤ X.Modules ⥤ X.Modules where
  obj V := extendRestrictFunctor V.unop
  map i := extendRestrictMap (leOfHom i.unop)
  map_id V := NatTrans.ext (funext fun ℱ ↦ hom_ext _ _ fun T ↦ by
    rw [extendRestrictMap_app_app]
    exact ℱ.presheaf.map_id _)
  map_comp i j := NatTrans.ext (funext fun ℱ ↦ hom_ext _ _ fun T ↦ by
    rw [NatTrans.comp_app, Hom.comp_app, extendRestrictMap_app_app, extendRestrictMap_app_app,
      extendRestrictMap_app_app, ← Functor.map_comp]
    rfl)

/-- The presheaf `V ↦ j_{V,*} (ℱ|_V)` of `𝒪_X`-modules. -/
noncomputable abbrev cechPresheaf (ℱ : X.Modules) : X.Opensᵒᵖ ⥤ X.Modules :=
  (extendRestrictPresheaf X).flip.obj ℱ

lemma cechPresheaf_map_app (ℱ : X.Modules) {V W : X.Opensᵒᵖ} (i : V ⟶ W) (T : X.Opens) :
    ((cechPresheaf ℱ).map i).app T =
      (ℱ.presheaf.map (homOfLE (ι_image_preimage_mono (leOfHom i.unop) T)).op :
        Γ(ℱ, V.unop.ι ''ᵁ V.unop.ι ⁻¹ᵁ T) ⟶ Γ(ℱ, W.unop.ι ''ᵁ W.unop.ι ⁻¹ᵁ T)) :=
  extendRestrictMap_app_app _ ℱ T

variable {ι : Type u} (U : ι → X.Opens)

/-- The **sheafified Čech complex** `Č(U, ℱ)` of an `𝒪_X`-module `ℱ` for a family `U` of opens,
as a functor of `ℱ`: in degree `k` it is `∏_{y : Fin (k + 1) → ι} j_{U_y,*} (ℱ|_{U_y})`, with
`U_y = U (y 0) ⊓ ⋯ ⊓ U (y k)` and the alternating sum of the restrictions as differential. -/
noncomputable def cechResolutionFunctor : X.Modules ⥤ CochainComplex X.Modules ℕ :=
  (extendRestrictPresheaf X).flip ⋙ cechComplexFunctor U

/-- The sheafified Čech complex `Č(U, ℱ)`. -/
noncomputable abbrev cechResolution (ℱ : X.Modules) : CochainComplex X.Modules ℕ :=
  (cechResolutionFunctor U).obj ℱ

/-- The augmentation `ℱ ⟶ Č⁰(U, ℱ) = ∏ᵢ j_{U i,*} (ℱ|_{U i})`, the product of the units of the
restrictions. -/
noncomputable def cechResolutionAugmentation (ℱ : X.Modules) : ℱ ⟶ (cechResolution U ℱ).X 0 :=
  (restrictAdjunction (⊤ : X.Opens).ι).unit.app ℱ ≫
    cechAugmentation U isTerminalTop (cechPresheaf ℱ)

@[reassoc (attr := simp)]
lemma cechResolutionAugmentation_d (ℱ : X.Modules) :
    cechResolutionAugmentation U ℱ ≫ (cechResolution U ℱ).d 0 1 = 0 := by
  rw [cechResolutionAugmentation, Category.assoc]
  erw [cechAugmentation_d]
  rw [comp_zero]

/-- The augmentation `ℱ ⟶ Č(U, ℱ)`, as a morphism of complexes from `ℱ` in degree `0`. -/
noncomputable def cechResolutionι (ℱ : X.Modules) :
    (CochainComplex.single₀ X.Modules).obj ℱ ⟶ cechResolution U ℱ :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨cechResolutionAugmentation U ℱ, cechResolutionAugmentation_d U ℱ⟩

@[simp]
lemma cechResolutionι_f_zero (ℱ : X.Modules) :
    (cechResolutionι U ℱ).f 0 = cechResolutionAugmentation U ℱ := by
  simp [cechResolutionι, CochainComplex.fromSingle₀Equiv]

end Complex

section Exactness

variable {ι : Type u} (U : ι → X.Opens) (ℱ : X.Modules)

/-- The sections over `W` of the Čech complex: the Čech complex of the presheaf
`V ↦ Γ(W, j_{V,*} (ℱ|_V))`, with explicit cochains. -/
noncomputable def sectionsCechResolutionIso (W : X.Opens) :
    ((sectionsAb W).mapHomologicalComplex _).obj (cechResolution U ℱ) ≅
      (TopCat.Presheaf.cechComplex U).obj
        (cechPresheaf ℱ ⋙ SheafOfModules.evaluation X.ringCatSheaf (op W) ⋙
          forget₂ _ AddCommGrpCat.{u}) := by
  let evaluation : X.Modules ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj (op W)) :=
    SheafOfModules.evaluation X.ringCatSheaf (op W)
  letI : evaluation.Additive :=
    SheafOfModules.evaluation_additive X.ringCatSheaf (op W)
  letI : ∀ J : Type u, PreservesLimitsOfShape (Discrete J) evaluation := fun J ↦
    inferInstanceAs (PreservesLimitsOfShape (Discrete J)
      (SheafOfModules.evaluation X.ringCatSheaf (op W)))
  let coefficients : X.Opensᵒᵖ ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj (op W)) :=
    cechPresheaf ℱ ⋙ evaluation
  let comparison := TopCat.Presheaf.cechComplexFunctorIso
    (R := X.ringCatSheaf.obj.obj (op W)) U coefficients
  let evaluationComparison := cechComplexFunctorMapIso U evaluation (cechPresheaf ℱ)
  exact ((forget₂ _ AddCommGrpCat.{u}).mapHomologicalComplex _).mapIso
    evaluationComparison ≪≫ comparison

/-- Over an open `W` contained in a member of the family, the sections of the Čech complex are
exact in positive degrees. -/
lemma exactAt_sectionsAb_cechResolution {W : X.Opens} {j : ι} (hW : W ≤ U j) (n : ℕ) :
    (((sectionsAb W).mapHomologicalComplex _).obj (cechResolution U ℱ)).ExactAt (n + 1) := by
  refine (ShortComplex.exact_iff_of_iso ((HomologicalComplex.shortComplexFunctor _ _ (n + 1)).mapIso
    (sectionsCechResolutionIso U ℱ W))).mpr ?_
  refine TopCat.Presheaf.exactAt_cechComplex_of_bijective U _
    (selectedIndex := j) (fun k y ↦ ?_) n
  have hle : ((⨅ l, U (y l)) ⊓ U j).ι ''ᵁ ((⨅ l, U (y l)) ⊓ U j).ι ⁻¹ᵁ W ≥
      (⨅ l, U (y l)).ι ''ᵁ (⨅ l, U (y l)).ι ⁻¹ᵁ W := by
    rw [ι_image_preimage, ι_image_preimage, inf_assoc, inf_eq_right.mpr hW]
  have := isIso_presheaf_map_of_le ℱ (homOfLE (ι_image_preimage_mono
    (inf_le_left : (⨅ l, U (y l)) ⊓ U j ≤ _) W)) hle
  have e : (cechPresheaf ℱ ⋙ SheafOfModules.evaluation X.ringCatSheaf (op W) ⋙
      forget₂ _ AddCommGrpCat.{u}).map
      (homOfLE (inf_le_left : (⨅ l, U (y l)) ⊓ U j ≤ _)).op =
      ℱ.presheaf.map (homOfLE (ι_image_preimage_mono
        (inf_le_left : (⨅ l, U (y l)) ⊓ U j ≤ _) W)).op :=
    cechPresheaf_map_app ℱ (homOfLE (inf_le_left : (⨅ l, U (y l)) ⊓ U j ≤ _)).op W
  rw [e]
  exact ConcreteCategory.bijective_of_isIso _

/-- Restricting twice is restricting once. -/
lemma presheaf_map_map_apply_eq (M : X.Modules) {A B C : X.Opensᵒᵖ} (i : A ⟶ B) (j : B ⟶ C)
    (k : A ⟶ C) (x : M.presheaf.obj A) :
    M.presheaf.map j (M.presheaf.map i x) = M.presheaf.map k x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma ι_image_preimage_le_self (V W : X.Opens) : V.ι ''ᵁ V.ι ⁻¹ᵁ W ≤ W := by
  rw [ι_image_preimage]
  exact inf_le_right

private lemma cechPresheaf_map_map_unit (W : X.Opens) (sectionValue : Γ(ℱ, W))
    {A B : X.Opensᵒᵖ} (firstMap : op ⊤ ⟶ A) (secondMap : A ⟶ B) :
    ((cechPresheaf ℱ).map secondMap).app W (((cechPresheaf ℱ).map firstMap).app W
      (((restrictAdjunction (⊤ : X.Opens).ι).unit.app ℱ).app W sectionValue)) =
      (ℱ.presheaf.map (homOfLE (ι_image_preimage_le_self B.unop W)).op :
        Γ(ℱ, W) ⟶ Γ(ℱ, B.unop.ι ''ᵁ B.unop.ι ⁻¹ᵁ W)) sectionValue := by
  rw [cechPresheaf_map_app, cechPresheaf_map_app, restrictAdjunction_unit_app_app]
  exact (congrArg _ (presheaf_map_map_apply_eq ℱ _ _
    (homOfLE (ι_image_preimage_le_self A.unop W)).op sectionValue)).trans
      (presheaf_map_map_apply_eq ℱ _ _
        (homOfLE (ι_image_preimage_le_self B.unop W)).op sectionValue)

/-- The augmentation of the Čech complex on sections, in explicit cochains: the restrictions. -/
lemma sectionsCechResolutionIso_augmentation (W : X.Opens) (s : Γ(ℱ, W)) (y : Fin 1 → ι) :
    (sectionsCechResolutionIso U ℱ W).hom.f 0 ((cechResolutionAugmentation U ℱ).app W s) y =
      (ℱ.presheaf.map (homOfLE (ι_image_preimage_le_self (⨅ l, U (y l)) W)).op :
        Γ(ℱ, W) ⟶ Γ(ℱ, (⨅ l, U (y l)).ι ''ᵁ (⨅ l, U (y l)).ι ⁻¹ᵁ W)) s := by
  let G := SheafOfModules.evaluation X.ringCatSheaf (op W)
  let P := cechPresheaf ℱ
  have h1 : (G.map (cechResolutionAugmentation U ℱ) ≫
      (cechComplexFunctorMapIso U G P).hom.f 0) =
      G.map ((restrictAdjunction (⊤ : X.Opens).ι).unit.app ℱ) ≫
        cechAugmentation U isTerminalTop (P ⋙ G) := by
    rw [cechResolutionAugmentation, G.map_comp, Category.assoc, map_cechAugmentation_comp]
  have h2 := congrArg (fun φ ↦ TopCat.Presheaf.cechComplexFunctorXAddEquiv U (P ⋙ G) 0
    (φ s) y) h1
  dsimp only at h2
  refine Eq.trans ?_ (h2.trans ?_)
  · rfl
  have h3 := ConcreteCategory.congr_hom (cechAugmentation_π U isTerminalTop (P ⋙ G) y)
    (G.map ((restrictAdjunction (⊤ : X.Opens).ι).unit.app ℱ) s)
  rw [TopCat.Presheaf.cechComplexFunctorXAddEquiv_apply, ConcreteCategory.comp_apply,
    TopCat.Presheaf.cechComplexFunctorπ]
  erw [h3]
  exact cechPresheaf_map_map_unit ℱ W s
    (A := op (∏ᶜ fun l ↦ U (y l))) (B := op (⨅ l, U (y l)))
    (homOfLE (le_top : (∏ᶜ fun l ↦ U (y l)) ≤ ⊤)).op
    (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op

lemma bijective_sectionsCechResolutionIso_hom_f (W : X.Opens) (k : ℕ) :
    Function.Bijective ((sectionsCechResolutionIso U ℱ W).hom.f k) :=
  ConcreteCategory.bijective_of_isIso
    ((HomologicalComplex.eval _ _ k).mapIso (sectionsCechResolutionIso U ℱ W)).hom

lemma sectionsCechResolutionIso_d (W : X.Opens) (k : ℕ) (x : Γ((cechResolution U ℱ).X k, W)) :
    (sectionsCechResolutionIso U ℱ W).hom.f (k + 1) (((cechResolution U ℱ).d k (k + 1)).app W x) =
      ((TopCat.Presheaf.cechComplex U).obj
        (cechPresheaf ℱ ⋙ SheafOfModules.evaluation X.ringCatSheaf (op W) ⋙
          forget₂ _ AddCommGrpCat.{u})).d k (k + 1)
        ((sectionsCechResolutionIso U ℱ W).hom.f k x) :=
  (ConcreteCategory.congr_hom ((sectionsCechResolutionIso U ℱ W).hom.comm k (k + 1)) x).symm

/-- Over an open `W` contained in a member `U j` of the family, the augmented Čech complex is
exact on sections in degree `0`, and the augmentation is injective on sections. -/
lemma injective_and_exact_sectionsAb_cechResolution_zero {W : X.Opens} {j : ι} (hW : W ≤ U j) :
    Function.Injective ((cechResolutionAugmentation U ℱ).app W) ∧
      ((ShortComplex.mk _ _ (cechResolutionAugmentation_d U ℱ)).map (sectionsAb W)).Exact := by
  set E := sectionsCechResolutionIso U ℱ W
  let Q := cechPresheaf ℱ ⋙ SheafOfModules.evaluation X.ringCatSheaf (op W) ⋙
    forget₂ _ AddCommGrpCat.{u}
  have hQ {A B : X.Opens} (h : A ≤ B) (x : Q.obj (op B)) :
      Q.map (homOfLE h).op x = (ℱ.presheaf.map (homOfLE (ι_image_preimage_mono h W)).op :
        Γ(ℱ, B.ι ''ᵁ B.ι ⁻¹ᵁ W) ⟶ Γ(ℱ, A.ι ''ᵁ A.ι ⁻¹ᵁ W)) x :=
    ConcreteCategory.congr_hom (cechPresheaf_map_app ℱ (homOfLE h).op W) x
  -- the open `(⨅ l, U (y l)) ⊓ W` for the constant tuple `j`
  have hj : (⨅ l, U ((fun _ : Fin 1 ↦ j) l)).ι ''ᵁ
      (⨅ l, U ((fun _ : Fin 1 ↦ j) l)).ι ⁻¹ᵁ W = W := by
    rw [ι_image_preimage, iInf_const, inf_eq_right.mpr hW]
  have hinj : Function.Injective (ℱ.presheaf.map (homOfLE (ι_image_preimage_le_self
      (⨅ l, U ((fun _ : Fin 1 ↦ j) l)) W)).op) := by
    have := isIso_presheaf_map_of_le ℱ (homOfLE (ι_image_preimage_le_self
      (⨅ l, U ((fun _ : Fin 1 ↦ j) l)) W)) hj.ge
    exact (ConcreteCategory.bijective_of_isIso _).1
  refine ⟨fun s t hst ↦ hinj ?_, ?_⟩
  · have h := congrArg (fun x ↦ E.hom.f 0 x (fun _ ↦ j)) hst
    simp only [E, sectionsCechResolutionIso_augmentation] at h
    exact h
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  change ((cechResolution U ℱ).d 0 1).app W x = 0 at hx
  have hc : ((TopCat.Presheaf.cechComplex U).obj Q).d 0 1 (E.hom.f 0 x) = 0 := by
    have := sectionsCechResolutionIso_d (U := U) (ℱ := ℱ) W 0 x
    rw [hx, map_zero] at this
    exact this.symm
  set c := E.hom.f 0 x with hc_def
  let s : Γ(ℱ, W) := (ℱ.presheaf.map (homOfLE hj.ge).op :
    Γ(ℱ, (⨅ l, U ((fun _ : Fin 1 ↦ j) l)).ι ''ᵁ (⨅ l, U ((fun _ : Fin 1 ↦ j) l)).ι ⁻¹ᵁ W) ⟶
      Γ(ℱ, W)) (c (fun _ ↦ j))
  refine ⟨s, (bijective_sectionsCechResolutionIso_hom_f (U := U) (ℱ := ℱ) W 0).1 ?_⟩
  change E.hom.f 0 ((cechResolutionAugmentation U ℱ).app W s) = c
  funext y
  rw [sectionsCechResolutionIso_augmentation]
  -- the cocycle condition at the tuple `(y 0, j)`
  let z : Fin 2 → ι := Fin.cons (y 0) (fun _ ↦ j)
  have hz0 : z ∘ (0 : Fin 2).succAbove = fun _ ↦ j := by
    funext l
    fin_cases l
    rfl
  have hz1 : z ∘ (1 : Fin 2).succAbove = y := by
    funext l
    fin_cases l
    rfl
  have h0 := congrFun hc z
  rw [TopCat.Presheaf.cechComplex_d_apply, Fin.sum_univ_two] at h0
  have hzj : ⨅ l, U (z l) ≤ ⨅ l, U ((fun _ : Fin 1 ↦ j) l) := le_iInf fun _ ↦ iInf_le _ 1
  have hzy : ⨅ l, U (z l) ≤ ⨅ l, U (y l) := le_iInf fun l ↦ by
    rw [show l = 0 from Fin.ext (Nat.lt_one_iff.mp l.isLt)]
    exact iInf_le _ 0
  rw [TopCat.Presheaf.map_homOfLE_apply_congr U Q c hz0 _ hzj,
    TopCat.Presheaf.map_homOfLE_apply_congr U Q c hz1 _ hzy] at h0
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at h0
  have h0' := sub_eq_zero.mp ((sub_eq_add_neg _ _).trans h0)
  have hge : (⨅ l, U (y l)).ι ''ᵁ (⨅ l, U (y l)).ι ⁻¹ᵁ W ≤
      (⨅ l, U (z l)).ι ''ᵁ (⨅ l, U (z l)).ι ⁻¹ᵁ W := by
    rw [ι_image_preimage, ι_image_preimage]
    refine le_inf (le_iInf fun l ↦ ?_) inf_le_right
    refine Fin.cases ?_ (fun l ↦ ?_) l
    · exact inf_le_left.trans (iInf_le _ 0)
    · exact inf_le_right.trans hW
  have := isIso_presheaf_map_of_le ℱ (homOfLE (ι_image_preimage_mono hzy W)) hge
  apply (ConcreteCategory.bijective_of_isIso
    (ℱ.presheaf.map (homOfLE (ι_image_preimage_mono hzy W)).op)).1
  refine Eq.trans ?_ ((hQ hzj _).symm.trans (h0'.trans (hQ hzy (c y))))
  exact (congrArg _ (presheaf_map_map_apply_eq ℱ _ _
    (homOfLE ((ι_image_preimage_le_self _ W).trans hj.ge)).op _)).trans
    (presheaf_map_map_apply_eq ℱ _ _ _ _)

/-- The Čech complex of a cover is exact in positive degrees. -/
theorem exactAt_cechResolution (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (cechResolution U ℱ).ExactAt (n + 1) := by
  refine exactAt_of_exactAt_sectionsAb _ _ fun x V hxV ↦ ?_
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp (by rw [hU]; trivial : x ∈ ⨆ i, U i)
  exact ⟨V ⊓ U j, ⟨hxV, hj⟩, inf_le_left,
    exactAt_sectionsAb_cechResolution U ℱ inf_le_right n⟩


lemma exists_le_of_iSup_eq_top (hU : ⨆ i, U i = ⊤) (x : X) (V : X.Opens) (hxV : x ∈ V) :
    ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧ ∃ j, W ≤ U j := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp (by rw [hU]; trivial : x ∈ ⨆ i, U i)
  exact ⟨V ⊓ U j, ⟨hxV, hj⟩, inf_le_left, j, inf_le_right⟩

/-- **The Čech resolution.** For an open cover `U` of `X` and an `𝒪_X`-module `ℱ`, the augmented
sheafified Čech complex `0 ⟶ ℱ ⟶ Č⁰(U, ℱ) ⟶ Č¹(U, ℱ) ⟶ ⋯` is exact: the augmentation
`ℱ ⟶ Č(U, ℱ)` is a quasi-isomorphism from `ℱ` placed in degree `0`.

Exactness is checked on the sections over the opens `W` contained in some member `U j` of the
cover; there, inserting the index `j` contracts the Čech complex of sections.
 -/
theorem quasiIso_cechResolutionι (hU : ⨆ i, U i = ⊤) : QuasiIso (cechResolutionι U ℱ) := by
  have hmono : Mono (cechResolutionAugmentation U ℱ) := by
    refine (exact_of_exact_sectionsAb
      (ShortComplex.mk (0 : 0 ⟶ ℱ) (cechResolutionAugmentation U ℱ) zero_comp)
      fun x V hxV ↦ ?_).mono_g rfl
    obtain ⟨W, hxW, hWV, j, hWj⟩ := exists_le_of_iSup_eq_top U hU x V hxV
    refine ⟨W, hxW, hWV, ?_⟩
    rw [ShortComplex.ab_exact_iff]
    intro s hs
    refine ⟨0, ?_⟩
    refine (injective_and_exact_sectionsAb_cechResolution_zero U ℱ hWj).1 ?_
    exact (map_zero _).trans hs.symm
  exact CochainComplex.quasiIso_fromSingle₀Equiv_symm _ _
    (exact_of_exact_sectionsAb _ fun x V hxV ↦ by
      obtain ⟨W, hxW, hWV, j, hWj⟩ := exists_le_of_iSup_eq_top U hU x V hxV
      exact ⟨W, hxW, hWV, (injective_and_exact_sectionsAb_cechResolution_zero U ℱ hWj).2⟩)
    (exactAt_cechResolution U ℱ hU)

end Exactness

section Acyclic

variable {S : Scheme.{u}} (f : X ⟶ S)

/-- For an affine open `V` of a scheme `X` separated over an affine scheme `S` and a
quasi-coherent `ℱ`, the module `j_* (ℱ|_V)` is `f_*`-acyclic: the inclusion `j : V ⟶ X` and the
composite `V ⟶ S` are affine morphisms. -/
theorem rightAcyclic_extendRestrict [IsAffine S] [IsSeparated f]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules) [ℱ.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) : (pushforward f).rightAcyclic ((extendRestrictFunctor V).obj ℱ) := by
  have : IsAffine V := hV
  have := isGrothendieckAbelian V
  have : IsAffineHom V.ι := IsAffineHom.of_comp V.ι f
  exact rightAcyclic_pushforward_obj_of_isZero V.ι f _
    (fun q ↦ isZero_higherDirectImage_of_isAffineHom _ _ q.succ_pos)
    (fun q ↦ isZero_higherDirectImage_of_isAffineHom _ _ q.succ_pos)

variable {ι : Type u} (U : ι → X.Opens)

lemma piObj_eq_iInf {k : ℕ} (y : Fin (k + 1) → ι) : ∏ᶜ (fun l ↦ U (y l)) = ⨅ l, U (y l) :=
  le_antisymm (TopCat.Presheaf.piObj_le_iInf U y) (TopCat.Presheaf.iInf_le_piObj U y)

/-- **The terms of the Čech complex are `f_*`-acyclic**, for a finite cover by affine opens of a
scheme separated over an affine scheme and a quasi-coherent module.
 -/
theorem rightAcyclic_cechResolution_X [IsAffine S] [IsSeparated f] [Finite ι]
    [HasInjectiveResolutions X.Modules] (hU : ∀ i, IsAffineOpen (U i)) (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] (k : ℕ) : (pushforward f).rightAcyclic ((cechResolution U ℱ).X k) := by
  have : (pushforward f).rightAcyclic.IsClosedUnderFiniteProducts := .mk'
  change (pushforward f).rightAcyclic
    (∏ᶜ fun y : Fin (k + 1) → ι ↦ (cechPresheaf ℱ).obj (op (∏ᶜ fun l ↦ U (y l))))
  refine ObjectProperty.prop_product _ fun y ↦ ?_
  exact rightAcyclic_extendRestrict f ℱ
    ((piObj_eq_iInf U y).symm ▸ isAffineOpen_iInf_of_isSeparated f U hU k y)

/-- **The Čech resolution computes the higher direct images.** Let `f : X ⟶ S` be separated with
`S` affine, `U` a finite cover of `X` by affine opens and `ℱ` a quasi-coherent `𝒪_X`-module.
Then `R^q f_* ℱ` is the `q`-th cohomology sheaf of the complex `f_* Č(U, ℱ)` of
`𝒪_S`-modules: the augmented Čech complex is a resolution of `ℱ`
(`AlgebraicGeometry.Scheme.Modules.quasiIso_cechResolutionι`) by `f_*`-acyclic modules
(`AlgebraicGeometry.Scheme.Modules.rightAcyclic_cechResolution_X`).
 -/
noncomputable def higherDirectImageIsoCechResolution [IsAffine S] [IsSeparated f] [Finite ι]
    [HasInjectiveResolutions X.Modules] (hU : ∀ i, IsAffineOpen (U i)) (hU' : ⨆ i, U i = ⊤)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (q : ℕ) :
    (higherDirectImage f q).obj ℱ ≅
      (((pushforward f).mapHomologicalComplex _).obj (cechResolution U ℱ)).homology q :=
  have := quasiIso_cechResolutionι U ℱ hU'
  (pushforward f).rightDerivedObjIsoOfResolution (cechResolutionι U ℱ)
    (rightAcyclic_cechResolution_X f U hU ℱ) q

end Acyclic

/-! ### The module structure on the sections of the Čech resolution -/

section Sections

open TopCat.Presheaf

variable {Z : Scheme.{u}} (M : Z.Modules)

/-- The functions on `V` act on the sections over `V` of `j_* (M|_A)` through their restriction
to `A ⊓ V`. -/
lemma extendRestrict_smul (A V : Z.Opens) (r : Γ(Z, V))
    (m : Γ((extendRestrictFunctor A).obj M, V)) :
    (show Γ(M, A.ι ''ᵁ A.ι ⁻¹ᵁ V) from r • m) =
      Z.presheaf.map (homOfLE (ι_image_preimage_le_self A V)).op r •
        (show Γ(M, A.ι ''ᵁ A.ι ⁻¹ᵁ V) from m) := by
  change (A.ι.appIso (A.ι ⁻¹ᵁ V)).inv (A.ι.app V r) • (show Γ(M, A.ι ''ᵁ A.ι ⁻¹ᵁ V) from m) = _
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.app_appIso_inv]
  rfl

variable {ι : Type u} (U : ι → Z.Opens)

/-- The sections of the Čech resolution in explicit cochains, through the restriction maps of the
presheaf `V ↦ j_{V,*} (M|_V)`. -/
lemma sectionsCechResolutionIso_hom_f_apply (V : Z.Opens) (k : ℕ)
    (x : Γ((cechResolution U M).X k, V)) (y : Fin (k + 1) → ι) :
    (sectionsCechResolutionIso U M V).hom.f k x y =
      Hom.app ((cechPresheaf M).map (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op) V
        (Hom.app (Pi.π (fun y : Fin (k + 1) → ι ↦ (cechPresheaf M).obj (op (∏ᶜ fun l ↦ U (y l))))
          y) V x) := by
  change cechComplexFunctorXAddEquiv U (cechPresheaf M ⋙ SheafOfModules.evaluation Z.ringCatSheaf (op V)) k
    ((cechComplexFunctorMapIso U (SheafOfModules.evaluation Z.ringCatSheaf (op V)) (cechPresheaf M)).hom.f k x) y = _
  rw [cechComplexFunctorXAddEquiv_apply, cechComplexFunctorMapIso_hom_f, cechComplexFunctorπ]
  have h := ConcreteCategory.congr_hom (piComparison_comp_π (SheafOfModules.evaluation Z.ringCatSheaf (op V))
    (fun y : Fin (k + 1) → ι ↦ (cechPresheaf M).obj (op (∏ᶜ fun l ↦ U (y l)))) y) x
  rw [ConcreteCategory.comp_apply] at h
  exact congrArg _ h

/-- The identification of the sections of the Čech resolution with explicit cochains is linear
over the functions. -/
lemma sectionsCechResolutionIso_hom_f_smul (V : Z.Opens) (k : ℕ) (r : Γ(Z, V))
    (x : Γ((cechResolution U M).X k, V)) (y : Fin (k + 1) → ι) :
    (sectionsCechResolutionIso U M V).hom.f k (r • x) y =
      (show Γ((cechPresheaf M).obj (op (⨅ l, U (y l))), V) from
        r • (show Γ((cechPresheaf M).obj (op (⨅ l, U (y l))), V) from
          (sectionsCechResolutionIso U M V).hom.f k x y)) := by
  rw [sectionsCechResolutionIso_hom_f_apply, sectionsCechResolutionIso_hom_f_apply,
    Hom.app_smul, Hom.app_smul]

/-- The restriction of a section of the Čech resolution, in explicit cochains. -/
lemma sectionsCechResolutionIso_hom_f_presheaf_map {V V' : Z.Opens} (h : V' ≤ V) (k : ℕ)
    (x : Γ((cechResolution U M).X k, V)) (y : Fin (k + 1) → ι) :
    (sectionsCechResolutionIso U M V').hom.f k
        (((cechResolution U M).X k).presheaf.map (homOfLE h).op x) y =
      ((cechPresheaf M).obj (op (⨅ l, U (y l)))).presheaf.map (homOfLE h).op
        ((sectionsCechResolutionIso U M V).hom.f k x y) := by
  rw [sectionsCechResolutionIso_hom_f_apply, sectionsCechResolutionIso_hom_f_apply]
  erw [Hom.app_presheaf_map (Pi.π _ y) (homOfLE h) x]
  exact Hom.app_presheaf_map _ (homOfLE h) _

lemma sectionsCechResolutionIso_inv_hom_f_apply (V : Z.Opens) (k : ℕ)
    (x : Γ((cechResolution U M).X k, V)) :
    (sectionsCechResolutionIso U M V).inv.f k ((sectionsCechResolutionIso U M V).hom.f k x) =
      x := by
  change ((sectionsCechResolutionIso U M V).hom.f k ≫
    (sectionsCechResolutionIso U M V).inv.f k) x = x
  rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  rfl

lemma sectionsCechResolutionIso_hom_inv_f_apply (V : Z.Opens) (k : ℕ) (c) :
    (sectionsCechResolutionIso U M V).hom.f k ((sectionsCechResolutionIso U M V).inv.f k c) =
      c := by
  change ((sectionsCechResolutionIso U M V).inv.f k ≫
    (sectionsCechResolutionIso U M V).hom.f k) c = c
  rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  rfl

/-- The inverse sections identification commutes with the Cech differentials. -/
lemma sectionsCechResolutionIso_inv_f_d {scheme : Scheme.{u}} {indices : Type u}
    (opens : indices → scheme.Opens) (coefficients : scheme.Modules)
    (openSubset : scheme.Opens) (degree : ℕ) (cochain) :
    (sectionsCechResolutionIso opens coefficients openSubset).inv.f (degree + 1)
        (((TopCat.Presheaf.cechComplex opens).obj
          (cechPresheaf coefficients ⋙ sectionsAb openSubset)).d degree (degree + 1) cochain) =
      Hom.app ((cechResolution opens coefficients).d degree (degree + 1)) openSubset
        ((sectionsCechResolutionIso opens coefficients openSubset).inv.f degree cochain) := by
  apply (bijective_sectionsCechResolutionIso_hom_f opens coefficients openSubset
    (degree + 1)).injective
  rw [sectionsCechResolutionIso_hom_inv_f_apply, sectionsCechResolutionIso_d,
    sectionsCechResolutionIso_hom_inv_f_apply]

lemma cechPresheaf_obj_presheaf_map_apply (A : Z.Opens) {V V' : Z.Opens} (h : V' ≤ V)
    (x : Γ(M, A.ι ''ᵁ A.ι ⁻¹ᵁ V)) :
    ((cechPresheaf M).obj (op A)).presheaf.map (homOfLE h).op x =
      M.presheaf.map (homOfLE (by
          rw [ι_image_preimage, ι_image_preimage]; exact inf_le_inf_left A h :
        A.ι ''ᵁ A.ι ⁻¹ᵁ V' ≤ A.ι ''ᵁ A.ι ⁻¹ᵁ V)).op x :=
  rfl

end Sections

end AlgebraicGeometry.Scheme.Modules
