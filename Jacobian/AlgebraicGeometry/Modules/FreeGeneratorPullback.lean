import Jacobian.AlgebraicGeometry.Modules.FreeGenerator
import Jacobian.AlgebraicGeometry.Modules.Endomorphism

/-!
# Pullback of local generators

Trivializations along open immersions identify generators with isomorphisms
from the structure sheaf. Pullback preserves these generators and the scalar
coefficients of maps between trivialized module sheaves.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Pullback of an endomorphism of the structure sheaf pulls back its coefficient. -/
lemma pullbackObjUnitIso_conj_app_top {Y : Scheme.{u}} (h : Y ⟶ X)
    (f : Modules.unit X ⟶ Modules.unit X) :
    ((pullbackObjUnitIso h).inv ≫ (pullback h).map f ≫ (pullbackObjUnitIso h).hom).app ⊤
      (1 : Γ(Y, ⊤)) = h.appTop (f.app ⊤ (1 : Γ(X, ⊤))) := by
  set F := (pullbackObjUnitIso h).inv ≫ (pullback h).map f ≫ (pullbackObjUnitIso h).hom
  have hF : (pullback h).map f ≫ (pullbackObjUnitIso h).hom =
      (pullbackObjUnitIso h).hom ≫ F := by
    simp [F]
  have key := congrArg ((pullbackPushforwardAdjunction h).homEquiv _ _) hF
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at key
  have h2 : (pullbackPushforwardAdjunction h).homEquiv _ _ (pullbackObjUnitIso h).hom =
      SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [h2] at key
  have := congrArg (fun (φ : Modules.unit X ⟶ (pushforward h).obj (Modules.unit Y)) ↦
    (Hom.app φ ⊤) (1 : Γ(X, ⊤))) key
  dsimp only at this
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply] at this
  have e1 : (Hom.app (SheafOfModules.unitToPushforwardObjUnit (Hom.toRingCatSheafHom h)) ⊤)
      (1 : Γ(X, ⊤)) = (1 : Γ(Y, ⊤)) :=
    map_one h.appTop.hom
  exact (this.trans (congrArg (Hom.app F (h ⁻¹ᵁ ⊤)) e1)).symm

/-- A map between trivialized module sheaves acts by its scalar coefficient. -/
lemma app_app_top_one {Z : Scheme.{u}} (j : Z ⟶ X) [IsOpenImmersion j] {P Q : X.Modules}
    (αP : Modules.unit Z ⟶ P.restrict j) (αQ : Modules.unit Z ≅ Q.restrict j) (φ : P ⟶ Q) :
    φ.app (j ''ᵁ ⊤) ((P.restrictAppIso j ⊤).hom (αP.app ⊤ (1 : Γ(Z, ⊤)))) =
      (j.appIso ⊤).inv ((αP ≫ (restrictFunctor j).map φ ≫ αQ.inv).app ⊤ (1 : Γ(Z, ⊤))) •
        (Q.restrictAppIso j ⊤).hom (αQ.hom.app ⊤ (1 : Γ(Z, ⊤))) := by
  set c : Γ(Z, ⊤) := (αP ≫ (restrictFunctor j).map φ ≫ αQ.inv).app ⊤ (1 : Γ(Z, ⊤))
  have h1 : αP ≫ (restrictFunctor j).map φ =
      (αP ≫ (restrictFunctor j).map φ ≫ αQ.inv) ≫ αQ.hom := by
    simp
  have h2 := congrArg (fun (ψ : Modules.unit Z ⟶ Q.restrict j) ↦ ψ.app ⊤ (1 : Γ(Z, ⊤))) h1
  dsimp only at h2
  simp only [Hom.comp_app, ConcreteCategory.comp_apply] at h2
  have h3 : αQ.hom.app ⊤ c = c • αQ.hom.app ⊤ (1 : Γ(Z, ⊤)) := by
    rw [← Hom.app_smul]
    congr 1
    exact (mul_one c).symm
  rw [← smul_restrictAppIso_hom_apply]
  exact h2.trans h3

/-- On sections, a morphism `α : 𝒪_Z ⟶ Q|_Z` is multiplication with its value at `1`. -/
lemma restrictAppIso_hom_comp_app_comp_appIso_hom {Z : Scheme.{u}} (j : Z ⟶ X)
    [IsOpenImmersion j] {Q : X.Modules} (α : Modules.unit Z ⟶ Q.restrict j) (W : Z.Opens)
    (h : j ''ᵁ W ≤ j ''ᵁ ⊤) :
    (Q.restrictAppIso j W).hom ∘ α.app W ∘ (j.appIso W).hom = fun r : Γ(X, j ''ᵁ W) ↦
      r • Q.presheaf.map (homOfLE h).op ((Q.restrictAppIso j ⊤).hom (α.app ⊤ (1 : Γ(Z, ⊤)))) := by
  funext r
  have h1 : (j.appIso W).hom r =
      (j.appIso W).hom r • (Z.presheaf.map (homOfLE le_top).op (1 : Γ(Z, ⊤))) := by
    rw [map_one]
    exact (mul_one _).symm
  simp only [Function.comp_apply]
  rw [h1, Hom.app_smul, smul_restrictAppIso_hom_apply, Iso.hom_inv_id_apply]
  congr 1
  exact congrArg (Q.restrictAppIso j W).hom
    (Hom.app_presheaf_map α (homOfLE le_top) (1 : Γ(Z, ⊤)))

/-- The value at `1` of a morphism `α : 𝒪_Z ⟶ Q|_Z` along an open immersion `j` is a free
generator of `Q` on the image of `j` if and only if `α` is an isomorphism. -/
lemma isFreeGenerator_iff_isIso {Z : Scheme.{u}} (j : Z ⟶ X) [IsOpenImmersion j]
    {Q : X.Modules} (α : Modules.unit Z ⟶ Q.restrict j) :
    IsFreeGenerator ((Q.restrictAppIso j ⊤).hom (α.app ⊤ (1 : Γ(Z, ⊤)))) ↔ IsIso α := by
  rw [Hom.isIso_iff_isIso_app]
  refine ⟨fun hα W ↦ ?_, fun hα V hV ↦ ?_⟩
  · have hb := hα (j ''ᵁ W) (j.image_mono le_top)
    rw [← restrictAppIso_hom_comp_app_comp_appIso_hom] at hb
    rw [ConcreteCategory.isIso_iff_bijective]
    rw [(ConcreteCategory.bijective_of_isIso _).of_comp_iff'] at hb
    have hc : Function.Bijective (j.appIso W).hom := ConcreteCategory.bijective_of_isIso _
    exact (Function.Bijective.of_comp_iff _ hc).mp hb
  · obtain ⟨W, rfl⟩ : ∃ W, j ''ᵁ W = V := ⟨j ⁻¹ᵁ V, by
      rw [j.image_preimage_eq_opensRange_inf, ← j.image_top_eq_opensRange, inf_eq_right.mpr hV]⟩
    rw [← restrictAppIso_hom_comp_app_comp_appIso_hom]
    exact ((ConcreteCategory.bijective_of_isIso _).comp
      (ConcreteCategory.bijective_of_isIso _)).comp (ConcreteCategory.bijective_of_isIso _)

/-- The global section of `P|_Z`, as a compatible family, given by a section of `P` over the
image of the open immersion `j`. -/
noncomputable def restrictSectionsMk {Z : Scheme.{u}} (j : Z ⟶ X) [IsOpenImmersion j]
    (P : X.Modules) (e : Γ(P, j ''ᵁ ⊤)) : (P.restrict j).sections :=
  PresheafOfModules.sectionsMk
    (fun W ↦ (P.restrict j).val.map (homOfLE le_top : W.unop ⟶ ⊤).op
      ((P.restrictAppIso j ⊤).inv e))
    (fun W _ f ↦ (ConcreteCategory.congr_hom ((P.restrict j).presheaf.map_comp
        (homOfLE le_top : W.unop ⟶ ⊤).op f) _).symm)

/-- The morphism `𝒪_Z ⟶ P|_Z` sending `1` to a section `e` of `P` over the image of the open
immersion `j`. -/
noncomputable def unitToRestrict {Z : Scheme.{u}} (j : Z ⟶ X) [IsOpenImmersion j]
    (P : X.Modules) (e : Γ(P, j ''ᵁ ⊤)) : Modules.unit Z ⟶ P.restrict j :=
  (P.restrict j).unitHomEquiv.symm (restrictSectionsMk j P e)

lemma restrictAppIso_hom_unitToRestrict_app_top {Z : Scheme.{u}} (j : Z ⟶ X)
    [IsOpenImmersion j] (P : X.Modules) (e : Γ(P, j ''ᵁ ⊤)) :
    (P.restrictAppIso j ⊤).hom ((unitToRestrict j P e).app ⊤ (1 : Γ(Z, ⊤))) = e := by
  have := congrArg (fun s ↦ s.val (Opposite.op ⊤))
    ((P.restrict j).unitHomEquiv.apply_symm_apply (restrictSectionsMk j P e))
  rw [SheafOfModules.unitHomEquiv_apply_coe] at this
  refine (congrArg (P.restrictAppIso j ⊤).hom this).trans ?_
  have h1 : (P.restrict j).presheaf.map (homOfLE le_top : (⊤ : Z.Opens) ⟶ ⊤).op =
      𝟙 _ := by
    rw [← (P.restrict j).presheaf.map_id]
    rfl
  exact (congrArg (P.restrictAppIso j ⊤).hom
    (ConcreteCategory.congr_hom h1 ((P.restrictAppIso j ⊤).inv e))).trans
    (Iso.inv_hom_id_apply _ _)

/-- Restricting to an open `U` and then pulling back along `g ∣_ U` is pulling back along `g`
and then restricting to `g ⁻¹ᵁ U`. -/
noncomputable def restrictFunctorCompPullbackIso {Y : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens) :
    restrictFunctor U.ι ⋙ pullback (g ∣_ U) ≅ pullback g ⋙ restrictFunctor (g ⁻¹ᵁ U).ι :=
  Functor.isoWhiskerRight (restrictFunctorIsoPullback U.ι) (pullback (g ∣_ U)) ≪≫
    pullbackComp (g ∣_ U) U.ι ≪≫ pullbackCongr (morphismRestrict_ι g U) ≪≫
    (pullbackComp (g ⁻¹ᵁ U).ι g).symm ≪≫
    Functor.isoWhiskerLeft (pullback g) (restrictFunctorIsoPullback (g ⁻¹ᵁ U).ι).symm

/-- **Free generators pull back to free generators.** If `M` and `N` have free generators
`eM` and `eN` on `W` and `φ(eM) = b • eN`, then `g^* M` and `g^* N` have free generators on
`g ⁻¹ᵁ W` on which `g^* φ` has coefficient `g^♯ b`. -/
lemma IsFreeGenerator.exists_pullback {Y : Scheme.{u}} (g : Y ⟶ X)
    (φ : M ⟶ N) {W : X.Opens} {eM : Γ(M, W)} {eN : Γ(N, W)} (hM : IsFreeGenerator eM)
    (hN : IsFreeGenerator eN) {b : Γ(X, W)} (hb : φ.app W eM = b • eN) :
    ∃ (eM' : Γ((pullback g).obj M, g ⁻¹ᵁ W)) (eN' : Γ((pullback g).obj N, g ⁻¹ᵁ W)),
      IsFreeGenerator eM' ∧ IsFreeGenerator eN' ∧
        ((pullback g).map φ).app (g ⁻¹ᵁ W) eM' = g.app W b • eN' := by
  have hW : W.ι ''ᵁ ⊤ ≤ W := (Opens.ι_image_top W).le
  set αM := unitToRestrict W.ι M (M.presheaf.map (homOfLE hW).op eM)
  set αN := unitToRestrict W.ι N (N.presheaf.map (homOfLE hW).op eN)
  have hαM : IsIso αM := by
    rw [← isFreeGenerator_iff_isIso, restrictAppIso_hom_unitToRestrict_app_top]
    exact hM.map hW
  have hαN : IsIso αN := by
    rw [← isFreeGenerator_iff_isIso, restrictAppIso_hom_unitToRestrict_app_top]
    exact hN.map hW
  set F := αM ≫ (restrictFunctor W.ι).map φ ≫ inv αN
  have hF : (W.ι.appIso ⊤).inv (F.app ⊤ (1 : Γ(W.toScheme, ⊤))) =
      X.presheaf.map (homOfLE hW).op b := by
    have h1 := app_app_top_one W.ι αM (asIso αN) φ
    rw [asIso_hom, restrictAppIso_hom_unitToRestrict_app_top,
      restrictAppIso_hom_unitToRestrict_app_top, Hom.app_presheaf_map, hb, map_smul] at h1
    exact ((hN.map hW).smul_left_injective h1).symm
  set κ := restrictFunctorCompPullbackIso g W
  set αM' : Modules.unit (g ⁻¹ᵁ W).toScheme ⟶ ((pullback g).obj M).restrict (g ⁻¹ᵁ W).ι :=
    (pullbackObjUnitIso (g ∣_ W)).inv ≫ (pullback (g ∣_ W)).map αM ≫ κ.hom.app M
  set αN' : Modules.unit (g ⁻¹ᵁ W).toScheme ⟶ ((pullback g).obj N).restrict (g ⁻¹ᵁ W).ι :=
    (pullbackObjUnitIso (g ∣_ W)).inv ≫ (pullback (g ∣_ W)).map αN ≫ κ.hom.app N
  have hcoef : αM' ≫ (restrictFunctor (g ⁻¹ᵁ W).ι).map ((pullback g).map φ) ≫ inv αN' =
      (pullbackObjUnitIso (g ∣_ W)).inv ≫ (pullback (g ∣_ W)).map F ≫
        (pullbackObjUnitIso (g ∣_ W)).hom := by
    have := κ.hom.naturality φ
    simp only [Functor.comp_map] at this
    simp only [αM', αN', F, IsIso.inv_comp, Functor.map_comp, Functor.map_inv, Category.assoc]
    rw [← reassoc_of% this]
    simp
  have h2 := app_app_top_one (g ⁻¹ᵁ W).ι αM' (asIso αN') ((pullback g).map φ)
  rw [asIso_hom, asIso_inv, hcoef, pullbackObjUnitIso_conj_app_top] at h2
  have hW' : g ⁻¹ᵁ W ≤ (g ⁻¹ᵁ W).ι ''ᵁ ⊤ := (Opens.ι_image_top _).ge
  refine ⟨_, _, (((isFreeGenerator_iff_isIso _ αM').mpr inferInstance).map hW'),
    (((isFreeGenerator_iff_isIso _ αN').mpr inferInstance).map hW'), ?_⟩
  rw [Hom.app_presheaf_map, h2, map_smul]
  congr 1
  have hid₁ (x : Γ(Y, (g ⁻¹ᵁ W).ι ''ᵁ ⊤)) : ((g ⁻¹ᵁ W).ι.appIso ⊤).inv x = x := by
    rw [Opens.ι_appIso]
    rfl
  have hid₂ (x : Γ(X, W.ι ''ᵁ ⊤)) : (W.ι.appIso ⊤).hom x = x := by
    rw [Opens.ι_appIso]
    rfl
  rw [← Iso.inv_hom_id_apply (W.ι.appIso ⊤) (F.app ⊤ (1 : Γ(W.toScheme, ⊤))), hF, hid₂, hid₁,
    morphismRestrict_appTop]
  have key : X.presheaf.map (homOfLE hW).op ≫ g.app (W.ι ''ᵁ ⊤) ≫
      Y.presheaf.map (eqToHom (image_morphismRestrict_preimage g W ⊤)).op ≫
        Y.presheaf.map (homOfLE hW').op = g.app W := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
    rw [Scheme.Hom.map_appLE_assoc, ← Functor.map_comp, Scheme.Hom.appLE_map]
  exact ConcreteCategory.congr_hom key b


end AlgebraicGeometry.Scheme.Modules
