import Jacobian.AlgebraicGeometry.Modules.GlobalSection
import Jacobian.AlgebraicGeometry.Modules.PullbackUnit
import Jacobian.CategoryTheory.Sites.Descent.PullHom

/-!
# Sections of pulled-back module morphisms

Morphisms from the pulled-back structure module are determined by the section given by the image of one.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y Z : Scheme.{u}}

section
variable (g : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
/-- The pullback of the section `φ 1` attached to a morphism `φ : 𝒪_Y ⟶ M` is the section
attached to the pullback `𝒪_X ≅ g^* 𝒪_Y ⟶ g^* M` of `φ`. -/
lemma pullbackSection_app_one {M : Y.Modules} (φ : Modules.unit Y ⟶ M) :
    pullbackSection g (Hom.app φ ⊤ (1 : Γ(Y, ⊤))) =
      Hom.app ((pullbackObjUnitIso g).inv ≫ (pullback g).map φ) (g ⁻¹ᵁ ⊤) (1 : Γ(X, ⊤)) := by
  have h1 := (pullbackPushforwardAdjunction g).unit.naturality φ
  have h2 : (pullbackPushforwardAdjunction g).homEquiv _ _ (pullbackObjUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [Adjunction.homEquiv_unit] at h2
  have h3 := congrArg (fun ψ : Modules.unit Y ⟶ (pushforward g).obj (Modules.unit X) ↦
    (Hom.app ψ ⊤) (1 : Γ(Y, ⊤))) h2
  have h1' := congrArg (fun ψ : Modules.unit Y ⟶ (pushforward g).obj ((pullback g).obj M) ↦
    (Hom.app ψ ⊤) (1 : Γ(Y, ⊤))) h1
  have e1 : (Hom.app (SheafOfModules.unitToPushforwardObjUnit (Hom.toRingCatSheafHom g)) ⊤)
      (1 : Γ(Y, ⊤)) = (1 : Γ(X, ⊤)) :=
    map_one g.appTop.hom
  dsimp only at h1' h3
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply, Functor.id_map,
    Functor.comp_map] at h1' h3
  have h4 : (Hom.app ((pullbackPushforwardAdjunction g).unit.app (Modules.unit Y)) ⊤)
      (1 : Γ(Y, ⊤)) = Hom.app (pullbackObjUnitIso g).inv (g ⁻¹ᵁ ⊤) (1 : Γ(X, ⊤)) := by
    have h5 (x : Γ((pullback g).obj (Modules.unit Y), g ⁻¹ᵁ ⊤)) :
        Hom.app (pullbackObjUnitIso g).inv (g ⁻¹ᵁ ⊤)
          (Hom.app (pullbackObjUnitIso g).hom (g ⁻¹ᵁ ⊤) x) = x := by
      rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.hom_inv_id, Hom.id_app]
      rfl
    exact (h5 _).symm.trans (congrArg (Hom.app (pullbackObjUnitIso g).inv (g ⁻¹ᵁ ⊤))
      (h3.trans e1))
  exact h1'.trans (congrArg (Hom.app ((pullback g).map φ) (g ⁻¹ᵁ ⊤)) h4)


end

lemma pullbackSection_pullbackSection (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} {U : Z.Opens} (m : Γ(M, U)) :
    pullbackSection f (pullbackSection g m) =
      ((pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U) (pullbackSection (f ≫ g) m) := by
  have h := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv] at h
  have h' := congr_arg (fun φ ↦ (Hom.app φ U) m) h
  simp only at h'
  exact h'

/-- The section `φ(1)` of `f^* A` attached to `φ : f^* 𝒪 ⟶ f^* A`. -/
noncomputable def homSection (f : Y ⟶ X) {A : X.Modules}
    (φ : (pullback f).obj (unit X) ⟶ (pullback f).obj A) : Γ((pullback f).obj A, f ⁻¹ᵁ ⊤) :=
  φ.app (f ⁻¹ᵁ ⊤) (pullbackSection f (1 : Γ(X, ⊤)))

lemma homSection_comp (f : Y ⟶ X) (g : Z ⟶ Y) {A : X.Modules}
    (φ : (pullback f).obj (unit X) ⟶ (pullback f).obj A) :
    homSection (g ≫ f) ((pullbackComp g f).inv.app _ ≫ (pullback g).map φ ≫
        (pullbackComp g f).hom.app A) =
      ((pullbackComp g f).hom.app A).app _ (pullbackSection g (homSection f φ)) := by
  have h1 := pullbackSection_pullbackSection g f (M := unit X) (1 : Γ(X, ⊤))
  have h2 := congrArg (fun ψ ↦ Hom.app ψ (f ⁻¹ᵁ ⊤) (pullbackSection f (M := unit X) (1 : Γ(X, ⊤))))
    ((pullbackPushforwardAdjunction g).unit.naturality φ)
  simp only [Functor.id_map, Functor.comp_map, Hom.comp_app, pushforward_map_app,
    ConcreteCategory.comp_apply] at h2
  simp only [homSection, Hom.comp_app, ConcreteCategory.comp_apply]
  rw [← h1]
  exact congrArg _ h2.symm

lemma unit_hom_ext {N : Y.Modules} {ψ₁ ψ₂ : unit Y ⟶ N}
    (h : ψ₁.app ⊤ (1 : Γ(Y, ⊤)) = ψ₂.app ⊤ (1 : Γ(Y, ⊤))) : ψ₁ = ψ₂ := by
  ext U x
  let x' : Γ(Y, U) := x
  have e (ψ : unit Y ⟶ N) : ψ.app U x =
      x' • N.presheaf.map (homOfLE (le_top (a := U))).op (ψ.app ⊤ (1 : Γ(Y, ⊤))) := by
    have h₁ : ψ.app U x = x' • ψ.app U (show Γ(unit Y, U) from (1 : Γ(Y, U))) := by
      rw [← Hom.app_smul]
      congr 1
      exact (mul_one x').symm
    have h₂ : ψ.app U (show Γ(unit Y, U) from (1 : Γ(Y, U))) =
        N.presheaf.map (homOfLE (le_top (a := U))).op
          (ψ.app ⊤ (show Γ(unit Y, ⊤) from (1 : Γ(Y, ⊤)))) := by
      rw [← Hom.app_presheaf_map]
      congr 1
      exact (map_one (Y.presheaf.map (homOfLE (le_top (a := U))).op).hom).symm
    rw [h₁, h₂]
  rw [e ψ₁, e ψ₂, h]

lemma homSection_injective (f : Y ⟶ X) {A : X.Modules} :
    Function.Injective (homSection f (A := A)) := by
  intro φ ψ h
  have e1 : pullbackSection f (M := unit X) (1 : Γ(X, ⊤)) =
      Hom.app (pullbackObjUnitIso f).inv (f ⁻¹ᵁ ⊤) (1 : Γ(Y, ⊤)) := by
    have := pullbackSection_app_one f (𝟙 (unit X))
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at this
    exact this
  have key : (pullbackObjUnitIso f).inv ≫ φ = (pullbackObjUnitIso f).inv ≫ ψ := by
    apply unit_hom_ext
    simp only [homSection, e1] at h
    simp only [Hom.comp_app]
    exact h
  have := congrArg ((pullbackObjUnitIso f).hom ≫ ·) key
  erw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc] at this
  exact this

open Pseudofunctor.LocallyDiscreteOpToCat in
set_option backward.isDefEq.respectTransparency.types false in
lemma pullHom_eq_pullbackComp (f : Y ⟶ X) (g : Z ⟶ Y) {B A : modulesPseudofunctor.obj (.mk (op X))}
    (φ : (modulesPseudofunctor.map f.op.toLoc).toFunctor.obj B ⟶
      (modulesPseudofunctor.map f.op.toLoc).toFunctor.obj A) :
    pullHom (F := modulesPseudofunctor) φ g (g ≫ f) (g ≫ f) rfl rfl =
      (pullbackComp g f).inv.app (B : X.Modules) ≫ (pullback g).map φ ≫
        (pullbackComp g f).hom.app (A : X.Modules) := by
  dsimp only [pullHom]
  erw [Pseudofunctor.mapComp'_eq_mapComp]
  rfl

lemma pullbackSection_one_eq (f : Y ⟶ X) :
    pullbackSection f (M := unit X) (1 : Γ(X, ⊤)) =
      Hom.app (pullbackObjUnitIso f).inv (f ⁻¹ᵁ ⊤) (1 : Γ(Y, ⊤)) := by
  have := pullbackSection_app_one f (𝟙 (unit X))
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at this
  exact this

end AlgebraicGeometry.Scheme.Modules
