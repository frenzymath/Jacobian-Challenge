import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Affine coordinates in base-changed families

Coordinate rings of affine opens in a family form directed systems. On affine
source and target opens, pullback morphisms are identified with tensor products
of the corresponding algebra maps. The comparisons respect arbitrary further
base change and include empty affine opens.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in

/-- Global sections of pulled-back affine opens give a directed ring-colimit presentation. -/
theorem exists_affineOpen_directedRingSystem
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (W : (D.obj (op i₀)).Opens) (hW : IsAffineOpen W) :
    ∃ (F : {i : I // i₀ ≤ i} ⥤ CommRingCat.{u})
      (e0 : W.toScheme ≅ Spec (F.obj ⟨i₀, le_rfl⟩)),
      (∀ i : {i : I // i₀ ≤ i},
        ∃ e : (D.map (homOfLE i.property).op ⁻¹ᵁ W).toScheme ≅ Spec (F.obj i),
          (D.map (homOfLE i.property).op).resLE W _ le_rfl ≫ e0.hom =
            e.hom ≫ Spec.map (F.map (homOfLE i.property))) ∧
      ∃ eL : (c.π.app (op i₀) ⁻¹ᵁ W).toScheme ≅ Spec (colimit F),
        (c.π.app (op i₀)).resLE W _ le_rfl ≫ e0.hom =
          eL.hom ≫ Spec.map (colimit.ι F ⟨i₀, le_rfl⟩) := by
  classical
  let : Nonempty I := ⟨i₀⟩
  let J := {i : I // i₀ ≤ i}
  let o : J := ⟨i₀, le_rfl⟩
  let : Nonempty J := ⟨o⟩
  let : IsDirected J (· ≤ ·) := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let K : Jᵒᵖ ⥤ Over (op i₀) :=
    { obj := fun i ↦ Over.mk (homOfLE i.unop.property).op
      map := fun {i j} f ↦ Over.homMk (homOfLE (leOfHom f.unop)).op
        (Subsingleton.elim _ _)
      map_id := by intro i; apply Over.OverMorphism.ext; apply Subsingleton.elim
      map_comp := by intros; apply Over.OverMorphism.ext; apply Subsingleton.elim }
  let : K.Initial := Functor.initial_of_exists_of_isCofiltered K
    (fun i ↦ ⟨op ⟨i.left.unop, leOfHom i.hom.unop⟩,
      ⟨Over.homMk (𝟙 _) (Subsingleton.elim _ _)⟩⟩)
    (fun {_ _} f g ↦ ⟨_, 𝟙 _, by
      apply Over.OverMorphism.ext
      apply Subsingleton.elim⟩)
  let E := K ⋙ opensDiagram D (op i₀) W
  let cE : Cone E := (opensCone D c (op i₀) W).whisker K
  have hE : IsLimit cE :=
    (Functor.Initial.isLimitWhiskerEquiv K _).symm (isLimitOpensCone D c hc (op i₀) W)
  let (i : Jᵒᵖ) : IsAffine (E.obj i) := hW.preimage (D.map (homOfLE i.unop.property).op)
  let : IsAffine cE.pt := Scheme.isAffine_of_isLimit cE hE
  let F : J ⥤ CommRingCat := E.rightOp ⋙ Scheme.Γ
  let (i : J) : IsAffine (E.rightOp.obj i).unop := inferInstanceAs (IsAffine (E.obj (op i)))
  let hΓ := isColimitOfPreserves Scheme.Γ (isColimitCoconeRightOpOfCone E hE)
  let eΓ := hΓ.coconePointUniqueUpToIso (colimit.isColimit F)
  have h₀ : D.map (homOfLE o.property).op ⁻¹ᵁ W = W := by
    have : (homOfLE o.property).op = 𝟙 (op i₀) := Subsingleton.elim _ _
    rw [this, D.map_id]
    rfl
  let q : E.obj (op o) ≅ W.toScheme := (D.obj (op i₀)).isoOfEq h₀
  let e0 : W.toScheme ≅ Spec (F.obj o) := q.symm ≪≫ (E.obj (op o)).isoSpec
  refine ⟨F, e0, ?_, ?_⟩
  · intro i
    refine ⟨(E.obj (op i)).isoSpec, ?_⟩
    have hm : E.map (homOfLE (show o ≤ i from i.property)).op ≫ q.hom =
        (D.map (homOfLE i.property).op).resLE W _ le_rfl := by
      rw [← cancel_mono W.ι]
      simp only [E, Functor.comp_map, opensDiagram_map, K,
        Category.assoc, q, Scheme.isoOfEq_hom_ι, Scheme.Hom.resLE_comp_ι]
      congr 2
    dsimp [e0]
    rw [← hm, Category.assoc, Iso.hom_inv_id_assoc]
    exact (Scheme.isoSpec_hom_naturality (E.map (homOfLE i.property).op)).symm
  · let eL : cE.pt ≅ Spec (colimit F) :=
      cE.pt.isoSpec ≪≫ Scheme.Spec.mapIso eΓ.symm.op
    refine ⟨eL, ?_⟩
    have hm : cE.π.app (op o) ≫ q.hom =
        (c.π.app (op i₀)).resLE W _ le_rfl := by
      rw [← cancel_mono W.ι]
      simp [cE, K, q, o, Scheme.Hom.resLE_comp_ι]
    dsimp [e0, eL]
    rw [← hm, Category.assoc, Iso.hom_inv_id_assoc]
    rw [Category.assoc, ← Spec.map_comp]
    have hι := hΓ.comp_coconePointUniqueUpToIso_inv (colimit.isColimit F) o
    change colimit.ι F o ≫ eΓ.inv = (cE.π.app (op o)).appTop at hι
    change cE.π.app (op o) ≫ (E.obj (op o)).isoSpec.hom =
      cE.pt.isoSpec.hom ≫ Spec.map (colimit.ι F o ≫ eΓ.inv)
    rw [hι]
    exact (Scheme.isoSpec_hom_naturality (X := cE.pt) (Y := E.obj (op o))
      (cE.π.app (op o))).symm

end AlgebraicGeometry
end

section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
private theorem composite_pullback_square
    {S T Z L : Scheme.{u}} (z : Z ⟶ S) (d : T ⟶ S) (t : L ⟶ T) :
    IsPullback
      ((pullbackLeftPullbackSndIso z d t).inv ≫
        pullback.fst (pullback.snd z d) t)
      (pullback.snd z (t ≫ d)) (pullback.snd z d) t := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    (pullbackLeftPullbackSndIso z d t).symm rfl ?_
  · simp [Category.assoc]
  · exact pullbackLeftPullbackSndIso_inv_snd_snd z d t

set_option backward.isDefEq.respectTransparency false in

private theorem restricted_composite_base_change
    {S T : Scheme.{u}} (d : T ⟶ S)
    (X₀ Y₀ : Over S) (f₀ : X₀ ⟶ Y₀)
    (V : Y₀.left.Opens) (W : S.Opens)
    (q : ((pullback.fst Y₀.hom d) ⁻¹ᵁ V).toScheme ⟶ (d ⁻¹ᵁ W).toScheme)
    (hq : q ≫ (d ⁻¹ᵁ W).ι =
      ((pullback.fst Y₀.hom d) ⁻¹ᵁ V).ι ≫ pullback.snd Y₀.hom d)
    (L : Scheme.{u}) (t : L ⟶ T) :
    let g := (((Over.pullback d).map f₀).left) ∣_
      ((pullback.fst Y₀.hom d) ⁻¹ᵁ V)
    let s := t.resLE (d ⁻¹ᵁ W) _ le_rfl
    Nonempty
      (Arrow.mk ((((Over.pullback (t ≫ d)).map f₀).left) ∣_
        ((pullback.fst Y₀.hom (t ≫ d)) ⁻¹ᵁ V)) ≅
      Arrow.mk (pullback.map (g ≫ q) s q s g (𝟙 _) (𝟙 _)
        (by simp) (by simp))) := by
  dsimp only
  let fT := ((Over.pullback d).map f₀).left
  let fL := ((Over.pullback (t ≫ d)).map f₀).left
  let VB := (pullback.fst Y₀.hom d) ⁻¹ᵁ V
  let UC := fT ⁻¹ᵁ VB
  let VL := (pullback.fst Y₀.hom (t ≫ d)) ⁻¹ᵁ V
  let UL := fL ⁻¹ᵁ VL
  let WT := d ⁻¹ᵁ W
  let WL := t ⁻¹ᵁ WT
  let nY := (pullbackLeftPullbackSndIso Y₀.hom d t).inv ≫
    pullback.fst (pullback.snd Y₀.hom d) t
  let nX := (pullbackLeftPullbackSndIso X₀.hom d t).inv ≫
    pullback.fst (pullback.snd X₀.hom d) t
  have hnY₁ : nY ≫ pullback.fst Y₀.hom d =
      pullback.fst Y₀.hom (t ≫ d) := by simp [nY]
  have hnY₂ : nY ≫ pullback.snd Y₀.hom d =
      pullback.snd Y₀.hom (t ≫ d) ≫ t := by simp [nY]
  have hnX₁ : nX ≫ pullback.fst X₀.hom d =
      pullback.fst X₀.hom (t ≫ d) := by simp [nX]
  have hnX₂ : nX ≫ pullback.snd X₀.hom d =
      pullback.snd X₀.hom (t ≫ d) ≫ t := by simp [nX]
  have hfT₁ : fT ≫ pullback.fst Y₀.hom d =
      pullback.fst X₀.hom d ≫ f₀.left := by simp [fT, Over.pullback_map_left]
  have hfT₂ : fT ≫ pullback.snd Y₀.hom d =
      pullback.snd X₀.hom d := by simp [fT, Over.pullback_map_left]
  have hfL₁ : fL ≫ pullback.fst Y₀.hom (t ≫ d) =
      pullback.fst X₀.hom (t ≫ d) ≫ f₀.left := by simp [fL, Over.pullback_map_left]
  have hfL₂ : fL ≫ pullback.snd Y₀.hom (t ≫ d) =
      pullback.snd X₀.hom (t ≫ d) := by simp [fL, Over.pullback_map_left]
  have hn : nX ≫ fT = fL ≫ nY := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hfT₁, hnY₁, reassoc_of% hnX₁, hfL₁]
    · simp only [Category.assoc, hfT₂, hnY₂,
        reassoc_of% hfL₂]
      exact hnX₂
  have eVB : VB ≤ (pullback.snd Y₀.hom d) ⁻¹ᵁ WT := by
    intro x hx
    have hh := congrArg (fun k ↦ k ⟨x, hx⟩) hq
    change (q ⟨x, hx⟩).val = pullback.snd Y₀.hom d x at hh
    change pullback.snd Y₀.hom d x ∈ WT
    rw [← hh]
    exact (q ⟨x, hx⟩).property
  have eUC : UC ≤ (pullback.snd X₀.hom d) ⁻¹ᵁ WT := by
    rw [← hfT₂, Scheme.Hom.comp_preimage]
    exact fT.preimage_mono eVB
  have hVL : VL = nY ⁻¹ᵁ VB := by
    dsimp [VL, VB]
    rw [← Scheme.Hom.comp_preimage, hnY₁]
  have hUL : UL = nX ⁻¹ᵁ UC := by
    change fL ⁻¹ᵁ VL = nX ⁻¹ᵁ (fT ⁻¹ᵁ VB)
    rw [hVL]
    exact (congrArg (fun k ↦ k ⁻¹ᵁ VB) hn).symm
  have eVL : VL ≤ (pullback.snd Y₀.hom (t ≫ d)) ⁻¹ᵁ WL := by
    rw [hVL]
    change nY ⁻¹ᵁ VB ≤ (pullback.snd Y₀.hom (t ≫ d)) ⁻¹ᵁ (t ⁻¹ᵁ WT)
    have hh := congrArg (fun k ↦ k ⁻¹ᵁ WT) hnY₂
    have hh' : nY ⁻¹ᵁ ((pullback.snd Y₀.hom d) ⁻¹ᵁ WT) =
        (pullback.snd Y₀.hom (t ≫ d)) ⁻¹ᵁ (t ⁻¹ᵁ WT) := by
      simpa only [Scheme.Hom.comp_preimage] using hh
    exact (nY.preimage_mono eVB).trans_eq hh'
  have eUL : UL ≤ (pullback.snd X₀.hom (t ≫ d)) ⁻¹ᵁ WL := by
    rw [hUL]
    change nX ⁻¹ᵁ UC ≤ (pullback.snd X₀.hom (t ≫ d)) ⁻¹ᵁ (t ⁻¹ᵁ WT)
    have hh := congrArg (fun k ↦ k ⁻¹ᵁ WT) hnX₂
    have hh' : nX ⁻¹ᵁ ((pullback.snd X₀.hom d) ⁻¹ᵁ WT) =
        (pullback.snd X₀.hom (t ≫ d)) ⁻¹ᵁ (t ⁻¹ᵁ WT) := by
      simpa only [Scheme.Hom.comp_preimage] using hh
    exact (nX.preimage_mono eUC).trans_eq hh'
  have hq' : (pullback.snd Y₀.hom d).resLE WT VB eVB = q := by
    rw [← cancel_mono WT.ι]
    exact (Scheme.Hom.resLE_comp_ι _ _).trans hq.symm
  have hqc : (pullback.snd X₀.hom d).resLE WT UC eUC = (fT ∣_ VB) ≫ q := by
    rw [← cancel_mono WT.ι]
    simp only [Scheme.Hom.resLE_comp_ι, Category.assoc]
    rw [show q ≫ WT.ι = VB.ι ≫ pullback.snd Y₀.hom d from hq,
      morphismRestrict_ι_assoc, hfT₂]
  have hB := Scheme.Hom.isPullback_resLE
    (composite_pullback_square Y₀.hom d t) (le_rfl : WL ≤ t ⁻¹ᵁ WT) eVB
    (UY := VL) (by rw [← hVL, inf_eq_left.mpr eVL])
  have hC := Scheme.Hom.isPullback_resLE
    (composite_pullback_square X₀.hom d t) (le_rfl : WL ≤ t ⁻¹ᵁ WT) eUC
    (UY := UL) (by rw [← hUL, inf_eq_left.mpr eUL])
  rw [hq'] at hB
  rw [hqc] at hC
  have hRT : (fT ∣_ VB) ≫ VB.ι = UC.ι ≫ fT := morphismRestrict_ι fT VB
  have hRL : (fL ∣_ VL) ≫ VL.ι = UL.ι ≫ fL := morphismRestrict_ι fL VL
  refine ⟨Arrow.isoMk hC.isoPullback hB.isoPullback ?_⟩
  dsimp only [Arrow.mk_hom]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    rw [reassoc_of% hC.isoPullback_hom_fst, hB.isoPullback_hom_fst]
    rw [← cancel_mono VB.ι]
    simp only [Category.assoc]
    rw [hRT, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc,
      reassoc_of% hRL]
    simpa only [nX, nY, Category.assoc] using congrArg (fun k ↦ UL.ι ≫ k) hn
  · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [hC.isoPullback_hom_snd, hB.isoPullback_hom_snd]
    rw [← cancel_mono WL.ι]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
    rw [reassoc_of% hRL, hfL₂]

open scoped TensorProduct in
private theorem tensor_pullback_arrow
    {H P Q M : Scheme.{u}} (g : P ⟶ Q) (q : Q ⟶ H) (s : M ⟶ H)
    (R A B C : CommRingCat.{u}) [Algebra R A] [Algebra R B] [Algebra R C]
    (φ : B →ₐ[R] C) (e0 : H ≅ Spec R) (eB : Q ≅ Spec B)
    (eC : P ≅ Spec C) (eA : M ≅ Spec A)
    (hB : q ≫ e0.hom = eB.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (hC : g ≫ eB.hom = eC.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (hA : s ≫ e0.hom = eA.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Nonempty (Arrow.mk (pullback.map (g ≫ q) s q s g (𝟙 _) (𝟙 _)
      (by simp) (by simp)) ≅ Arrow.mk (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R A) φ).toRingHom))) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let c := Spec.map (CommRingCat.ofHom (algebraMap R C))
  let a := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have hc : (g ≫ q) ≫ e0.hom = eC.hom ≫ c := by
    rw [Category.assoc, hB, ← Category.assoc, hC, Category.assoc]
    dsimp [c]
    rw [← Spec.map_comp]
    congr 1
    exact congrArg (fun k : R →+* C ↦ Spec.map (CommRingCat.ofHom k)) φ.comp_algebraMap
  have hB' : b ≫ e0.inv = eB.inv ≫ q := by
    simpa [Category.assoc, b] using
      congrArg (fun k ↦ eB.inv ≫ k ≫ e0.inv) hB.symm
  have hC' : c ≫ e0.inv = eC.inv ≫ (g ≫ q) := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ eC.inv ≫ k ≫ e0.inv) hc.symm
  have hA' : a ≫ e0.inv = eA.inv ≫ s := by
    simpa [Category.assoc, a] using
      congrArg (fun k ↦ eA.inv ≫ k ≫ e0.inv) hA.symm
  let jB : pullback q s ≅ pullback b a :=
    { hom := pullback.map q s b a eB.hom eA.hom e0.hom hB hA
      inv := pullback.map b a q s eB.inv eA.inv e0.inv hB' hA'
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp }
  let jC : pullback (g ≫ q) s ≅ pullback c a :=
    { hom := pullback.map (g ≫ q) s c a eC.hom eA.hom e0.hom hc hA
      inv := pullback.map c a (g ≫ q) s eC.inv eA.inv e0.inv hC' hA'
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp }
  let iB := jB ≪≫ pullbackSymmetry b a ≪≫ pullbackSpecIso R A B
  let iC := jC ≪≫ pullbackSymmetry c a ≪≫ pullbackSpecIso R A C
  have hb₁ : iB.inv ≫ pullback.fst q s =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) ≫
        eB.inv := by
    dsimp [iB]
    simp only [Category.assoc]
    rw [← cancel_mono eB.hom]
    simp [jB, a, b, Category.assoc]
  have hb₂ : iB.inv ≫ pullback.snd q s =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)) ≫
        eA.inv := by
    dsimp [iB]
    simp only [Category.assoc]
    rw [← cancel_mono eA.hom]
    simp [jB, a, b, Category.assoc]
  have hc₁ : iC.inv ≫ pullback.fst (g ≫ q) s =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toRingHom) ≫
        eC.inv := by
    dsimp [iC]
    simp only [Category.assoc]
    rw [← cancel_mono eC.hom]
    simp [jC, a, c, Category.assoc]
  have hc₂ : iC.inv ≫ pullback.snd (g ≫ q) s =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] C)) ≫
        eA.inv := by
    dsimp [iC]
    simp only [Category.assoc]
    rw [← cancel_mono eA.hom]
    simp [jC, a, c, Category.assoc]
  let ψ := Algebra.TensorProduct.map (AlgHom.id R A) φ
  let sψ := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have hRight : sψ ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toRingHom) ≫
        Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    dsimp [sψ]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have hLeft : sψ ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] C)) := by
    dsimp [sψ]
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp [ψ]
  have hh : sψ ≫ iB.inv = iC.inv ≫
      pullback.map (g ≫ q) s q s g (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [hb₁, reassoc_of% hRight, reassoc_of% hc₁]
      rw [← cancel_mono eB.hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hC, Iso.inv_hom_id_assoc]
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
      rw [hb₂, ← Category.assoc, hLeft, hc₂]
  refine ⟨Arrow.isoMk' _ sψ iC iB ?_⟩
  rw [← cancel_epi iC.inv, ← cancel_mono iB.inv]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using hh

set_option linter.unusedVariables false in

private theorem affine_base_piece_tensor_base_change
    {S T : Scheme.{u}} (d : T ⟶ S)
    (X₀ Y₀ : Over S) (f₀ : X₀ ⟶ Y₀)
    (V : Y₀.left.Opens) (W : S.Opens)
    (R B C : CommRingCat.{u}) (aB : R →+* B) (aC : R →+* C)
    (e0 : (d ⁻¹ᵁ W).toScheme ≅ Spec R)
    (q : ((pullback.fst Y₀.hom d) ⁻¹ᵁ V).toScheme ⟶ (d ⁻¹ᵁ W).toScheme)
    (hq : q ≫ (d ⁻¹ᵁ W).ι =
      ((pullback.fst Y₀.hom d) ⁻¹ᵁ V).ι ≫ pullback.snd Y₀.hom d)
    (eB : ((pullback.fst Y₀.hom d) ⁻¹ᵁ V).toScheme ≅ Spec B)
    (eC : ((((Over.pullback d).map f₀).left) ⁻¹ᵁ
      ((pullback.fst Y₀.hom d) ⁻¹ᵁ V)).toScheme ≅ Spec C)
    : letI : Algebra R B := aB.toAlgebra
      letI : Algebra R C := aC.toAlgebra
      ∀ (φ : B →ₐ[R] C),
        eB.hom ≫ Spec.map (CommRingCat.ofHom aB) = q ≫ e0.hom →
        eC.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
          ((((Over.pullback d).map f₀).left) ∣_
            ((pullback.fst Y₀.hom d) ⁻¹ᵁ V)) ≫ eB.hom →
        ∀ (L : Scheme.{u}) (t : L ⟶ T) (A : CommRingCat.{u})
          (aA : Algebra R A) (e : (t ⁻¹ᵁ (d ⁻¹ᵁ W)).toScheme ≅ Spec A),
          t.resLE (d ⁻¹ᵁ W) _ le_rfl ≫ e0.hom =
            e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) →
          Nonempty
            (Arrow.mk ((((Over.pullback (t ≫ d)).map f₀).left) ∣_
              ((pullback.fst Y₀.hom (t ≫ d)) ⁻¹ᵁ V)) ≅
              Arrow.mk (Spec.map (CommRingCat.ofHom
                (Algebra.TensorProduct.map (AlgHom.id R A) φ).toRingHom))) := by
  intro φ hB hC L t A aA e he
  let : Algebra R B := aB.toAlgebra
  let : Algebra R C := aC.toAlgebra
  let := aA
  obtain ⟨i⟩ := restricted_composite_base_change d X₀ Y₀ f₀ V W q hq L t
  obtain ⟨j⟩ := tensor_pullback_arrow
    ((((Over.pullback d).map f₀).left) ∣_ ((pullback.fst Y₀.hom d) ⁻¹ᵁ V))
    q (t.resLE (d ⁻¹ᵁ W) _ le_rfl) R A B C φ e0 eB eC e hB.symm hC.symm he
  exact ⟨i ≪≫ j⟩
end AlgebraicGeometry
end

section
universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem specModel {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (R : CommRingCat.{u}) (q : Y ⟶ Spec R) :
    ∃ (aB : R →+* Γ(Y, ⊤)) (aC : R →+* Γ(X, ⊤)),
      let : Algebra R Γ(Y, ⊤) := aB.toAlgebra
      let : Algebra R Γ(X, ⊤) := aC.toAlgebra
      ∃ φ : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤), φ.FiniteType ∧
        Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom aB) = q ∧
        X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
          f ≫ Y.isoSpec.hom := by
  let aB : R →+* Γ(Y, ⊤) := ((Scheme.ΓSpecIso R).inv ≫ q.appTop).hom
  let aC : R →+* Γ(X, ⊤) := f.appTop.hom.comp aB
  let : Algebra R Γ(Y, ⊤) := aB.toAlgebra
  let : Algebra R Γ(X, ⊤) := aC.toAlgebra
  let φ : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤) :=
    { f.appTop.hom with commutes' := fun _ ↦ rfl }
  refine ⟨aB, aC, φ, ?_, ?_, ?_⟩
  · change f.appTop.hom.FiniteType
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
      f.finiteType_appLE (isAffineOpen_top Y) (isAffineOpen_top X)
        (by simp)
  · change Y.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ q.appTop) = q
    rw [Spec.map_comp]
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp [Scheme.isoSpec]
  · exact Scheme.isoSpec_hom_naturality f

set_option backward.isDefEq.respectTransparency false in
private theorem stageLft {S T : Scheme.{u}} (d : T ⟶ S)
    (X₀ Y₀ : Over S) (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left] :
    LocallyOfFiniteType (((Over.pullback d).map f₀).left) := by
  have hp : IsPullback (pullback.fst X₀.hom d)
      (((Over.pullback d).map f₀).left) f₀.left (pullback.fst Y₀.hom d) := by
    have hs : IsPullback (pullback.fst X₀.hom d)
        ((((Over.pullback d).map f₀).left) ≫ pullback.snd Y₀.hom d)
        (f₀.left ≫ Y₀.hom) d := by
      simpa [Over.pullback_map_left, Over.w] using
        (IsPullback.of_hasPullback X₀.hom d)
    exact hs.of_bot (by simp [Over.pullback_map_left])
      (IsPullback.of_hasPullback Y₀.hom d)
  exact MorphismProperty.of_isPullback hp inferInstance

private theorem exists_affine_base_piece_tensor_comparison
    {S T : Scheme.{u}} (d : T ⟶ S) [IsAffineHom d]
    (X₀ Y₀ : Over S) (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left]
    (haffine : IsAffineHom (((Over.pullback d).map f₀).left))
    (V : Y₀.left.Opens) (hV : IsAffineOpen V)
    (W : S.Opens) (hVW : V ≤ Y₀.hom ⁻¹ᵁ W)
    (R : CommRingCat.{u}) (e0 : (d ⁻¹ᵁ W).toScheme ≅ Spec R) :
    ∃ (B C : CommRingCat.{u}) (aB : R →+* B) (aC : R →+* C),
      letI : Algebra R B := aB.toAlgebra
      letI : Algebra R C := aC.toAlgebra
      ∃ φ : B →ₐ[R] C, φ.FiniteType ∧
        ∀ (L : Scheme.{u}) (t : L ⟶ T) (A : CommRingCat.{u}) (aA : Algebra R A),
          letI := aA
          ∀ (e : (t ⁻¹ᵁ (d ⁻¹ᵁ W)).toScheme ≅ Spec A),
            t.resLE (d ⁻¹ᵁ W) _ le_rfl ≫ e0.hom =
              e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) →
            Nonempty
              (Arrow.mk ((((Over.pullback (t ≫ d)).map f₀).left) ∣_
                ((pullback.fst Y₀.hom (t ≫ d)) ⁻¹ᵁ V)) ≅
                Arrow.mk (Spec.map (CommRingCat.ofHom
                  (Algebra.TensorProduct.map (AlgHom.id R A) φ).toRingHom)))  := by
  let fT := ((Over.pullback d).map f₀).left
  let VT := (pullback.fst Y₀.hom d) ⁻¹ᵁ V
  let : IsAffineHom fT := haffine
  let : LocallyOfFiniteType fT := stageLft d X₀ Y₀ f₀
  let : IsAffineHom (pullback.fst Y₀.hom d) :=
    MorphismProperty.pullback_fst Y₀.hom d inferInstance
  have hVT : IsAffineOpen VT := hV.preimage (pullback.fst Y₀.hom d)
  have hUT : IsAffineOpen (fT ⁻¹ᵁ VT) := hVT.preimage fT
  let : IsAffine VT.toScheme := hVT
  let : IsAffine (fT ⁻¹ᵁ VT).toScheme := hUT
  have hVW' : VT ≤ (pullback.snd Y₀.hom d) ⁻¹ᵁ (d ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← pullback.condition, Scheme.Hom.comp_preimage]
    exact (pullback.fst Y₀.hom d).preimage_mono hVW
  let q := (pullback.snd Y₀.hom d).resLE (d ⁻¹ᵁ W) VT hVW'
  obtain ⟨aB, aC, φ, hφ, hB, hC⟩ := specModel (fT ∣_ VT) R (q ≫ e0.hom)
  let : Algebra R Γ(VT.toScheme, ⊤) := aB.toAlgebra
  let : Algebra R Γ((fT ⁻¹ᵁ VT).toScheme, ⊤) := aC.toAlgebra
  refine ⟨Γ(VT.toScheme, ⊤), Γ((fT ⁻¹ᵁ VT).toScheme, ⊤), aB, aC, φ, hφ, ?_⟩
  exact affine_base_piece_tensor_base_change d X₀ Y₀ f₀ V W R _ _ aB aC e0 q
    (Scheme.Hom.resLE_comp_ι _ _) VT.toScheme.isoSpec (fT ⁻¹ᵁ VT).toScheme.isoSpec
    φ hB hC

end AlgebraicGeometry
end

section
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Present an affine piece of a base-changed family by a finite type algebra map,
compatibly with its directed system and every later base change. -/
theorem exists_affine_base_piece_tensor_presentation
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ k : I) (hk : i₀ ≤ k)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [LocallyOfFiniteType f₀.left]
    (haffine : IsAffineHom (((Over.pullback (D.map (homOfLE hk).op)).map f₀).left))
    (V : Y₀.left.Opens) (hV : IsAffineOpen V)
    (W : (D.obj (op i₀)).Opens) (hW : IsAffineOpen W)
    (hVW : V ≤ Y₀.hom ⁻¹ᵁ W)
    : ∃ (F : {i : I // k ≤ i} ⥤ CommRingCat.{u})
      (B C : CommRingCat.{u})
      (aB : F.obj ⟨k, le_rfl⟩ →+* B) (aC : F.obj ⟨k, le_rfl⟩ →+* C),
      letI : Algebra (F.obj ⟨k, le_rfl⟩) B := aB.toAlgebra
      letI : Algebra (F.obj ⟨k, le_rfl⟩) C := aC.toAlgebra
      ∃ φ : B →ₐ[F.obj ⟨k, le_rfl⟩] C, φ.FiniteType ∧
        (letI : Algebra (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u}) :=
          (CommRingCat.Hom.hom (colimit.ι F ⟨k, le_rfl⟩)).toAlgebra
        Nonempty
          (Arrow.mk
            ((((Over.pullback (c.π.app (op i₀))).map f₀).left) ∣_
              ((pullback.fst Y₀.hom (c.π.app (op i₀))) ⁻¹ᵁ V)) ≅
            Arrow.mk (Spec.map (CommRingCat.ofHom
              (Algebra.TensorProduct.map
                (AlgHom.id (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u})) φ).toRingHom)))) ∧
        (∀ j : {i : I // k ≤ i},
          letI : Algebra (F.obj ⟨k, le_rfl⟩) (F.obj j) :=
            (CommRingCat.Hom.hom (F.map (homOfLE j.property))).toAlgebra
          Nonempty
            (Arrow.mk
              ((((Over.pullback (D.map (homOfLE (hk.trans j.property)).op)).map f₀).left)
                ∣_ ((pullback.fst Y₀.hom
                  (D.map (homOfLE (hk.trans j.property)).op)) ⁻¹ᵁ V)) ≅
              Arrow.mk (Spec.map (CommRingCat.ofHom
                (Algebra.TensorProduct.map
                  (AlgHom.id (F.obj ⟨k, le_rfl⟩) (F.obj j)) φ).toRingHom)))) := by
  let d := D.map (homOfLE hk).op
  have hWk : IsAffineOpen (d ⁻¹ᵁ W) := hW.preimage d
  obtain ⟨F, e0, hi, eL, hL⟩ :=
    exists_affineOpen_directedRingSystem D c hc k (d ⁻¹ᵁ W) hWk
  obtain ⟨B, C, aB, aC, φ, hφ, hcomp⟩ :=
    exists_affine_base_piece_tensor_comparison d X₀ Y₀ f₀ haffine V hV W hVW
      (F.obj ⟨k, le_rfl⟩) e0
  let := aB.toAlgebra
  let := aC.toAlgebra
  refine ⟨F, B, C, aB, aC, φ, hφ, ?_, ?_⟩
  · let aL : Algebra (F.obj ⟨k, le_rfl⟩) (colimit F : CommRingCat.{u}) :=
      (CommRingCat.Hom.hom (colimit.ι F ⟨k, le_rfl⟩)).toAlgebra
    have h := hcomp c.pt (c.π.app (op k)) (colimit F) aL eL hL
    have heq : c.π.app (op k) ≫ d = c.π.app (op i₀) :=
      c.w (homOfLE hk).op
    rw [heq] at h
    exact h
  · intro j
    let aj : Algebra (F.obj ⟨k, le_rfl⟩) (F.obj j) :=
      (CommRingCat.Hom.hom (F.map (homOfLE j.property))).toAlgebra
    obtain ⟨ej, hej⟩ := hi j
    have h := hcomp (D.obj (op j.val)) (D.map (homOfLE j.property).op)
      (F.obj j) aj ej hej
    have heq : D.map (homOfLE j.property).op ≫ d =
        D.map (homOfLE (hk.trans j.property)).op := by
      rw [← D.map_comp]
      congr 1
    rw [heq] at h
    exact h

end AlgebraicGeometry
end
