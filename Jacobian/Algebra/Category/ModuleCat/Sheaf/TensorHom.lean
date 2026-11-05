import Jacobian.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Jacobian.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Jacobian.Algebra.Category.ModuleCat.Presheaf.TensorHom
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Tensor and internal hom on finite free charts

A finite basis of a module sheaf gives an inverse to the canonical
tensor–internal-Hom comparison on every smaller chart.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory Limits Opposite

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] {R : Sheaf J CommRingCat.{u}}
set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R

section Monoidal

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

attribute [local instance] monoidalCategory symmetricCategory

/-- The tensor-sheafification comparison is natural in its first argument. -/
lemma whiskerRight_tensorObjIsoSheafification_hom {M M' : SheafOfModules.{u} 𝓡} (f : M ⟶ M')
    (P : SheafOfModules.{u} 𝓡) :
    f ▷ P ≫ (SheafOfModules.tensorObjIsoSheafification (R := R) M' P).hom =
      (SheafOfModules.tensorObjIsoSheafification (R := R) M P).hom ≫
        (PresheafOfModules.sheafification (𝟙 (𝓡).obj)).map (f.val ▷ P.val) := by
  letI := SheafOfModules.sheafificationMonoidal R
  simp only [SheafOfModules.tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_hom, Category.assoc]
  erw [← Functor.LaxMonoidal.μ_natural_left]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  simp only [tensorIso_inv, Iso.app_inv, asIso_inv]
  rw [← tensorHom_id (C := SheafOfModules.{u} 𝓡), ← tensorHom_id (C := SheafOfModules.{u} 𝓡),
    tensorHom_comp_tensorHom (C := SheafOfModules.{u} 𝓡), tensorHom_comp_tensorHom (C := SheafOfModules.{u} 𝓡)]
  erw [Category.id_comp]
  congr 1
  exact (inv (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡).obj)).counit).naturality
    f

/-- The tensor-sheafification comparison is natural in its second argument. -/
lemma whiskerLeft_tensorObjIsoSheafification_hom (M : SheafOfModules.{u} 𝓡)
    {N N' : SheafOfModules.{u} 𝓡} (f : N ⟶ N') :
    M ◁ f ≫ (SheafOfModules.tensorObjIsoSheafification (R := R) M N').hom =
      (SheafOfModules.tensorObjIsoSheafification (R := R) M N).hom ≫
        (PresheafOfModules.sheafification (𝟙 (𝓡).obj)).map (M.val ◁ f.val) := by
  letI := SheafOfModules.sheafificationMonoidal R
  simp only [SheafOfModules.tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_hom, Category.assoc]
  erw [← Functor.LaxMonoidal.μ_natural_right]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  simp only [tensorIso_inv, Iso.app_inv, asIso_inv]
  rw [← id_tensorHom (C := SheafOfModules.{u} 𝓡), ← id_tensorHom (C := SheafOfModules.{u} 𝓡),
    tensorHom_comp_tensorHom (C := SheafOfModules.{u} 𝓡), tensorHom_comp_tensorHom (C := SheafOfModules.{u} 𝓡)]
  erw [Category.id_comp]
  congr 1
  exact (inv (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡).obj)).counit).naturality f

end Monoidal

section

variable {U : C}
/-- A morphism `M|_U ⟶ N|_U` of sheaves of modules over `Over U`, as a morphism between the
restrictions to `Over U` of the underlying presheaves of modules. -/
private noncomputable def toRestrictOverHom {M N : SheafOfModules.{u} 𝓡} (f : M.over U ⟶ N.over U) :
    (PresheafOfModules.restrictOver R.obj U).obj M.val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj N.val where
  app W := f.val.app W
  naturality _ := f.val.naturality _

private lemma toRestrictOverHom_app {M N : SheafOfModules.{u} 𝓡} (f : M.over U ⟶ N.over U) (W) (x) :
    (toRestrictOverHom f).app W x = f.val.app W x := rfl

private lemma toRestrictOverHom_comp {M N P : SheafOfModules.{u} 𝓡} (f : M.over U ⟶ N.over U)
    (g : N.over U ⟶ P.over U) :
    toRestrictOverHom (f ≫ g) = toRestrictOverHom f ≫ toRestrictOverHom g := rfl

private lemma toRestrictOverHom_id (M : SheafOfModules.{u} 𝓡) :
    toRestrictOverHom (𝟙 (M.over U)) = 𝟙 _ := rfl

private lemma toRestrictOverHom_zero (M N : SheafOfModules.{u} 𝓡) :
    toRestrictOverHom (0 : M.over U ⟶ N.over U) = 0 := rfl

private lemma toRestrictOverHom_add {M N : SheafOfModules.{u} 𝓡} (f g : M.over U ⟶ N.over U) :
    toRestrictOverHom (f + g) = toRestrictOverHom f + toRestrictOverHom g := rfl

private lemma toRestrictOverHom_sum {M N : SheafOfModules.{u} 𝓡} {ι : Type*} (t : Finset ι)
    (f : ι → (M.over U ⟶ N.over U)) :
    toRestrictOverHom (∑ i ∈ t, f i) = ∑ i ∈ t, toRestrictOverHom (f i) :=
  map_sum (AddMonoidHom.mk' toRestrictOverHom toRestrictOverHom_add :
      (M.over U ⟶ N.over U) →+ ((PresheafOfModules.restrictOver R.obj U).obj M.val ⟶
        (PresheafOfModules.restrictOver R.obj U).obj N.val)) f t

end

variable {U : C} in
/-- If `M` is free of finite rank on `U`, then `Hom(M, R) ⊗ N ⟶ Hom(M, N)` is bijective on
sections over every `V ⟶ U`. -/
lemma dualTensorHom_app_bijective_of_iso_free [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] (M N : SheafOfModules.{u} 𝓡)
    {I : Type u} [Finite I] (e : free I ≅ M.over U) {V : C} (g : V ⟶ U) :
    Function.Bijective ((PresheafOfModules.dualTensorHom M.val N.val).app (op V)) := by
  classical
  let := Fintype.ofFinite I
  let S (j : I) : (unit 𝓡).over U ⟶ M.over U := Sigma.ι (fun _ ↦ unit _) j ≫ e.hom
  let Cc (j : I) : M.over U ⟶ (unit 𝓡).over U :=
    e.inv ≫ Sigma.desc (fun k ↦ if k = j then 𝟙 (unit _) else 0)
  have hsc (i j : I) : S j ≫ Cc i = if j = i then 𝟙 _ else 0 := by
    simp only [S, Cc, Category.assoc, Iso.hom_inv_id_assoc, Sigma.ι_desc]
    rfl
  have hsum : ∑ i, Sigma.desc (fun k ↦ if k = i then 𝟙 (unit _) else 0) ≫
      Sigma.ι (fun _ : I ↦ unit ((𝓡).over U)) i = 𝟙 (free I) := by
    refine Sigma.hom_ext _ _ fun k ↦ ?_
    rw [Preadditive.comp_sum, Finset.sum_eq_single k (fun b _ hb ↦ by simp [Ne.symm hb])
      (by simp)]
    simp only [Sigma.ι_desc_assoc]
    exact (Category.comp_id _).symm
  have htot : ∑ i, Cc i ≫ S i = 𝟙 _ := by
    calc ∑ i, Cc i ≫ S i = e.inv ≫ (∑ i, Sigma.desc (fun k ↦ if k = i then 𝟙 (unit _) else 0) ≫
          Sigma.ι (fun _ : I ↦ unit ((𝓡).over U)) i) ≫ e.hom := by
          simp only [Cc, S, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
          rfl
      _ = 𝟙 _ := by rw [hsum, Category.id_comp, Iso.inv_hom_id]
  refine PresheafOfModules.dualTensorHom_app_bijective_of_hom (P := N.val) (U := U)
    (fun j ↦ toRestrictOverHom (S j)) (fun j ↦ toRestrictOverHom (Cc j)) (fun i j ↦ ?_) ?_ g
  · refine (congrArg toRestrictOverHom (hsc i j)).trans ?_
    split_ifs
    · exact toRestrictOverHom_id _
    · exact toRestrictOverHom_zero _ _
  · exact (toRestrictOverHom_sum Finset.univ (fun i ↦ Cc i ≫ S i)).symm.trans
      ((congrArg toRestrictOverHom htot).trans (toRestrictOverHom_id M))

end SheafOfModules
