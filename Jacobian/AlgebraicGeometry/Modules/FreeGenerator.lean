import Jacobian.AlgebraicGeometry.Modules.GlobalSection
import Jacobian.AlgebraicGeometry.Modules.Invertible
import Jacobian.CategoryTheory.Sites.LocalIsomorphism

/-!
# Free generators of module sheaves

A section is a free generator when multiplication by it is bijective on every smaller open.
Free generators have unique coefficients and identify the restricted module with the unit.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- Restricting a function twice is restricting it along the composite. -/
lemma presheaf_map_map_apply {U V W : X.Opens} (f : V ⟶ U) (g : W ⟶ V) (a : Γ(X, U)) :
    X.presheaf.map g.op (X.presheaf.map f.op a) = X.presheaf.map (g ≫ f).op a := by
  rw [op_comp, Functor.map_comp]
  rfl

/-- Restricting a function along an endomorphism of an open does nothing. -/
lemma presheaf_map_id_apply {U : X.Opens} (f : U ⟶ U) (a : Γ(X, U)) :
    X.presheaf.map f.op a = a := by
  rw [Subsingleton.elim f (𝟙 U), op_id, CategoryTheory.Functor.map_id]
  rfl

namespace Modules

variable {M N : X.Modules}

/-- A section `e` of `M` over `U` is a *free generator* of `M` on `U` if every section of `M`
over an open `V ⊆ U` is uniquely of the form `r • e|_V` with `r ∈ Γ(X, V)`; i.e. `e`
trivializes `M|_U ≅ 𝒪_U`. -/
def IsFreeGenerator {U : X.Opens} (e : Γ(M, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U),
    Function.Bijective fun r : Γ(X, V) ↦ r • M.presheaf.map (homOfLE h).op e

namespace IsFreeGenerator

variable {U : X.Opens} {e : Γ(M, U)}

/-- The restriction of a free generator to a smaller open is a free generator. -/
lemma map {V : X.Opens} (he : IsFreeGenerator e) (h : V ≤ U) :
    IsFreeGenerator (M.presheaf.map (homOfLE h).op e) := by
  intro W hW
  simp_rw [presheaf_map_map_apply]
  exact he W (hW.trans h)

/-- A free generator `e` on `U` gives a bijection `r ↦ r • e` from `Γ(X, U)` to `Γ(M, U)`. -/
lemma bijective (he : IsFreeGenerator e) : Function.Bijective fun r : Γ(X, U) ↦ r • e := by
  simpa only [presheaf_map_id_apply] using he U le_rfl

/-- A free generator `e` on `U` gives an injection `r ↦ r • e` of `Γ(X, U)` into `Γ(M, U)`. -/
lemma smul_left_injective (he : IsFreeGenerator e) :
    Function.Injective fun r : Γ(X, U) ↦ r • e :=
  he.bijective.1

/-- Every section over `U` is a multiple of a free generator on `U`. -/
lemma exists_smul_eq (he : IsFreeGenerator e) (m : Γ(M, U)) : ∃ r : Γ(X, U), r • e = m :=
  he.bijective.2 m

/-- Two free generators on the same open differ by a unit. -/
lemma exists_unit_smul_eq {e' : Γ(M, U)} (he : IsFreeGenerator e) (he' : IsFreeGenerator e') :
    ∃ u : Γ(X, U)ˣ, e' = u.1 • e := by
  obtain ⟨u, hu⟩ := he.exists_smul_eq e'
  obtain ⟨v, hv⟩ := he'.exists_smul_eq e
  have huv : v * u = 1 := he.smul_left_injective (by simp only [mul_smul, hu, hv, one_smul])
  exact ⟨⟨u, v, by rw [mul_comm, huv], huv⟩, hu.symm⟩

/-- A unit multiple of a free generator is a free generator. -/
lemma units_smul (he : IsFreeGenerator e) (g : Γ(X, U)ˣ) :
    IsFreeGenerator ((g : Γ(X, U)) • e) := by
  intro V h
  have : (fun a : Γ(X, V) ↦ a • M.presheaf.map (homOfLE h).op ((g : Γ(X, U)) • e)) =
      (fun a : Γ(X, V) ↦ a • M.presheaf.map (homOfLE h).op e) ∘
        (fun a ↦ a * X.presheaf.map (homOfLE h).op (g : Γ(X, U))) := by
    ext a
    simp [mul_smul]
  rw [this]
  exact (he V h).comp
    (Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom g).mulRight_bijective

/-- The coefficient of a section `m` with respect to a free generator `e`: the unique `a` with
`a • e = m`. -/
noncomputable def coeff (he : IsFreeGenerator e) (m : Γ(M, U)) : Γ(X, U) :=
  Function.surjInv he.bijective.2 m

variable (he : IsFreeGenerator e)
include he

@[simp]
lemma coeff_smul (m : Γ(M, U)) : he.coeff m • e = m :=
  Function.surjInv_eq he.bijective.2 m

lemma coeff_eq_iff (m : Γ(M, U)) (a : Γ(X, U)) : he.coeff m = a ↔ a • e = m :=
  ⟨fun h ↦ h ▸ he.coeff_smul m, fun h ↦ he.bijective.1 ((he.coeff_smul m).trans h.symm)⟩

@[simp]
lemma coeff_smul_self (a : Γ(X, U)) : he.coeff (a • e) = a :=
  (he.coeff_eq_iff _ _).2 rfl

@[simp]
lemma coeff_add (m m' : Γ(M, U)) : he.coeff (m + m') = he.coeff m + he.coeff m' := by
  rw [coeff_eq_iff, add_smul, coeff_smul, coeff_smul]

@[simp]
lemma coeff_zero : he.coeff 0 = 0 := by
  rw [coeff_eq_iff, zero_smul]

@[simp]
lemma coeff_smul_left (a : Γ(X, U)) (m : Γ(M, U)) : he.coeff (a • m) = a * he.coeff m := by
  rw [coeff_eq_iff, mul_smul, coeff_smul]

lemma coeff_map {V : X.Opens} (h : V ≤ U) (m : Γ(M, U)) :
    (he.map h).coeff (M.presheaf.map (homOfLE h).op m) =
      X.presheaf.map (homOfLE h).op (he.coeff m) := by
  rw [coeff_eq_iff, ← map_smul, coeff_smul]

end IsFreeGenerator

/-- If `M` is trivial on `U`, i.e. `M.over U ≅ 𝒪_U`, then `M` has a free generator on `U`,
namely the section corresponding to `1`. -/
lemma exists_isFreeGenerator_of_iso {U : X.Opens}
    (i : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ∃ e : Γ(M, U), IsFreeGenerator e := by
  let s := (M.over U).unitHomEquiv i.inv
  refine ⟨s.val (.op (Over.mk (𝟙 U))), fun V h ↦ ?_⟩
  let ψ := (i.inv.val.app (.op (Over.mk (homOfLE h)))).hom
  let ψ' : Γ(X, V) → Γ(M, V) := fun r ↦ ψ r
  have h1 (r : Γ(X, V)) : ψ' r = r • ψ' 1 :=
    (congrArg ψ (mul_one r).symm).trans (ψ.map_smul r (1 : Γ(X, V)))
  have h2 : M.presheaf.map (homOfLE h).op (s.val (.op (Over.mk (𝟙 U)))) = ψ' 1 :=
    s.2 (Over.homMk (homOfLE h) : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U)).op
  have key : (fun r : Γ(X, V) ↦ r • M.presheaf.map (homOfLE h).op
      (s.val (.op (Over.mk (𝟙 U))))) = ψ' := by
    ext r
    rw [h1, h2]
  rw [key]
  exact ConcreteCategory.bijective_of_isIso ((PresheafOfModules.evaluation _
    (.op (Over.mk (homOfLE h)))).mapIso ((SheafOfModules.forget _).mapIso i)).inv

/-- **Invertible modules are locally trivial.** Every point `x` of an open `W` has an affine
open neighbourhood `U ⊆ W` on which an invertible module has a free generator. -/
lemma exists_isFreeGenerator (M : X.Modules)
    [M.IsInvertible] {x : X}
    {W : X.Opens} (hx : x ∈ W) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧ ∃ e : Γ(M, U.1), IsFreeGenerator e := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := exists_mem_over_iso_unit M x
  obtain ⟨s, hs⟩ := exists_isFreeGenerator_of_iso e
  obtain ⟨V, hV, hxV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := U ⊓ W) ⟨hxU, hx⟩
  exact ⟨⟨V, hV⟩, hxV, fun y hy ↦ (hVU hy).2, _,
    hs.map (fun y hy ↦ (hVU hy).1)⟩

/-- An isomorphism of modules carries free generators to free generators. -/
lemma IsFreeGenerator.app_hom {M' : X.Modules} (e : M ≅ M') {U : X.Opens} {x : Γ(M, U)}
    (hx : IsFreeGenerator x) : IsFreeGenerator (e.hom.app U x) := by
  intro V h
  have he : Function.Bijective (e.hom.app V) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨e.inv.app V, fun y ↦ ?_, fun y ↦ ?_⟩
    · change (e.hom.app V ≫ e.inv.app V) y = y
      rw [← Hom.comp_app, e.hom_inv_id, Hom.id_app]
      rfl
    · change (e.inv.app V ≫ e.hom.app V) y = y
      rw [← Hom.comp_app, e.inv_hom_id, Hom.id_app]
      rfl
  convert he.comp (hx V h) using 1
  ext r
  simp only [Function.comp_apply, Hom.app_smul, Hom.app_presheaf_map]

/-- A free generator `e` of `M` over `U` trivializes `M` over `U`: `a ↦ a • e` is an isomorphism
`𝒪_U ≅ M|_U`. -/
noncomputable def IsFreeGenerator.overIso {U : X.Opens} {e : Γ(M, U)} (he : IsFreeGenerator e) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  let σ : (M.over U).sections := PresheafOfModules.sectionsMk
    (fun W ↦ show Γ(M, W.unop.left) from M.presheaf.map W.unop.hom.op e)
    (fun W W' f ↦ by
      change M.presheaf.map f.unop.left.op (M.presheaf.map W.unop.hom.op e) = _
      rw [presheaf_map_map_apply]
      rfl)
  let φ := (M.over U).unitHomEquiv.symm σ
  have : IsIso φ := by
    have : IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map φ) := by
      refine (NatTrans.isIso_iff_isIso_app _).2 fun W ↦ ?_
      rw [ConcreteCategory.isIso_iff_bijective]
      exact he _ (leOfHom W.unop.hom)
    exact isIso_of_reflects_iso φ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)
  (asIso φ).symm

/-- The image of a free generator under a morphism which is bijective on all sections over
opens `V ⊆ U` is a free generator. -/
lemma IsFreeGenerator.app_of_bijective (φ : M ⟶ N) {U : X.Opens} {e : Γ(M, U)}
    (he : IsFreeGenerator e) (hφ : ∀ V ≤ U, Function.Bijective (φ.app V)) :
    IsFreeGenerator (φ.app U e) := by
  intro V h
  have : (fun r : Γ(X, V) ↦ r • N.presheaf.map (homOfLE h).op (φ.app U e)) =
      φ.app V ∘ fun r : Γ(X, V) ↦ r • M.presheaf.map (homOfLE h).op e := by
    funext r
    simp [Hom.app_smul, Hom.app_presheaf_map]
  rw [this]
  exact (hφ V h).comp (he V h)

/-- The section `1` is a free generator of the structure sheaf on every open. -/
lemma isFreeGenerator_one (U : X.Opens) :
    IsFreeGenerator (M := unit X) (U := U) (1 : Γ(X, U)) := by
  intro V h
  have key (r : Γ(X, V)) : r • (unit X).presheaf.map
      (homOfLE h).op (1 : Γ(X, U)) = r :=
    (congrArg (r * ·) (map_one (X.presheaf.map (homOfLE h).op).hom)).trans (mul_one r)
  refine ⟨fun a b hab ↦ ?_, fun b ↦ ⟨b, key b⟩⟩
  exact (key a).symm.trans (hab.trans (key b))

end Modules

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable {X : Scheme.{u}}
lemma Modules.isIso_of_isFreeGenerator {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ (U : X.Opens) (e : Γ(M, U)), x ∈ U ∧ Modules.IsFreeGenerator e ∧
      Modules.IsFreeGenerator (φ.app U e)) : IsIso φ := by
  choose U e hxU he hφe using h
  have hbij (x : X) (W : X.Opens) (hW : W ≤ U x) : Function.Bijective (φ.app W) := by
    refine (Function.Bijective.of_comp_iff _ (he x W hW)).1 ?_
    convert hφe x W hW using 1
    ext r
    simp only [Function.comp_apply, Modules.Hom.app_smul, Modules.Hom.app_presheaf_map]
  have : IsIso ((Modules.toPresheaf X).map φ) := by
    refine Presheaf.isIso_of_isIso_app_of_mem (_root_.Opens.grothendieckTopology X) M.isSheaf N.isSheaf
      _ fun W ↦ ⟨⟨fun V _ ↦ ∃ x, V ≤ U x, fun ⟨x, hx⟩ f ↦ ⟨x, f.le.trans hx⟩⟩,
        fun x hx ↦ ⟨W ⊓ U x, homOfLE inf_le_left, ⟨x, inf_le_right⟩, hx, hxU x⟩,
        fun V _ ⟨x, hx⟩ ↦ ?_⟩
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hbij x V hx
  exact isIso_of_reflects_iso φ (Modules.toPresheaf X)

end AlgebraicGeometry.Scheme
