import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Jacobian.AlgebraicGeometry.Differentials.Presheaf
import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Gluing
import Jacobian.AlgebraicGeometry.Modules.Sections
import Jacobian.RingTheory.Derivation.Localization

/-!
# Derivations of the structure sheaf over an open

For an open `U` of a scheme `X` and an `𝒪_X`-module `M`, a *local derivation* of `𝒪_X` into
`M` over `U` is a family of additive maps `Γ(X, W) → Γ(M, W)`, for the opens `W ⊆ U`, satisfying
the Leibniz rule and compatible with restriction.

Derivations are local: a family of derivations on a basis of the opens of `U`, compatible with
restriction, glues to a local derivation over `U`. On an affine open `U`, the sections over a
basic open `D(g)` are the localization `Γ(X, U)_g`, so a derivation `Γ(X, U) → Γ(M, U)` extends
uniquely to a local derivation over `U`.

## Main definitions and results

- `AlgebraicGeometry.Scheme.Modules.LocalDerivation`: local derivations of `𝒪_X` into `M` over
  `U`.
- `AlgebraicGeometry.Scheme.Modules.LocalDerivation.glue`: gluing derivations given on a basis.
- `AlgebraicGeometry.Scheme.Modules.LocalDerivation.ext_of_basis`: local derivations agreeing on
  a basis agree.
- `AlgebraicGeometry.Scheme.Modules.LocalDerivation.ofIsAffineOpen`: the extension of a
  derivation of `Γ(X, U)`, for `U` affine.
- `AlgebraicGeometry.Scheme.Modules.LocalDerivation.ext_of_isAffineOpen`: on an affine open,
  local derivations agreeing on the restrictions of the functions on `U` agree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

/-- A **local derivation** of `𝒪_X` into the `𝒪_X`-module `M` over the open `U`: additive maps
`Γ(X, W) → Γ(M, W)` for the opens `W ⊆ U`, satisfying the Leibniz rule and compatible with
restriction. -/
structure LocalDerivation (U : X.Opens) where
  /-- The derivation on the sections over an open `W ⊆ U`. -/
  app (W : X.Opens) (hW : W ≤ U) : Γ(X, W) →+ Γ(M, W)
  map_mul (W : X.Opens) (hW : W ≤ U) (a b : Γ(X, W)) :
    app W hW (a * b) = a • app W hW b + b • app W hW a
  naturality (W W' : X.Opens) (hW : W ≤ U) (h : W' ≤ W) (a : Γ(X, W)) :
    app W' (h.trans hW) (X.presheaf.map (homOfLE h).op a) =
      M.presheaf.map (homOfLE h).op (app W hW a)

/-- The sections of a sheaf of modules over the empty open are trivial. -/
lemma subsingleton_sections_bot : Subsingleton Γ(M, ⊥) :=
  ⟨fun a b ↦ TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ (fun _ : PEmpty.{1} ↦ ⊥) ⊥
    (fun i ↦ i.elim) (fun _ hx ↦ hx.elim) a b fun i ↦ i.elim⟩

namespace LocalDerivation

variable {M} {U : X.Opens}

/-- A local derivation over `U` restricts to a local derivation over every open `V ⊆ U`. -/
def restrict (D : LocalDerivation M U) {V : X.Opens} (hV : V ≤ U) : LocalDerivation M V where
  app W hW := D.app W (hW.trans hV)
  map_mul W _ := D.map_mul W _
  naturality W W' _ h := D.naturality W W' _ h

@[simp]
lemma restrict_app (D : LocalDerivation M U) {V : X.Opens} (hV : V ≤ U) (W : X.Opens)
    (hW : W ≤ V) : (D.restrict hV).app W hW = D.app W (hW.trans hV) :=
  rfl

lemma app_one (D : LocalDerivation M U) (W : X.Opens) (hW : W ≤ U) :
    D.app W hW 1 = 0 := by
  have h := D.map_mul W hW 1 1
  rw [mul_one, one_smul] at h
  exact left_eq_add.mp h

/-- The derivative of an inverse: if `a * b = 1`, then `D a = -a² D b`. -/
lemma app_eq_neg_sq_smul_of_mul_eq_one (D : LocalDerivation M U) {W : X.Opens} (hW : W ≤ U)
    {a b : Γ(X, W)} (hab : a * b = 1) : D.app W hW a = -(a ^ 2) • D.app W hW b := by
  have h := D.map_mul W hW a b
  rw [hab, app_one] at h
  calc D.app W hW a = (a * b) • D.app W hW a := by rw [hab, one_smul]
    _ = a • (b • D.app W hW a) := mul_smul _ _ _
    _ = a • -(a • D.app W hW b) := by rw [eq_neg_of_add_eq_zero_right h.symm]
    _ = -(a ^ 2) • D.app W hW b := by rw [smul_neg, smul_smul, neg_smul, sq]

section Glue

variable {ι : Type*} (O : ι → X.Opens) (d : ∀ i, Γ(X, O i) →+ Γ(M, O i))

/-- `n` is the value at `f` of the derivation glued from the derivations `d i` on the opens
`O i`: its restriction to every `O i ⊆ W` is `d i (f|_{O i})`. -/
def IsGlueValue {W : X.Opens} (f : Γ(X, W)) (n : Γ(M, W)) : Prop :=
  ∀ i (h : O i ≤ W), M.presheaf.map (homOfLE h).op n = d i (X.presheaf.map (homOfLE h).op f)

variable {O d}
variable (hO : ∀ i, O i ≤ U) (hcov : ∀ W ≤ U, ∀ x ∈ W, ∃ i, x ∈ O i ∧ O i ≤ W)

include hcov in
lemma IsGlueValue.unique {W : X.Opens} (hW : W ≤ U) {f : Γ(X, W)} {n n' : Γ(M, W)}
    (hn : IsGlueValue O d f n) (hn' : IsGlueValue O d f n') : n = n' :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
    (fun i : {i // O i ≤ W} ↦ O i) W (fun i ↦ homOfLE i.2) (fun x hx ↦ by
      obtain ⟨i, hx, hi⟩ := hcov W hW x hx
      exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hx⟩) n n' fun i ↦ (hn i.1 i.2).trans (hn' i.1 i.2).symm

variable (hcomp : ∀ i j (h : O j ≤ O i) (a : Γ(X, O i)),
    d j (X.presheaf.map (homOfLE h).op a) = M.presheaf.map (homOfLE h).op (d i a))

include hcomp in
lemma map_d_restrict {i k : ι} (φ : O k ⟶ O i) {W : X.Opens} (hi : O i ≤ W) (hk : O k ≤ W)
    (f : Γ(X, W)) :
    M.presheaf.map φ.op (d i (X.presheaf.map (homOfLE hi).op f)) =
      d k (X.presheaf.map (homOfLE hk).op f) := by
  rw [Subsingleton.elim φ (homOfLE φ.le), ← hcomp, Scheme.presheaf_map_map_apply,
    Subsingleton.elim (homOfLE φ.le ≫ homOfLE hi) (homOfLE hk)]

include hcov hcomp in
lemma exists_isGlueValue {W : X.Opens} (hW : W ≤ U) (f : Γ(X, W)) :
    ∃ n, IsGlueValue O d f n := by
  let sf (i : {i // O i ≤ W}) : Γ(M, O i) := d i (X.presheaf.map (homOfLE i.2).op f)
  have hsf : TopCat.Presheaf.IsCompatible M.presheaf (fun i : {i // O i ≤ W} ↦ O i) sf := by
    intro i j
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
      (fun k : {k // O k ≤ O i ⊓ O j} ↦ O k) _ (fun k ↦ homOfLE k.2) (fun x hx ↦ by
        obtain ⟨k, hx, hk⟩ := hcov _ ((inf_le_left.trans i.2).trans hW) x hx
        exact Opens.mem_iSup.mpr ⟨⟨k, hk⟩, hx⟩) _ _ fun k ↦ ?_
    change M.presheaf.map _ (M.presheaf.map _ (sf i)) = M.presheaf.map _ (M.presheaf.map _ (sf j))
    simp only [sf, presheaf_map_map_apply]
    rw [map_d_restrict hcomp _ i.2 (k.2.trans (inf_le_left.trans i.2)),
      map_d_restrict hcomp _ j.2 (k.2.trans (inf_le_left.trans i.2))]
  obtain ⟨n, hn, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩
    (fun i : {i // O i ≤ W} ↦ O i) W (fun i ↦ homOfLE i.2) (fun x hx ↦ by
      obtain ⟨i, hx, hi⟩ := hcov W hW x hx
      exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hx⟩) sf hsf
  exact ⟨n, fun i h ↦ hn ⟨i, h⟩⟩

variable (hd : ∀ i (a b : Γ(X, O i)), d i (a * b) = a • d i b + b • d i a)

include hd in
lemma IsGlueValue.mul {W : X.Opens} {f g : Γ(X, W)} {n m : Γ(M, W)}
    (hn : IsGlueValue O d f n) (hm : IsGlueValue O d g m) :
    IsGlueValue O d (f * g) (f • m + g • n) := by
  intro i h
  rw [map_add, map_smul, map_smul, hn i h, hm i h, _root_.map_mul, hd]

lemma IsGlueValue.add {W : X.Opens} {f g : Γ(X, W)} {n m : Γ(M, W)}
    (hn : IsGlueValue O d f n) (hm : IsGlueValue O d g m) :
    IsGlueValue O d (f + g) (n + m) := by
  intro i h
  rw [map_add, hn i h, hm i h, map_add, map_add]

lemma isGlueValue_zero {W : X.Opens} : IsGlueValue O d (0 : Γ(X, W)) 0 := by
  intro i h
  rw [map_zero, map_zero, map_zero]

lemma IsGlueValue.map {W W' : X.Opens} (h : W' ≤ W) {f : Γ(X, W)} {n : Γ(M, W)}
    (hn : IsGlueValue O d f n) :
    IsGlueValue O d (X.presheaf.map (homOfLE h).op f) (M.presheaf.map (homOfLE h).op n) := by
  intro i hi
  rw [presheaf_map_homOfLE_map_homOfLE, hn i (hi.trans h), Scheme.presheaf_map_map_apply]
  rfl

include hcomp in
lemma isGlueValue_self (i : ι) (a : Γ(X, O i)) : IsGlueValue O d a (d i a) :=
  fun j h ↦ (hcomp i j h a).symm

/-- **Gluing derivations.** Derivations `d i` on the opens `O i` of a basis of the opens of `U`,
compatible with restriction, glue to a local derivation over `U`. -/
noncomputable def glue : LocalDerivation M U where
  app _ hW :=
    { toFun f := (exists_isGlueValue hcov hcomp hW f).choose
      map_zero' := (exists_isGlueValue hcov hcomp hW _).choose_spec.unique hcov hW
        isGlueValue_zero
      map_add' f g := (exists_isGlueValue hcov hcomp hW _).choose_spec.unique hcov hW
        ((exists_isGlueValue hcov hcomp hW f).choose_spec.add
          (exists_isGlueValue hcov hcomp hW g).choose_spec) }
  map_mul _ hW f g := (exists_isGlueValue hcov hcomp hW _).choose_spec.unique hcov hW
    ((exists_isGlueValue hcov hcomp hW f).choose_spec.mul hd
      (exists_isGlueValue hcov hcomp hW g).choose_spec)
  naturality _ _ hW h f := (exists_isGlueValue hcov hcomp (h.trans hW) _).choose_spec.unique hcov
    (h.trans hW) ((exists_isGlueValue hcov hcomp hW f).choose_spec.map h)

lemma isGlueValue_glue_app {W : X.Opens} (hW : W ≤ U) (f : Γ(X, W)) :
    IsGlueValue O d f ((glue hcov hcomp hd).app W hW f) :=
  (exists_isGlueValue hcov hcomp hW f).choose_spec

lemma glue_app_basis (i : ι) (a : Γ(X, O i)) : (glue hcov hcomp hd).app (O i) (hO i) a = d i a :=
  (isGlueValue_glue_app hcov hcomp hd (hO i) a).unique hcov (hO i)
    (isGlueValue_self hcomp i a)

end Glue

/-- **Local derivations agreeing on a basis agree.** -/
lemma ext_of_basis {ι : Type*} (O : ι → X.Opens) (hO : ∀ i, O i ≤ U)
    (hcov : ∀ W ≤ U, ∀ x ∈ W, ∃ i, x ∈ O i ∧ O i ≤ W) (D₁ D₂ : LocalDerivation M U)
    (h : ∀ i (a : Γ(X, O i)), D₁.app (O i) (hO i) a = D₂.app (O i) (hO i) a)
    (W : X.Opens) (hW : W ≤ U) (f : Γ(X, W)) : D₁.app W hW f = D₂.app W hW f := by
  have h₁ : IsGlueValue O (fun i ↦ D₁.app (O i) (hO i)) f (D₁.app W hW f) := fun i hi ↦
    (D₁.naturality W (O i) hW hi f).symm
  have h₂ : IsGlueValue O (fun i ↦ D₁.app (O i) (hO i)) f (D₂.app W hW f) := fun i hi ↦ by
    rw [← D₂.naturality W (O i) hW hi f, h]
  exact h₁.unique hcov hW h₂

section Cover

variable {ι : Type*} (V : ι → X.Opens) (hV : ⨆ i, V i = ⊤) (D : ∀ i, LocalDerivation M (V i))
  (hD : ∀ i j (W : X.Opens) (hi : W ≤ V i) (hj : W ≤ V j) (a : Γ(X, W)),
    (D i).app W hi a = (D j).app W hj a)

include hV in
lemma cover_basis (W : X.Opens) (_ : W ≤ ⊤) (x : X) (hx : x ∈ W) :
    ∃ p : Σ i, {W : X.Opens // W ≤ V i}, x ∈ p.2.1 ∧ p.2.1 ≤ W := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hV.ge (Set.mem_univ x))
  exact ⟨⟨i, W ⊓ V i, inf_le_right⟩, ⟨hx, hi⟩, inf_le_left⟩

/-- **Gluing local derivations along an open cover.** Local derivations over the opens `V i` of
an open cover, agreeing on the opens contained in two of them, glue to a local derivation over
`⊤`. -/
noncomputable def glueCover : LocalDerivation M ⊤ :=
  glue (O := fun p : Σ i, {W : X.Opens // W ≤ V i} ↦ p.2.1)
    (d := fun p ↦ (D p.1).app p.2.1 p.2.2) (cover_basis V hV)
    (fun p q h a ↦ by
      dsimp only
      rw [hD q.1 p.1 q.2.1 q.2.2 (h.trans p.2.2), (D p.1).naturality _ _ p.2.2 h])
    (fun p a b ↦ (D p.1).map_mul _ _ a b)

lemma glueCover_app (i : ι) (W : X.Opens) (hW : W ≤ V i) (a : Γ(X, W)) :
    (glueCover V hV D hD).app W le_top a = (D i).app W hW a :=
  glue_app_basis (O := fun p : Σ i, {W : X.Opens // W ≤ V i} ↦ p.2.1) (fun _ ↦ le_top) _ _ _
    ⟨i, W, hW⟩ a

end Cover

section Affine

variable (hU : IsAffineOpen U)

include hU in
lemma basicOpen_cover (W : X.Opens) (hW : W ≤ U) (x : X) (hx : x ∈ W) :
    ∃ g : Γ(X, U), x ∈ X.basicOpen g ∧ X.basicOpen g ≤ W := by
  obtain ⟨g, hg, hxg⟩ := hU.exists_basicOpen_le ⟨x, hx⟩ (hW hx)
  exact ⟨g, hxg, hg⟩

/-- The restriction `Γ(X, U) → Γ(M, D(g))` of a map `δ : Γ(X, U) → Γ(M, U)`. -/
noncomputable def restrictBasicOpen (δ : Γ(X, U) →+ Γ(M, U)) (g : Γ(X, U)) :
    Γ(X, U) →+ Γ(M, X.basicOpen g) :=
  (M.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.comp δ

variable (δ : Γ(X, U) →+ Γ(M, U)) (hδ : ∀ a b, δ (a * b) = a • δ b + b • δ a)

include hδ in
lemma restrictBasicOpen_mul (g : Γ(X, U)) (a b : Γ(X, U)) :
    restrictBasicOpen δ g (a * b) =
      (RingHom.id _) (algebraMap Γ(X, U) Γ(X, X.basicOpen g) a) • restrictBasicOpen δ g b +
        (RingHom.id _) (algebraMap Γ(X, U) Γ(X, X.basicOpen g) b) • restrictBasicOpen δ g a := by
  simp only [restrictBasicOpen, AddMonoidHom.coe_comp, Function.comp_apply, hδ, map_add,
    map_smul, RingHom.id_apply]
  rfl

/-- The derivation `Γ(X, D(g)) → Γ(M, D(g))` extending `δ`, `Γ(X, D(g))` being the localization
of `Γ(X, U)` at `g`. -/
noncomputable def basicOpenDerivation (g : Γ(X, U)) : Γ(X, X.basicOpen g) →+ Γ(M, X.basicOpen g) :=
  haveI := hU.isLocalization_basicOpen g
  IsLocalization.extendDerivation (Submonoid.powers g) (RingHom.id _) (restrictBasicOpen δ g)
    (restrictBasicOpen_mul δ hδ g)

lemma basicOpenDerivation_mul (g : Γ(X, U)) (a b : Γ(X, X.basicOpen g)) :
    basicOpenDerivation hU δ hδ g (a * b) =
      a • basicOpenDerivation hU δ hδ g b + b • basicOpenDerivation hU δ hδ g a :=
  haveI := hU.isLocalization_basicOpen g
  IsLocalization.extendDerivation_mul (Submonoid.powers g) (RingHom.id _) _ _ a b

lemma basicOpenDerivation_restrict (g : Γ(X, U)) (a : Γ(X, U)) :
    basicOpenDerivation hU δ hδ g (X.presheaf.map (homOfLE (X.basicOpen_le g)).op a) =
      M.presheaf.map (homOfLE (X.basicOpen_le g)).op (δ a) :=
  haveI := hU.isLocalization_basicOpen g
  IsLocalization.extendDerivation_algebraMap (Submonoid.powers g) (RingHom.id _) _ _ a

lemma basicOpenDerivation_map {g h : Γ(X, U)} (hgh : X.basicOpen h ≤ X.basicOpen g)
    (a : Γ(X, X.basicOpen g)) :
    basicOpenDerivation hU δ hδ h (X.presheaf.map (homOfLE hgh).op a) =
      M.presheaf.map (homOfLE hgh).op (basicOpenDerivation hU δ hδ g a) := by
  have := hU.isLocalization_basicOpen g
  let ψ : Γ(X, X.basicOpen g) →+* Γ(X, X.basicOpen h) := (X.presheaf.map (homOfLE hgh).op).hom
  have := IsLocalization.derivation_ext (Submonoid.powers g) ψ
    (δ₁ := fun a ↦ basicOpenDerivation hU δ hδ h (ψ a))
    (δ₂ := fun a ↦ M.presheaf.map (homOfLE hgh).op (basicOpenDerivation hU δ hδ g a))
    (fun x y ↦ by simp only [_root_.map_mul, basicOpenDerivation_mul])
    (fun x y ↦ by simp only [basicOpenDerivation_mul, map_add, map_smul]; rfl)
    (fun c ↦ by
      change basicOpenDerivation hU δ hδ h (X.presheaf.map (homOfLE hgh).op
        (X.presheaf.map (homOfLE (X.basicOpen_le g)).op c)) = M.presheaf.map (homOfLE hgh).op
          (basicOpenDerivation hU δ hδ g (X.presheaf.map (homOfLE (X.basicOpen_le g)).op c))
      rw [basicOpenDerivation_restrict, Scheme.presheaf_map_map_apply,
        Subsingleton.elim (homOfLE hgh ≫ homOfLE (X.basicOpen_le g)) (homOfLE (X.basicOpen_le h)),
        basicOpenDerivation_restrict, presheaf_map_homOfLE_map_homOfLE])
  exact congrFun this a

/-- **Derivations on an affine open extend to local derivations.** For `U` affine, a derivation
`δ : Γ(X, U) → Γ(M, U)` extends to a local derivation over `U`: on a basic open `D(g)` it is the
extension of `δ` to the localization `Γ(X, D(g)) = Γ(X, U)_g`. -/
noncomputable def ofIsAffineOpen : LocalDerivation M U :=
  glue (O := fun g : Γ(X, U) ↦ X.basicOpen g)
    (fun W hW x hx ↦ basicOpen_cover hU W hW x hx) (fun _ _ hgh a ↦ basicOpenDerivation_map
      hU δ hδ hgh a) (fun g a b ↦ basicOpenDerivation_mul hU δ hδ g a b)

lemma ofIsAffineOpen_app_basicOpen (g : Γ(X, U)) :
    (ofIsAffineOpen hU δ hδ).app (X.basicOpen g) (X.basicOpen_le g) =
      basicOpenDerivation hU δ hδ g :=
  AddMonoidHom.ext fun a ↦ glue_app_basis (O := fun g : Γ(X, U) ↦ X.basicOpen g)
    (fun g ↦ X.basicOpen_le g) _ _ _ g a

lemma ofIsAffineOpen_app_self (a : Γ(X, U)) : (ofIsAffineOpen hU δ hδ).app U le_rfl a = δ a :=
  (isGlueValue_glue_app (O := fun g : Γ(X, U) ↦ X.basicOpen g) _ _ _ le_rfl a).unique
    (fun W hW x hx ↦ basicOpen_cover hU W hW x hx) le_rfl fun g _ ↦
      (basicOpenDerivation_restrict hU δ hδ g a).symm

include hU in
/-- **Uniqueness of local derivations on an affine open.** Two local derivations over an affine
open `U` agreeing on `Γ(X, U)` agree: on a basic open `D(g)`, both are derivations of the
localization `Γ(X, U)_g`. -/
lemma ext_of_isAffineOpen (D₁ D₂ : LocalDerivation M U)
    (h : ∀ a, D₁.app U le_rfl a = D₂.app U le_rfl a) (W : X.Opens) (hW : W ≤ U)
    (f : Γ(X, W)) : D₁.app W hW f = D₂.app W hW f :=
  ext_of_basis (fun g : Γ(X, U) ↦ X.basicOpen g) (fun g ↦ X.basicOpen_le g)
    (fun W hW x hx ↦ basicOpen_cover hU W hW x hx) D₁ D₂ (fun g a ↦ by
      have := hU.isLocalization_basicOpen g
      refine congrFun (IsLocalization.derivation_ext (Submonoid.powers g) (RingHom.id _)
        (δ₁ := D₁.app _ (X.basicOpen_le g)) (δ₂ := D₂.app _ (X.basicOpen_le g))
        (D₁.map_mul _ _) (D₂.map_mul _ _) fun c ↦ ?_) a
      change D₁.app _ _ (X.presheaf.map (homOfLE (X.basicOpen_le g)).op c) =
        D₂.app _ _ (X.presheaf.map (homOfLE (X.basicOpen_le g)).op c)
      rw [D₁.naturality U _ le_rfl, D₂.naturality U _ le_rfl, h]) W hW f

end Affine

/-- Local derivations agreeing on a set of functions generating `Γ(X, W)` as a ring agree on
`Γ(X, W)`. -/
lemma app_eq_of_closure (D₁ D₂ : LocalDerivation M U) {W : X.Opens} (hW : W ≤ U)
    (T : Set Γ(X, W)) (hT : Subring.closure T = ⊤)
    (h : ∀ a ∈ T, D₁.app W hW a = D₂.app W hW a) (a : Γ(X, W)) :
    D₁.app W hW a = D₂.app W hW a := by
  have ha : a ∈ Subring.closure T := hT ▸ Subring.mem_top a
  induction ha using Subring.closure_induction with
  | mem x hx => exact h x hx
  | zero => rw [map_zero, map_zero]
  | one => rw [app_one, app_one]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | neg x _ hx => rw [map_neg, map_neg, hx]
  | mul x y _ _ hx hy => rw [D₁.map_mul, D₂.map_mul, hx, hy]

/-- The postcomposition of a local derivation with a morphism of modules. -/
noncomputable def postcomp (D : LocalDerivation M U) {N : X.Modules} (g : M ⟶ N) :
    LocalDerivation N U where
  app W hW := (g.app W).hom.comp (D.app W hW)
  map_mul W hW a b := by
    change g.app W (D.app W hW (a * b)) = a • g.app W (D.app W hW b) + b • g.app W (D.app W hW a)
    rw [D.map_mul, map_add, Hom.app_smul, Hom.app_smul]
  naturality W W' hW h a := by
    change g.app W' (D.app W' _ _) = _
    rw [D.naturality]
    exact Hom.app_presheaf_map g (homOfLE h) _

@[simp]
lemma postcomp_app (D : LocalDerivation M U) {N : X.Modules} (g : M ⟶ N) (W : X.Opens)
    (hW : W ≤ U) (a : Γ(X, W)) : (D.postcomp g).app W hW a = g.app W (D.app W hW a) :=
  rfl

/-- **Local derivations agreeing on an open cover agree.** -/
lemma ext_of_cover {ι : Type*} (V : ι → X.Opens) (hV : ⨆ i, V i = ⊤)
    (D₁ D₂ : LocalDerivation M ⊤)
    (h : ∀ i (W : X.Opens) (_ : W ≤ V i) (a : Γ(X, W)), D₁.app W le_top a = D₂.app W le_top a)
    (W : X.Opens) (a : Γ(X, W)) : D₁.app W le_top a = D₂.app W le_top a :=
  ext_of_basis (fun p : Σ i, {W : X.Opens // W ≤ V i} ↦ p.2.1) (fun _ ↦ le_top)
    (cover_basis V hV) D₁ D₂ (fun p a ↦ h p.1 p.2.1 p.2.2 a) W le_top a

section Relative

variable {S : Scheme.{u}} (f : X ⟶ S)

/-- Two ring homomorphisms out of `(f⁻¹𝒪_S)(V)` agree if they agree on the images of the
sections of `𝒪_S` over the opens `U` with `V ⊆ f⁻¹ U`. -/
lemma pullbackPresheaf_hom_ext {V : X.Opens} {R : CommRingCat.{u}}
    {g₁ g₂ : f.pullbackPresheaf.obj (op V) ⟶ R}
    (h : ∀ (U : S.Opens) (e : V ≤ f ⁻¹ᵁ U),
      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).unit.app
          S.presheaf).app (op U) ≫ f.pullbackPresheaf.map (homOfLE e).op ≫ g₁ =
        ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).unit.app
          S.presheaf).app (op U) ≫ f.pullbackPresheaf.map (homOfLE e).op ≫ g₂) :
    g₁ = g₂ := by
  refine ((Opens.map f.base).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit S.presheaf
    (op V)).hom_ext fun j ↦ ?_
  have := h j.left.unop j.hom.unop.le
  rw [Subsingleton.elim (homOfLE j.hom.unop.le).op j.hom] at this
  exact (Category.assoc _ _ _).trans (this.trans (Category.assoc _ _ _).symm)

attribute [local instance] IsLocalization.opModule

/-- A local derivation over `⊤` vanishing on the functions coming from `S` is a derivation of
`𝒪_X` relative to `f⁻¹𝒪_S`. -/
noncomputable def toDerivation' (D : LocalDerivation M ⊤)
    (h : ∀ (U : S.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (c : Γ(S, U)),
      D.app V le_top (f.appLE U V e c) = 0) :
    PresheafOfModulesOfCommRing.Derivation' M.val f.pullbackPresheafToPresheaf where
  d {V} := D.app V.unop le_top
  d_mul {V} a b := D.map_mul _ _ a b
  d_map {V V'} i x := by
    rw [Subsingleton.elim i (homOfLE i.unop.le).op]
    exact D.naturality V.unop V'.unop le_top i.unop.le x
  d_app {V} a := by
    let ρ := IsLocalization.derivationToTrivSqZeroExt (A := Γ(X, V.unop)) (B := Γ(X, V.unop))
      (RingHom.id _) (D.app V.unop le_top) (D.map_mul _ _)
    let ρ₀ : Γ(X, V.unop) →+* TrivSqZeroExt Γ(X, V.unop) Γ(M, V.unop) := TrivSqZeroExt.inlHom _ _
    have key : f.pullbackPresheafToPresheaf.app V ≫ CommRingCat.ofHom ρ =
        f.pullbackPresheafToPresheaf.app V ≫ CommRingCat.ofHom ρ₀ := by
      refine pullbackPresheaf_hom_ext f fun U e ↦ ?_
      have e' : ∀ {R : CommRingCat.{u}} (g : Γ(X, V.unop) ⟶ R),
          ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).unit.app
            S.presheaf).app (op U) ≫ f.pullbackPresheaf.map (homOfLE e).op ≫
              f.pullbackPresheafToPresheaf.app V ≫ g = f.appLE U V.unop e ≫ g := fun g ↦ by
        rw [Scheme.Hom.appLE_eq_pullbackPresheafToPresheaf_app]
        simp only [Category.assoc]
      rw [e', e']
      ext c
      · change (ρ (f.appLE U V.unop e c)).fst = (ρ₀ (f.appLE U V.unop e c)).fst
        rw [IsLocalization.fst_derivationToTrivSqZeroExt]
        rfl
      · change (ρ (f.appLE U V.unop e c)).snd = 0
        rw [IsLocalization.snd_derivationToTrivSqZeroExt]
        exact h U V.unop e c
    have := congrArg (fun g ↦ (g a).snd) (congrArg CommRingCat.Hom.hom key)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] at this
    rw [IsLocalization.snd_derivationToTrivSqZeroExt] at this
    exact this

@[simp]
lemma toDerivation'_d (D : LocalDerivation M ⊤)
    (h : ∀ (U : S.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (c : Γ(S, U)),
      D.app V le_top (f.appLE U V e c) = 0) (V : X.Opens) (a : Γ(X, V)) :
    (toDerivation' f D h).d (X := op V) a = D.app V le_top a :=
  rfl

/-- A relative derivation of `𝒪_X`, as a local derivation over `⊤`. -/
def ofDerivation' {S' : X.Opensᵒᵖ ⥤ CommRingCat.{u}} {φ : S' ⟶ X.presheaf}
    (d : PresheafOfModulesOfCommRing.Derivation' M.val φ) : LocalDerivation M ⊤ where
  app W _ := d.d (X := op W)
  map_mul _ _ a b := d.d_mul a b
  naturality _ _ _ h a := d.d_map (homOfLE h).op a

@[simp]
lemma ofDerivation'_app {S' : X.Opensᵒᵖ ⥤ CommRingCat.{u}} {φ : S' ⟶ X.presheaf}
    (d : PresheafOfModulesOfCommRing.Derivation' M.val φ) (W : X.Opens) (a : Γ(X, W)) :
    (ofDerivation' d).app W le_top a = d.d (X := op W) a :=
  rfl

end Relative

end LocalDerivation

end AlgebraicGeometry.Scheme.Modules
