import Jacobian.AlgebraicGeometry.Modules.FreeGenerator.Local
import Jacobian.AlgebraicGeometry.Modules.LocalIsomorphism
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Morphisms of modules from a basis of opens

Let `M` and `N` be `𝒪_X`-modules and `O i` a family of opens of `X` forming a basis of the
topology. Linear maps `Γ(M, O i) → Γ(N, O i)`, compatible with restriction between the opens
`O i`, extend uniquely to a morphism `M ⟶ N`.

## Main definitions and results

- `AlgebraicGeometry.Scheme.Modules.homOfBasis`: the morphism `M ⟶ N` glued from maps on a
  basis.
- `AlgebraicGeometry.Scheme.Modules.homOfBasis_app_basis`: it is the given map on the basis.
- `AlgebraicGeometry.Scheme.Modules.isIso_of_bijective_app_of_basis`: a morphism which is
  bijective on the sections over the opens of a basis is an isomorphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type*} (O : ι → X.Opens)
  (φ : ∀ i, Γ(M, O i) →+ Γ(N, O i))

/-- `n` is the value at `m` of the morphism glued from the maps `φ i` on the opens `O i`: its
restriction to every `O i ⊆ W` is `φ i (m|_{O i})`. -/
def IsBasisGlueValue {W : X.Opens} (m : Γ(M, W)) (n : Γ(N, W)) : Prop :=
  ∀ i (h : O i ≤ W), N.presheaf.map (homOfLE h).op n = φ i (M.presheaf.map (homOfLE h).op m)

variable {O φ}
variable (hcov : ∀ W : X.Opens, ∀ x ∈ W, ∃ i, x ∈ O i ∧ O i ≤ W)

include hcov in
lemma IsBasisGlueValue.unique {W : X.Opens} {m : Γ(M, W)} {n n' : Γ(N, W)}
    (hn : IsBasisGlueValue O φ m n) (hn' : IsBasisGlueValue O φ m n') : n = n' :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i : {i // O i ≤ W} ↦ O i) W (fun i ↦ homOfLE i.2) (fun x hx ↦ by
      obtain ⟨i, hx, hi⟩ := hcov W x hx
      exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hx⟩) n n' fun i ↦ (hn i.1 i.2).trans (hn' i.1 i.2).symm

variable (hcomp : ∀ i j (h : O j ≤ O i) (m : Γ(M, O i)),
    φ j (M.presheaf.map (homOfLE h).op m) = N.presheaf.map (homOfLE h).op (φ i m))

include hcomp in
lemma map_φ_restrict {i l : ι} (h : O l ≤ O i) {W : X.Opens} (hi : O i ≤ W) (hl : O l ≤ W)
    (m : Γ(M, W)) :
    N.presheaf.map (homOfLE h).op (φ i (M.presheaf.map (homOfLE hi).op m)) =
      φ l (M.presheaf.map (homOfLE hl).op m) := by
  rw [← hcomp, presheaf_map_homOfLE_map_homOfLE]

include hcov hcomp in
lemma exists_isBasisGlueValue {W : X.Opens} (m : Γ(M, W)) : ∃ n, IsBasisGlueValue O φ m n := by
  let sf (i : {i // O i ≤ W}) : Γ(N, O i) := φ i (M.presheaf.map (homOfLE i.2).op m)
  have hsf : TopCat.Presheaf.IsCompatible N.presheaf (fun i : {i // O i ≤ W} ↦ O i) sf := by
    intro i j
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
      (fun l : {l // O l ≤ O i ⊓ O j} ↦ O l) _ (fun l ↦ homOfLE l.2) (fun x hx ↦ by
        obtain ⟨l, hx, hl⟩ := hcov _ x hx
        exact Opens.mem_iSup.mpr ⟨⟨l, hl⟩, hx⟩) _ _ fun l ↦ ?_
    change N.presheaf.map _ (N.presheaf.map _ (sf i)) = N.presheaf.map _ (N.presheaf.map _ (sf j))
    simp only [sf, presheaf_map_map_apply]
    rw [Subsingleton.elim (homOfLE l.2 ≫ Opens.infLELeft (O i) (O j))
        (homOfLE (l.2.trans inf_le_left)),
      Subsingleton.elim (homOfLE l.2 ≫ Opens.infLERight (O i) (O j))
        (homOfLE (l.2.trans inf_le_right)),
      map_φ_restrict hcomp _ i.2 (l.2.trans (inf_le_left.trans i.2)),
      map_φ_restrict hcomp _ j.2 (l.2.trans (inf_le_left.trans i.2))]
  obtain ⟨n, hn, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨N.presheaf, N.isSheaf⟩
    (fun i : {i // O i ≤ W} ↦ O i) W (fun i ↦ homOfLE i.2) (fun x hx ↦ by
      obtain ⟨i, hx, hi⟩ := hcov W x hx
      exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hx⟩) sf hsf
  exact ⟨n, fun i h ↦ hn ⟨i, h⟩⟩

lemma IsBasisGlueValue.add {W : X.Opens} {m m' : Γ(M, W)} {n n' : Γ(N, W)}
    (hn : IsBasisGlueValue O φ m n) (hn' : IsBasisGlueValue O φ m' n') :
    IsBasisGlueValue O φ (m + m') (n + n') := by
  intro i h
  rw [map_add, hn i h, hn' i h, map_add, map_add]

lemma isBasisGlueValue_zero {W : X.Opens} : IsBasisGlueValue O φ (0 : Γ(M, W)) 0 := by
  intro i h
  rw [map_zero, map_zero, map_zero]

lemma IsBasisGlueValue.smul (hsmul : ∀ i (r : Γ(X, O i)) (m : Γ(M, O i)), φ i (r • m) = r • φ i m)
    {W : X.Opens} {m : Γ(M, W)} {n : Γ(N, W)} (hn : IsBasisGlueValue O φ m n) (r : Γ(X, W)) :
    IsBasisGlueValue O φ (r • m) (r • n) := by
  intro i h
  rw [map_smul, map_smul, hn i h, hsmul]

lemma IsBasisGlueValue.map {W W' : X.Opens} (h : W' ≤ W) {m : Γ(M, W)} {n : Γ(N, W)}
    (hn : IsBasisGlueValue O φ m n) :
    IsBasisGlueValue O φ (M.presheaf.map (homOfLE h).op m) (N.presheaf.map (homOfLE h).op n) := by
  intro i hi
  rw [presheaf_map_homOfLE_map_homOfLE, hn i (hi.trans h), presheaf_map_homOfLE_map_homOfLE]

include hcomp in
lemma isBasisGlueValue_self (i : ι) (m : Γ(M, O i)) : IsBasisGlueValue O φ m (φ i m) :=
  fun j h ↦ (hcomp i j h m).symm

variable (hsmul : ∀ i (r : Γ(X, O i)) (m : Γ(M, O i)), φ i (r • m) = r • φ i m)

/-- **Gluing morphisms from a basis.** Maps `φ i : Γ(M, O i) → Γ(N, O i)` on the opens `O i` of a
basis of `X`, linear and compatible with restriction, glue to a morphism `M ⟶ N`. -/
noncomputable def homOfBasis : M ⟶ N :=
  ⟨PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom
        { toFun m := (exists_isBasisGlueValue hcov hcomp (W := W.unop) m).choose
          map_zero' := (exists_isBasisGlueValue hcov hcomp _).choose_spec.unique hcov
            isBasisGlueValue_zero
          map_add' m m' := (exists_isBasisGlueValue hcov hcomp _).choose_spec.unique hcov
            ((exists_isBasisGlueValue hcov hcomp m).choose_spec.add
              (exists_isBasisGlueValue hcov hcomp m').choose_spec) }
      naturality W W' i := by
        ext m
        exact (exists_isBasisGlueValue hcov hcomp _).choose_spec.unique hcov
          ((exists_isBasisGlueValue hcov hcomp m).choose_spec.map (W' := W'.unop) i.unop.le) }
    fun W r m ↦ (exists_isBasisGlueValue hcov hcomp _).choose_spec.unique hcov
      ((exists_isBasisGlueValue hcov hcomp m).choose_spec.smul hsmul r)⟩

lemma isBasisGlueValue_homOfBasis_app {W : X.Opens} (m : Γ(M, W)) :
    IsBasisGlueValue O φ m ((homOfBasis hcov hcomp hsmul).app W m) :=
  (exists_isBasisGlueValue hcov hcomp m).choose_spec

lemma homOfBasis_app_basis (i : ι) (m : Γ(M, O i)) :
    (homOfBasis hcov hcomp hsmul).app (O i) m = φ i m :=
  (isBasisGlueValue_homOfBasis_app hcov hcomp hsmul m).unique hcov
    (isBasisGlueValue_self hcomp i m)

end AlgebraicGeometry.Scheme.Modules
