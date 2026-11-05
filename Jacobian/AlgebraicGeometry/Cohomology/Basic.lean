import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Over
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Sheaf cohomology of sheaves of modules on a scheme

Let `X` be a scheme and let `M` be a sheaf of `𝒪_X`-modules, i.e. an object of `X.Modules`.
We define the sheaf cohomology `M.H n` of `M` in degree `n` as the sheaf cohomology
`CategoryTheory.Sheaf.H` of the underlying sheaf of abelian groups, i.e. as the `Ext`-group
from the constant sheaf `ℤ` on the small Zariski site of `X`.

Multiplication by a global function `a : Γ(X, ⊤)` is an endomorphism `M.smulHom a` of `M`,
and this makes `M.H n` a module over `Γ(X, ⊤)`. If `X` is a scheme over a field `k`, the
ring map `k →+* Γ(X, ⊤)` induced by the structure morphism turns `M.H n` into a
`k`-vector space, whose dimension `M.finrankH k n` is the `n`-th cohomological invariant of `M`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.H`: the sheaf cohomology of a sheaf of modules.
- `AlgebraicGeometry.Scheme.Modules.smulHom`: multiplication by a global function.
- `AlgebraicGeometry.Scheme.Modules.moduleH`: the `Γ(X, ⊤)`-module structure on `M.H n`.
- `AlgebraicGeometry.Scheme.Modules.H.mapLinearMap`: the `k`-linear map on cohomology induced
  by a morphism, over a base field `k`.
- `AlgebraicGeometry.Scheme.Modules.cohomologyFunctor`: `M ↦ H^n(X, M)` as a functor to
  `k`-vector spaces.
- `AlgebraicGeometry.Scheme.Modules.finrankH`: the dimension of `M.H n` over a base field.
- `AlgebraicGeometry.Scheme.Modules.eulerChar`: the Euler characteristic of `M`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.H.zeroLinearEquiv`: `H⁰(X, M) ≅ Γ(X, M)`.
- `AlgebraicGeometry.Scheme.Modules.finrankH_of_isBilimit`: cohomology commutes with finite
  biproducts.
- `AlgebraicGeometry.Scheme.Modules.eulerChar_congr`: the Euler characteristic only depends on
  the isomorphism class of `M`.
-/


universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace Modules

/-- The `n`-th sheaf cohomology of a sheaf of modules on a scheme, as the `Ext`-group from
the constant sheaf `ℤ` to the underlying abelian sheaf. -/
def H (M : X.Modules) (n : ℕ) : Type u :=
  Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n

noncomputable instance (M : X.Modules) (n : ℕ) : AddCommGroup (M.H n) :=
  inferInstanceAs (AddCommGroup (Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n))

/-- The map on sheaf cohomology induced by a morphism of sheaves of modules. -/
noncomputable def H.map {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) : M.H n →+ N.H n :=
  Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) n

@[simp]
lemma H.map_id_apply (M : X.Modules) (n : ℕ) (x : M.H n) : H.map (𝟙 M) n x = x := by
  simp only [H.map]
  exact Sheaf.H.map_id_apply x

lemma H.map_comp_apply {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) (n : ℕ) (x : M.H n) :
    H.map (φ ≫ ψ) n x = H.map ψ n (H.map φ n x) := by
  exact (congrArg (fun q => Sheaf.H.map q n x)
    ((SheafOfModules.toSheaf X.ringCatSheaf).map_comp φ ψ)).trans
    (Sheaf.H.map_comp_apply
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)
      ((SheafOfModules.toSheaf X.ringCatSheaf).map ψ) x)

@[simp]
lemma H.map_add_apply {M N : X.Modules} (φ ψ : M ⟶ N) (n : ℕ) (x : M.H n) :
    H.map (φ + ψ) n x = H.map φ n x + H.map ψ n x := by
  exact (congrArg (fun q => Sheaf.H.map q n x)
    ((SheafOfModules.toSheaf X.ringCatSheaf).map_add (f := φ) (g := ψ))).trans
    (Sheaf.H.map_add_apply
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)
      ((SheafOfModules.toSheaf X.ringCatSheaf).map ψ) x)

@[simp]
lemma H.map_zero_apply {M N : X.Modules} (n : ℕ) (x : M.H n) :
    H.map (0 : M ⟶ N) n x = 0 := by
  have h := H.map_add_apply (0 : M ⟶ N) 0 n x
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- Multiplication by a global function `a : Γ(X, ⊤)`, as an endomorphism of the underlying
presheaf of abelian groups of a sheaf of modules `M`. -/
noncomputable def smulPresheafHom (M : X.Modules) (a : Γ(X, ⊤)) : M.presheaf ⟶ M.presheaf where
  app U := M.smul (X.presheaf.map (homOfLE le_top).op a)
  naturality U V i := by
    obtain ⟨U⟩ := U
    obtain ⟨V⟩ := V
    obtain ⟨i⟩ := i
    ext x
    have e : X.presheaf.map i.op (X.presheaf.map (homOfLE (le_top (a := U))).op a) =
        X.presheaf.map (homOfLE (le_top (a := V))).op a := by
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl
    have h := M.map_smul i (X.presheaf.map (homOfLE (le_top (a := U))).op a) x
    rw [e] at h
    exact h.symm

/-- Multiplication by a global function `a : Γ(X, ⊤)`, as an endomorphism of a sheaf of
modules `M`. Over an open `U` it is multiplication by the restriction of `a` to `U`. -/
noncomputable def smulHom (M : X.Modules) (a : Γ(X, ⊤)) : M ⟶ M :=
  ⟨PresheafOfModules.homMk (M.smulPresheafHom a) fun U r m ↦ by
    obtain ⟨U⟩ := U
    exact smul_comm (M := Γ(X, U)) (N := Γ(X, U)) (α := Γ(M, U))
      (X.presheaf.map (homOfLE le_top).op a) r m⟩

@[simp]
lemma smulHom_app_apply (M : X.Modules) (a : Γ(X, ⊤)) (U : X.Opens) (x : Γ(M, U)) :
    (M.smulHom a).app U x = X.presheaf.map (homOfLE (le_top (a := U))).op a • x :=
  rfl

@[simp]
lemma smulHom_one (M : X.Modules) : M.smulHom 1 = 𝟙 M := by
  ext U x
  simp

@[simp]
lemma smulHom_zero (M : X.Modules) : M.smulHom 0 = 0 := by
  ext U x
  simp

lemma smulHom_mul (M : X.Modules) (a b : Γ(X, ⊤)) :
    M.smulHom (a * b) = M.smulHom b ≫ M.smulHom a := by
  ext U x
  simp [mul_comm a b, mul_smul]

lemma smulHom_add (M : X.Modules) (a b : Γ(X, ⊤)) :
    M.smulHom (a + b) = M.smulHom a + M.smulHom b := by
  ext U x
  simp [add_smul]

@[reassoc]
lemma smulHom_naturality {M N : X.Modules} (φ : M ⟶ N) (a : Γ(X, ⊤)) :
    M.smulHom a ≫ φ = φ ≫ N.smulHom a := by
  ext U x
  simp

/-- Pushing forward multiplication by the pullback `g^♯ c` of a global function is
multiplication by `c`. -/
lemma pushforward_map_smulHom {Y : Scheme.{u}} (g : X ⟶ Y) (N : X.Modules) (c : Γ(Y, ⊤)) :
    (pushforward g).map (N.smulHom (g.appTop c)) = ((pushforward g).obj N).smulHom c := by
  ext U x
  rw [pushforward_map_app, smulHom_app_apply]
  refine (smulHom_app_apply N (g.appTop c) (g ⁻¹ᵁ U) x).trans ?_
  have h := ConcreteCategory.congr_hom (g.naturality (homOfLE (le_top (a := U))).op) c
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact congrArg (fun r : Γ(X, g ⁻¹ᵁ U) ↦ r • (show Γ(N, g ⁻¹ᵁ U) from x)) h.symm

/-- Multiplication by global functions on the `n`-th cohomology of a sheaf of modules, as a
ring homomorphism to the additive endomorphisms of `M.H n`. -/
noncomputable def smulEnd (M : X.Modules) (n : ℕ) : Γ(X, ⊤) →+* AddMonoid.End (M.H n) where
  toFun a := H.map (M.smulHom a) n
  map_one' := by
    refine AddMonoidHom.ext fun x ↦ ?_
    simp only [smulHom_one, H.map_id_apply]
    rfl
  map_zero' := by
    refine AddMonoidHom.ext fun x ↦ ?_
    simp only [smulHom_zero, H.map_zero_apply]
    rfl
  map_mul' a b := by
    refine AddMonoidHom.ext fun x ↦ ?_
    simp only [smulHom_mul, H.map_comp_apply]
    rfl
  map_add' a b := by
    refine AddMonoidHom.ext fun x ↦ ?_
    simp only [smulHom_add, H.map_add_apply]
    rfl

/-- The cohomology of a sheaf of modules on `X` is a module over the global functions of `X`,
via multiplication by global functions. -/
noncomputable instance moduleH (M : X.Modules) (n : ℕ) : Module Γ(X, ⊤) (M.H n) :=
  Module.compHom (M.H n) (M.smulEnd n)

lemma H.map_smul {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) (a : Γ(X, ⊤)) (x : M.H n) :
    H.map φ n (a • x) = a • H.map φ n x := by
  change H.map φ n (H.map (M.smulHom a) n x) = H.map (N.smulHom a) n (H.map φ n x)
  rw [← H.map_comp_apply, ← H.map_comp_apply, smulHom_naturality]

/-- The `Γ(X, ⊤)`-linear map on sheaf cohomology induced by a morphism of sheaves of modules. -/
noncomputable def H.mapₗ {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) : M.H n →ₗ[Γ(X, ⊤)] N.H n where
  toFun := H.map φ n
  map_add' := map_add _
  map_smul' := H.map_smul φ n

/-- An isomorphism of sheaves of modules induces a `Γ(X, ⊤)`-linear isomorphism on sheaf
cohomology. -/
noncomputable def H.mapLinearEquiv {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    M.H n ≃ₗ[Γ(X, ⊤)] N.H n :=
  LinearEquiv.ofLinearMap (H.mapₗ e.hom n) (H.mapₗ e.inv n)
    (LinearMap.ext fun x ↦ by simp [H.mapₗ, ← H.map_comp_apply])
    (LinearMap.ext fun x ↦ by simp [H.mapₗ, ← H.map_comp_apply])

lemma H.map_sum_apply {ι : Type*} (s : Finset ι) {M N : X.Modules} (φ : ι → (M ⟶ N)) (n : ℕ)
    (x : M.H n) : H.map (∑ i ∈ s, φ i) n x = ∑ i ∈ s, H.map (φ i) n x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, H.map_add_apply, ih]

/-- On global sections, multiplication by a global function `a` is the scalar action of `a`. -/
lemma smulHom_app_top_apply (M : X.Modules) (a : Γ(X, ⊤)) (x : Γ(M, ⊤)) :
    (M.smulHom a).app ⊤ x = a • x := by
  rw [smulHom_app_apply]
  congr 1
  change X.presheaf.map (𝟙 (Opposite.op ⊤)) a = a
  simp

/-- **Cohomology in degree `0` is global sections**: `H⁰(X, M) ≅ Γ(X, M)` as
`Γ(X, ⊤)`-modules. -/
noncomputable def H.zeroLinearEquiv (M : X.Modules) : M.H 0 ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) where
  __ := Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) isTerminalTop
  map_smul' a x :=
    (Sheaf.H.equiv₀_naturality (hT := isTerminalTop)
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (M.smulHom a)) x).symm.trans
      (smulHom_app_top_apply M a _)

end Modules

section Field

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

/-- The ring homomorphism `k →+* Γ(X, ⊤)` induced by the structure morphism of a
`k`-scheme `X`. -/
noncomputable def globalSectionsRingHom : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop).hom

namespace Modules

/-- The cohomology of a sheaf of modules on a `k`-scheme is a `k`-vector space, by restriction
of scalars along `AlgebraicGeometry.Scheme.globalSectionsRingHom`.

The base field `k` appears in the head `Module k (M.H n)` of the goal, so instance search is
not asked to guess it. -/
noncomputable instance moduleHOfField (M : X.Modules) (n : ℕ) : Module k (M.H n) :=
  Module.compHom (M.H n) (globalSectionsRingHom k (X := X))

/-- The `k`-action on `M.H n` is the `Γ(X, ⊤)`-action along the structure morphism. This is
the compatibility that an `IsScalarTower k Γ(X, ⊤) (M.H n)` instance would record, stated
without an `Algebra k Γ(X, ⊤)` instance. -/
lemma smul_H_eq_globalSectionsRingHom_smul (M : X.Modules) (n : ℕ) (c : k) (x : M.H n) :
    c • x = globalSectionsRingHom k (X := X) c • x :=
  rfl

/-- The `k`-linear map on sheaf cohomology induced by a morphism of sheaves of modules on a
`k`-scheme. -/
noncomputable def H.mapLinearMap {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) :
    M.H n →ₗ[k] N.H n :=
  { H.mapₗ φ n with map_smul' c := H.map_smul φ n (globalSectionsRingHom k c) }

@[simp]
lemma H.mapLinearMap_apply {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) (x : M.H n) :
    H.mapLinearMap k φ n x = H.map φ n x :=
  rfl

@[simp]
lemma H.mapLinearMap_id (M : X.Modules) (n : ℕ) :
    H.mapLinearMap k (𝟙 M) n = LinearMap.id :=
  LinearMap.ext (H.map_id_apply M n)

lemma H.mapLinearMap_comp {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) (n : ℕ) :
    H.mapLinearMap k (φ ≫ ψ) n = H.mapLinearMap k ψ n ∘ₗ H.mapLinearMap k φ n :=
  LinearMap.ext (H.map_comp_apply φ ψ n)

/-- The `n`-th sheaf cohomology `M ↦ H^n(X, M)` of sheaves of modules on a `k`-scheme, as a
functor to `k`-vector spaces. -/
@[simps]
noncomputable def cohomologyFunctor (n : ℕ) : X.Modules ⥤ ModuleCat.{u} k where
  obj M := ModuleCat.of k (M.H n)
  map φ := ModuleCat.ofHom (H.mapLinearMap k φ n)
  map_id M := by ext1; exact H.mapLinearMap_id k M n
  map_comp φ ψ := by ext1; exact H.mapLinearMap_comp k φ ψ n

/-- The `q`-th cohomological invariant `h^q(X, M)` of a sheaf of modules `M` on a
`k`-scheme `X`: the dimension of `H^q(X, M)` as a `k`-vector space. -/
noncomputable def finrankH (M : X.Modules) (q : ℕ) : ℕ := Module.finrank k (M.H q)

/-- The Euler characteristic `χ(X, M) = ∑ (-1)^q h^q(X, M)` of a sheaf of modules `M` on a
`k`-scheme `X`.

The sum is a `finsum`, so it is `0` whenever infinitely many terms are nonzero. That makes
`eulerChar` meaningful only together with a vanishing statement for the higher cohomology,
such as Grothendieck vanishing
the vanishing of cohomology above the dimension of the scheme. -/
noncomputable def eulerChar (M : X.Modules) : ℤ := ∑ᶠ q : ℕ, (-1) ^ q * (M.finrankH k q : ℤ)

/-- `h^q(X, M)` only depends on the isomorphism class of `M`. -/
lemma finrankH_congr {M N : X.Modules} (e : M ≅ N) (q : ℕ) : M.finrankH k q = N.finrankH k q :=
  LinearEquiv.finrank_eq
    { H.mapLinearEquiv e q with
      map_smul' := fun c x ↦ (H.mapLinearEquiv e q).map_smul (globalSectionsRingHom k c) x }

/-- The Euler characteristic only depends on the isomorphism class of a sheaf of modules. -/
lemma eulerChar_congr {M N : X.Modules} (e : M ≅ N) : M.eulerChar k = N.eulerChar k := by
  simp only [eulerChar, finrankH_congr k e]

omit [X.Over (Spec (CommRingCat.of k))] in
/-- **Changing the base field along an isomorphism.** If the structure morphism of `X` to
`Spec K` is the composite of `g : X ⟶ Spec L` with `Spec ψ` for an isomorphism `ψ : K ≅ L`,
then `dim_K H^q(X, M) = dim_L H^q(X, M)`: the two scalar actions correspond under `ψ`. -/
theorem finrankH_eq_of_comp_specMap {L : Type u} [Field L]
    (ψ : CommRingCat.of k ⟶ CommRingCat.of L) [IsIso ψ] (g : X ⟶ Spec (.of L)) (M : X.Modules)
    (q : ℕ) :
    (letI : X.Over (Spec (.of k)) := ⟨g ≫ Spec.map ψ⟩; M.finrankH k q) =
      (letI : X.Over (Spec (.of L)) := ⟨g⟩; M.finrankH L q) := by
  let : X.Over (Spec (.of k)) := ⟨g ≫ Spec.map ψ⟩
  let : X.Over (Spec (.of L)) := ⟨g⟩
  have hring :
      globalSectionsRingHom k (X := X) = (globalSectionsRingHom L (X := X)).comp ψ.hom := by
    simp only [globalSectionsRingHom]
    rw [← CommRingCat.hom_comp]
    congr 1
    change _ ≫ (g ≫ Spec.map ψ).appTop = ψ ≫ _ ≫ g.appTop
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc]
  have h := rank_eq_of_equiv_equiv (R := k) (R' := L) (M := M.H q) (M₁ := M.H q) ψ.hom
    (AddEquiv.refl _) (ConcreteCategory.bijective_of_isIso ψ) (fun r m ↦ by
      change globalSectionsRingHom k (X := X) r • m =
        globalSectionsRingHom L (X := X) (ψ.hom r) • m
      rw [hring, RingHom.comp_apply])
  exact congrArg Cardinal.toNat h

/-- **Cohomology of a finite biproduct.** If `b` is a bilimit bicone on a finite family `M`
of sheaves of modules, then `H^n(X, b.pt) ≅ ∏ᵢ H^n(X, Mᵢ)` as `k`-vector spaces, via the
projections and the inclusions of `b`. -/
noncomputable def H.isBilimitLinearEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → X.Modules} {b : Bicone M} (hb : b.IsBilimit) (n : ℕ) :
    b.pt.H n ≃ₗ[k] ((i : ι) → (M i).H n) where
  toFun x i := H.map (b.π i) n x
  invFun y := ∑ i, H.map (b.ι i) n (y i)
  map_add' x y := funext fun i ↦ map_add _ x y
  map_smul' c x := funext fun i ↦ H.map_smul _ n (globalSectionsRingHom k c) x
  left_inv x := by
    simp only [← H.map_comp_apply]
    rw [← H.map_sum_apply, IsBilimit.total hb, H.map_id_apply]
  right_inv y := funext fun j ↦ by
    simp only [map_sum, ← H.map_comp_apply, b.ι_π]
    rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [dif_neg hij, H.map_zero_apply])
      (by simp), dif_pos rfl, eqToHom_refl, H.map_id_apply]

/-- **`h^n` of a finite biproduct** is the sum of the `h^n` of the summands, when these are
finite-dimensional. -/
theorem finrankH_of_isBilimit {ι : Type*} [Fintype ι] {M : ι → X.Modules} {b : Bicone M}
    (hb : b.IsBilimit) (n : ℕ) [∀ i, FiniteDimensional k ((M i).H n)] :
    b.pt.finrankH k n = ∑ i, (M i).finrankH k n := by
  classical
  rw [finrankH, (H.isBilimitLinearEquiv k hb n).finrank_eq, Module.finrank_pi_fintype]
  rfl

end Modules

end Field

end AlgebraicGeometry.Scheme
