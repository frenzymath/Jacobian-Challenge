import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Flat base change of `Ext`-groups along actions on the target

Let `C` be an abelian category, `A ⟶ B` a flat map of commutative rings, `F` an object of `C`
with an action `ρ : A →+* End F` of `A`, and `G` an object with an action `σ : B →+* End G` of
`B`, together with a morphism `η : F ⟶ G` intertwining the two actions. For every object `P`
the groups `Ext P F n` and `Ext P G n` are modules over `A` and `B`
(`CategoryTheory.Abelian.Ext.WithAction`), and there is a `B`-linear base change map
```
  B ⊗[A] Ext P F n ⟶ Ext P G n,   b ⊗ x ↦ b • η_* x
```
(`CategoryTheory.Abelian.Ext.WithAction.baseChange`). We show that the class of objects `P` for
which these maps are bijective in all degrees is closed under isomorphisms, binary biproducts and
cokernels of monomorphisms between its members. The last point is the five lemma applied to the
long exact sequences of `Ext`-groups, the first of which stays exact after `B ⊗[A] -` since `B`
is flat over `A`.

This is the algebraic core of flat base change for the cohomology of quasi-coherent modules,
where `P` runs through the free abelian sheaves `ℤ_U` on opens `U` and a short exact sequence
`0 ⟶ ℤ_{U ∩ V} ⟶ ℤ_U ⊕ ℤ_V ⟶ ℤ_{U ∪ V} ⟶ 0` gives the Mayer–Vietoris sequence.

## Main statements

- `CategoryTheory.Abelian.Ext.WithAction.bijective_baseChange_of_iso`,
  `CategoryTheory.Abelian.Ext.WithAction.bijective_baseChange_biprod`,
  `CategoryTheory.Abelian.Ext.WithAction.bijective_baseChange_of_shortExact`: the closure
  properties of the objects for which the base change maps are bijective.
-/

universe w v u

open CategoryTheory Limits TensorProduct

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- In degree `0`, postcomposition with `mk₀ φ` is composition with `φ`. -/
lemma addEquiv₀_comp_mk₀ {P F G : C} (x : Ext P F 0) (φ : F ⟶ G) :
    addEquiv₀ (x.comp (mk₀ φ) (add_zero 0)) = addEquiv₀ x ≫ φ := by
  apply (mk₀_bijective P G).injective
  rw [mk₀_addEquiv₀_apply, ← mk₀_comp_mk₀, mk₀_addEquiv₀_apply]

section Action

variable {A : Type*} [CommRing A] {F : C} (ρ : A →+* End F)

/-- `Ext P F n` with the action of `A` induced by an action `ρ : A →+* End F` of `A` on `F`,
`a • x = ρ(a)_* x`. -/
@[nolint unusedArguments]
def WithAction (_ρ : A →+* End F) (P : C) (n : ℕ) : Type w := Ext P F n

namespace WithAction

noncomputable instance (P : C) (n : ℕ) : AddCommGroup (WithAction ρ P n) :=
  inferInstanceAs (AddCommGroup (Ext P F n))

/-- The action of `A` on `Ext P F n` induced by `ρ`, as a ring homomorphism to the additive
endomorphisms. -/
noncomputable def smulEnd (P : C) (n : ℕ) : A →+* AddMonoid.End (Ext P F n) where
  toFun a := (mk₀ (ρ a)).postcomp P (add_zero n)
  map_one' := by
    ext x
    change x.comp (mk₀ (ρ 1)) (add_zero n) = x
    rw [map_one, End.one_def]
    exact comp_mk₀_id x
  map_mul' a b := by
    ext x
    change x.comp (mk₀ (ρ (a * b))) (add_zero n) =
      (x.comp (mk₀ (ρ b)) (add_zero n)).comp (mk₀ (ρ a)) (add_zero n)
    rw [map_mul, End.mul_def, comp_assoc_of_third_deg_zero, mk₀_comp_mk₀]
  map_zero' := by
    ext x
    change x.comp (mk₀ (ρ 0)) (add_zero n) = 0
    rw [map_zero, mk₀_zero]
    exact comp_zero _ _ _ _ _
  map_add' a b := by
    ext x
    change x.comp (mk₀ (ρ (a + b))) (add_zero n) =
      x.comp (mk₀ (ρ a)) (add_zero n) + x.comp (mk₀ (ρ b)) (add_zero n)
    rw [map_add, mk₀_add]
    exact comp_add _ _ _ _

noncomputable instance (P : C) (n : ℕ) : Module A (WithAction ρ P n) :=
  Module.compHom (Ext P F n) (smulEnd ρ P n)

/-- The identification of `WithAction ρ P n` with `Ext P F n`. -/
noncomputable def toExt {P : C} {n : ℕ} : WithAction ρ P n ≃+ Ext P F n := AddEquiv.refl _

lemma toExt_smul {P : C} {n : ℕ} (a : A) (x : WithAction ρ P n) :
    toExt ρ (a • x) = (toExt ρ x).comp (mk₀ (ρ a)) (add_zero n) :=
  rfl

/-- Precomposition with `α : Ext P P' m` is `A`-linear. -/
noncomputable def precompₗ {P P' : C} {m : ℕ} (α : Ext P P' m) {n n' : ℕ} (h : m + n = n') :
    WithAction ρ P' n →ₗ[A] WithAction ρ P n' where
  toFun x := (toExt ρ).symm (α.comp (toExt ρ x) h)
  map_add' x y := comp_add α (toExt ρ x) (toExt ρ y) h
  map_smul' a x := (comp_assoc_of_third_deg_zero α (toExt ρ x) (mk₀ (ρ a)) h).symm

lemma toExt_precompₗ {P P' : C} {m : ℕ} (α : Ext P P' m) {n n' : ℕ} (h : m + n = n')
    (x : WithAction ρ P' n) : toExt ρ (precompₗ ρ α h x) = α.comp (toExt ρ x) h :=
  rfl

/-- Precomposition with an isomorphism, as an `A`-linear equivalence. -/
noncomputable def precompLinearEquiv {P P' : C} (e : P ≅ P') (n : ℕ) :
    WithAction ρ P' n ≃ₗ[A] WithAction ρ P n :=
  LinearEquiv.ofLinearMap (precompₗ ρ (mk₀ e.hom) (zero_add n))
    (precompₗ ρ (mk₀ e.inv) (zero_add n))
    (LinearMap.ext fun x ↦ by
      change (mk₀ e.hom).comp ((mk₀ e.inv).comp (toExt ρ x) (zero_add n)) (zero_add n) =
        toExt ρ x
      rw [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, e.hom_inv_id, mk₀_id_comp])
    (LinearMap.ext fun x ↦ by
      change (mk₀ e.inv).comp ((mk₀ e.hom).comp (toExt ρ x) (zero_add n)) (zero_add n) =
        toExt ρ x
      rw [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, e.inv_hom_id, mk₀_id_comp])

section BaseChange

variable {B : Type*} [CommRing B] [Algebra A B] {G : C} (σ : B →+* End G) (η : F ⟶ G)
  (hη : ∀ a, ρ a ≫ η = η ≫ σ (algebraMap A B a))

/-- The additive map underlying `CategoryTheory.Abelian.Ext.WithAction.baseChange`. -/
noncomputable def baseChangeAddHom (P : C) (n : ℕ) :
    B ⊗[A] WithAction ρ P n →+ WithAction σ P n :=
  TensorProduct.liftAddHom
    { toFun b := ((mk₀ (η ≫ σ b)).postcomp P (add_zero n)).comp (toExt ρ).toAddMonoidHom
      map_zero' := by
        ext x
        change (toExt ρ x).comp (mk₀ (η ≫ σ 0)) (add_zero n) = 0
        rw [map_zero, Limits.comp_zero, mk₀_zero]
        exact Ext.comp_zero _ _ _ _ _
      map_add' b b' := by
        ext x
        change (toExt ρ x).comp (mk₀ (η ≫ σ (b + b'))) (add_zero n) =
          (toExt ρ x).comp (mk₀ (η ≫ σ b)) (add_zero n) +
            (toExt ρ x).comp (mk₀ (η ≫ σ b')) (add_zero n)
        rw [map_add, Preadditive.comp_add, mk₀_add]
        exact Ext.comp_add _ _ _ _ }
    (fun a b x ↦ by
      change (toExt ρ x).comp (mk₀ (η ≫ σ (a • b))) (add_zero n) =
        ((toExt ρ x).comp (mk₀ (ρ a)) (add_zero n)).comp (mk₀ (η ≫ σ b)) (add_zero n)
      rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, ← Category.assoc, hη, Algebra.smul_def,
        mul_comm, map_mul, End.mul_def, Category.assoc])

include hη in
lemma baseChangeAddHom_tmul (P : C) (n : ℕ) (b : B) (x : WithAction ρ P n) :
    toExt σ (baseChangeAddHom ρ σ η hη P n (b ⊗ₜ x)) =
      (toExt ρ x).comp (mk₀ (η ≫ σ b)) (add_zero n) :=
  rfl

/-- **Base change of `Ext`-groups.** The `B`-linear map `B ⊗[A] Ext P F n ⟶ Ext P G n`,
`b ⊗ x ↦ b • η_* x`. -/
noncomputable def baseChange (P : C) (n : ℕ) :
    B ⊗[A] WithAction ρ P n →ₗ[B] WithAction σ P n where
  toAddHom := (baseChangeAddHom ρ σ η hη P n).toAddHom
  map_smul' c z := by
    change baseChangeAddHom ρ σ η hη P n (c • z) = c • baseChangeAddHom ρ σ η hη P n z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | add z z' hz hz' => rw [smul_add, map_add, map_add, hz, hz', smul_add]
    | tmul b x =>
      rw [TensorProduct.smul_tmul']
      change (toExt ρ x).comp (mk₀ (η ≫ σ (c • b))) (add_zero n) =
        ((toExt ρ x).comp (mk₀ (η ≫ σ b)) (add_zero n)).comp (mk₀ (σ c)) (add_zero n)
      rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, smul_eq_mul, map_mul, End.mul_def,
        Category.assoc]

lemma baseChange_tmul (P : C) (n : ℕ) (b : B) (x : WithAction ρ P n) :
    toExt σ (baseChange ρ σ η hη P n (b ⊗ₜ x)) =
      (toExt ρ x).comp (mk₀ (η ≫ σ b)) (add_zero n) :=
  rfl

/-- The base change maps commute with precomposition. -/
lemma baseChange_comp_lTensor_precompₗ {P P' : C} {m : ℕ} (α : Ext P P' m) {n n' : ℕ}
    (h : m + n = n') :
    (baseChange ρ σ η hη P n').toAddMonoidHom.comp
        ((precompₗ ρ α h).lTensor B).toAddMonoidHom =
      (precompₗ σ α h).toAddMonoidHom.comp (baseChange ρ σ η hη P' n).toAddMonoidHom := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul b x =>
    change (α.comp (toExt ρ x) h).comp (mk₀ (η ≫ σ b)) (add_zero n') =
      α.comp ((toExt ρ x).comp (mk₀ (η ≫ σ b)) (add_zero n)) h
    exact comp_assoc_of_third_deg_zero _ _ _ _

lemma baseChange_lTensor_precompₗ_apply {P P' : C} {m : ℕ} (α : Ext P P' m) {n n' : ℕ}
    (h : m + n = n') (z : B ⊗[A] WithAction ρ P' n) :
    baseChange ρ σ η hη P n' ((precompₗ ρ α h).lTensor B z) =
      precompₗ σ α h (baseChange ρ σ η hη P' n z) :=
  DFunLike.congr_fun (baseChange_comp_lTensor_precompₗ ρ σ η hη α h) z

/-- The base change maps are bijective for an object isomorphic to one for which they are. -/
lemma bijective_baseChange_of_iso {P P' : C} (e : P ≅ P') {n : ℕ}
    (h : Function.Bijective (baseChange ρ σ η hη P n)) :
    Function.Bijective (baseChange ρ σ η hη P' n) := by
  have key : ⇑(precompLinearEquiv σ e n) ∘ ⇑(baseChange ρ σ η hη P' n) =
      ⇑(baseChange ρ σ η hη P n) ∘ ⇑((precompLinearEquiv ρ e n).lTensor B) :=
    funext fun z ↦ (baseChange_lTensor_precompₗ_apply ρ σ η hη (mk₀ e.hom) (zero_add n) z).symm
  refine (Function.Bijective.of_comp_iff' (precompLinearEquiv σ e n).bijective _).mp ?_
  rw [key]
  exact h.comp (LinearEquiv.bijective _)

/-- The base change maps are bijective for a binary biproduct of objects for which they are. -/
lemma bijective_baseChange_biprod {P₁ P₂ : C} {n : ℕ}
    (h₁ : Function.Bijective (baseChange ρ σ η hη P₁ n))
    (h₂ : Function.Bijective (baseChange ρ σ η hη P₂ n)) :
    Function.Bijective (baseChange ρ σ η hη (P₁ ⊞ P₂) n) := by
  let πF : WithAction ρ (P₁ ⊞ P₂) n →ₗ[A] WithAction ρ P₁ n × WithAction ρ P₂ n :=
    (precompₗ ρ (mk₀ biprod.inl) (zero_add n)).prod (precompₗ ρ (mk₀ biprod.inr) (zero_add n))
  have hπF : Function.Bijective πF := (biprodAddEquiv (Y := F) (n := n)).bijective
  let πG : WithAction σ (P₁ ⊞ P₂) n → WithAction σ P₁ n × WithAction σ P₂ n :=
    fun x ↦ (precompₗ σ (mk₀ biprod.inl) (zero_add n) x,
      precompₗ σ (mk₀ biprod.inr) (zero_add n) x)
  have hπG : Function.Bijective πG := (biprodAddEquiv (Y := G) (n := n)).bijective
  have key : πG ∘ ⇑(baseChange ρ σ η hη (P₁ ⊞ P₂) n) =
      Prod.map (baseChange ρ σ η hη P₁ n) (baseChange ρ σ η hη P₂ n) ∘
        ⇑(TensorProduct.prodRight A A B _ _) ∘ ⇑(πF.lTensor B) := by
    have hfst (z : B ⊗[A] WithAction ρ (P₁ ⊞ P₂) n) :
        (TensorProduct.prodRight A A B _ _ (πF.lTensor B z)).1 =
          (precompₗ ρ (mk₀ biprod.inl) (zero_add n)).lTensor B z := by
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero, Prod.fst_zero]
      | add z z' hz hz' => simp only [map_add, Prod.fst_add, hz, hz']
      | tmul b x => rfl
    have hsnd (z : B ⊗[A] WithAction ρ (P₁ ⊞ P₂) n) :
        (TensorProduct.prodRight A A B _ _ (πF.lTensor B z)).2 =
          (precompₗ ρ (mk₀ biprod.inr) (zero_add n)).lTensor B z := by
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero, Prod.snd_zero]
      | add z z' hz hz' => simp only [map_add, Prod.snd_add, hz, hz']
      | tmul b x => rfl
    funext z
    refine Prod.ext ?_ ?_
    · change _ = baseChange ρ σ η hη P₁ n (TensorProduct.prodRight A A B _ _ (πF.lTensor B z)).1
      rw [hfst, baseChange_lTensor_precompₗ_apply]
      rfl
    · change _ = baseChange ρ σ η hη P₂ n (TensorProduct.prodRight A A B _ _ (πF.lTensor B z)).2
      rw [hsnd, baseChange_lTensor_precompₗ_apply]
      rfl
  refine (Function.Bijective.of_comp_iff' hπG _).mp ?_
  rw [key]
  exact (h₁.prodMap h₂).comp ((LinearEquiv.bijective _).comp
    (LinearEquiv.lTensor B (LinearEquiv.ofBijective πF hπF)).bijective)

/-- Exactness of the rows of the long exact sequence of `Ext`-groups, in the form needed for the
five lemma. -/
lemma exact_precompₗ_mk₀_g_f {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (precompₗ ρ (mk₀ S.g) (zero_add n)) (precompₗ ρ (mk₀ S.f) (zero_add n)) :=
  (ShortComplex.ab_exact_iff_function_exact _).1 (contravariant_sequence_exact₂' hS F n)

lemma exact_precompₗ_mk₀_f_extClass {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (precompₗ ρ (mk₀ S.f) (zero_add n))
      (precompₗ ρ hS.extClass (add_comm 1 n)) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (contravariant_sequence_exact₁' hS F n (n + 1) (add_comm 1 n))

lemma exact_precompₗ_extClass_mk₀_g {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (precompₗ ρ hS.extClass (add_comm 1 n))
      (precompₗ ρ (mk₀ S.g) (zero_add (n + 1))) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (contravariant_sequence_exact₃' hS F n (n + 1) (add_comm 1 n))

variable [Module.Flat A B]

/-- **Two out of three for base change.** Let `0 ⟶ P₁ ⟶ P₂ ⟶ P₃ ⟶ 0` be short exact. If the
base change maps of `P₁` and `P₂` are bijective in all degrees, then so are those of `P₃`: this is
the five lemma for the long exact sequences of `Ext`-groups, the first one tensored with the flat
`A`-module `B`. -/
lemma bijective_baseChange_of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    (h₁ : ∀ n, Function.Bijective (baseChange ρ σ η hη S.X₁ n))
    (h₂ : ∀ n, Function.Bijective (baseChange ρ σ η hη S.X₂ n)) (n : ℕ) :
    Function.Bijective (baseChange ρ σ η hη S.X₃ n) := by
  have := hS.epi_g
  have hc {P P' : C} {m : ℕ} (α : Ext P P' m) {k k' : ℕ} (h : m + k = k') :=
    (baseChange_comp_lTensor_precompₗ ρ σ η hη α h).symm
  cases n with
  | zero =>
    exact AddMonoidHom.bijective_of_bijective_of_injective_of_left_exact
      (f₁ := ((precompₗ ρ (mk₀ S.g) (zero_add 0)).lTensor B).toAddMonoidHom)
      (f₂ := ((precompₗ ρ (mk₀ S.f) (zero_add 0)).lTensor B).toAddMonoidHom)
      (g₁ := (precompₗ σ (mk₀ S.g) (zero_add 0)).toAddMonoidHom)
      (g₂ := (precompₗ σ (mk₀ S.f) (zero_add 0)).toAddMonoidHom)
      (i₁ := (baseChange ρ σ η hη S.X₃ 0).toAddMonoidHom)
      (i₂ := (baseChange ρ σ η hη S.X₂ 0).toAddMonoidHom)
      (i₃ := (baseChange ρ σ η hη S.X₁ 0).toAddMonoidHom)
      (hc₁ := hc _ _) (hc₂ := hc _ _)
      (hf₁ := Module.Flat.lTensor_exact B (exact_precompₗ_mk₀_g_f ρ hS 0))
      (hg₁ := exact_precompₗ_mk₀_g_f σ hS 0) (hi₂ := h₂ 0) (hi₃ := (h₁ 0).1)
      (hf₀ := Module.Flat.lTensor_preserves_injective_linearMap _
        (precomp_mk₀_injective_of_epi F S.g))
      (hg₀ := precomp_mk₀_injective_of_epi G S.g)
  | succ n =>
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (f₁ := ((precompₗ ρ (mk₀ S.f) (zero_add n)).lTensor B).toAddMonoidHom)
      (f₂ := ((precompₗ ρ hS.extClass (add_comm 1 n)).lTensor B).toAddMonoidHom)
      (f₃ := ((precompₗ ρ (mk₀ S.g) (zero_add (n + 1))).lTensor B).toAddMonoidHom)
      (f₄ := ((precompₗ ρ (mk₀ S.f) (zero_add (n + 1))).lTensor B).toAddMonoidHom)
      (g₁ := (precompₗ σ (mk₀ S.f) (zero_add n)).toAddMonoidHom)
      (g₂ := (precompₗ σ hS.extClass (add_comm 1 n)).toAddMonoidHom)
      (g₃ := (precompₗ σ (mk₀ S.g) (zero_add (n + 1))).toAddMonoidHom)
      (g₄ := (precompₗ σ (mk₀ S.f) (zero_add (n + 1))).toAddMonoidHom)
      (i₁ := (baseChange ρ σ η hη S.X₂ n).toAddMonoidHom)
      (i₂ := (baseChange ρ σ η hη S.X₁ n).toAddMonoidHom)
      (i₃ := (baseChange ρ σ η hη S.X₃ (n + 1)).toAddMonoidHom)
      (i₄ := (baseChange ρ σ η hη S.X₂ (n + 1)).toAddMonoidHom)
      (i₅ := (baseChange ρ σ η hη S.X₁ (n + 1)).toAddMonoidHom)
      (hc₁ := hc _ _) (hc₂ := hc _ _) (hc₃ := hc _ _) (hc₄ := hc _ _)
      (hf₁ := Module.Flat.lTensor_exact B (exact_precompₗ_mk₀_f_extClass ρ hS n))
      (hf₂ := Module.Flat.lTensor_exact B (exact_precompₗ_extClass_mk₀_g ρ hS n))
      (hf₃ := Module.Flat.lTensor_exact B (exact_precompₗ_mk₀_g_f ρ hS (n + 1)))
      (hg₁ := exact_precompₗ_mk₀_f_extClass σ hS n)
      (hg₂ := exact_precompₗ_extClass_mk₀_g σ hS n)
      (hg₃ := exact_precompₗ_mk₀_g_f σ hS (n + 1))
      (hi₁ := (h₂ n).2) (hi₂ := h₁ n) (hi₄ := h₂ (n + 1)) (hi₅ := (h₁ (n + 1)).1)

end BaseChange

end WithAction

end Action

end CategoryTheory.Abelian.Ext
