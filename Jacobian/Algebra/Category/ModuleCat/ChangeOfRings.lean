import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Tensor products and extension of scalars
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe schemeUniverse
open CategoryTheory TensorProduct

/-- For an `R`-algebra `S`, `S ⊗[R] N` is `(ModuleCat.extendScalars (algebraMap R S)).obj N`. -/
noncomputable def ModuleCat.tensorEquivExtendScalars (R S : Type schemeUniverse) [CommRing R]
    [CommRing S] [Algebra R S] (N : ModuleCat.{schemeUniverse} R) :
    S ⊗[R] N ≃ₗ[S] (ModuleCat.extendScalars (algebraMap R S)).obj N := by
  let T := (ModuleCat.extendScalars (algebraMap R S)).obj N
  let S' := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let toFun : S ⊗[R] N →ₗ[R] TensorProduct R S' N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S' N s
        map_add' s s' := (TensorProduct.mk R S' N).map_add s s'
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S' N) (Algebra.smul_def r s)).trans
            ((TensorProduct.mk R S' N).map_smul r (s : S')) }
  let invFun : TensorProduct R S' N →ₗ[R] S ⊗[R] N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S N (show S from s)
        map_add' s s' := (TensorProduct.mk R S N).map_add (show S from s) (show S from s')
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S N) (Algebra.smul_def r (show S from s)).symm).trans
            ((TensorProduct.mk R S N).map_smul r (show S from s)) }
  have h₁ : ∀ x, invFun (toFun x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have h₂ : ∀ x, toFun (invFun x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  exact
    { toFun := toFun
      invFun := invFun
      map_add' := toFun.map_add
      map_smul' s x := by
        induction x using TensorProduct.induction_on with
        | zero => exact (map_zero toFun).trans (show (0 : T) = s • (0 : T) from (smul_zero s).symm)
        | tmul s' n => rfl
        | add x y hx hy =>
          rw [smul_add, map_add, hx, hy, map_add]
          exact (smul_add s _ _).symm
      left_inv := h₁
      right_inv := h₂ }

lemma ModuleCat.tensorEquivExtendScalars_tmul (R S : Type schemeUniverse) [CommRing R]
    [CommRing S] [Algebra R S] (N : ModuleCat.{schemeUniverse} R) (s : S) (n : N) :
    ModuleCat.tensorEquivExtendScalars R S N (s ⊗ₜ n) =
      TensorProduct.tmul R
        (M := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S))
        s n :=
  rfl

/-- The tensor description of scalar extension is natural in the module. -/
lemma ModuleCat.tensorEquivExtendScalars_naturality (R S : Type schemeUniverse) [CommRing R]
    [CommRing S] [Algebra R S] {M N : ModuleCat.{schemeUniverse} R} (φ : M ⟶ N)
    (element : S ⊗[R] M) :
    (ModuleCat.extendScalars (algebraMap R S)).map φ
        (ModuleCat.tensorEquivExtendScalars R S M element) =
      ModuleCat.tensorEquivExtendScalars R S N (φ.hom.baseChange S element) := by
  induction element using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add left right left_eq right_eq => simp only [map_add, left_eq, right_eq]
  | tmul scalar coefficient =>
    rw [ModuleCat.tensorEquivExtendScalars_tmul, ModuleCat.ExtendScalars.map_tmul,
      LinearMap.baseChange_tmul, ModuleCat.tensorEquivExtendScalars_tmul]

/-- The inverse tensor comparison intertwines scalar extension and tensoring a linear map. -/
lemma ModuleCat.tensorEquivExtendScalars_symm_naturality (R S : Type schemeUniverse) [CommRing R]
    [CommRing S] [Algebra R S] {M N : ModuleCat.{schemeUniverse} R} (φ : M ⟶ N)
    (element : (ModuleCat.extendScalars (algebraMap R S)).obj M) :
    (ModuleCat.tensorEquivExtendScalars R S N).symm
        ((ModuleCat.extendScalars (algebraMap R S)).map φ element) =
      φ.hom.baseChange S ((ModuleCat.tensorEquivExtendScalars R S M).symm element) := by
  obtain ⟨element, rfl⟩ := (ModuleCat.tensorEquivExtendScalars R S M).surjective element
  rw [ModuleCat.tensorEquivExtendScalars_naturality, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]
