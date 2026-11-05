import Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechBaseChange

/-!
# Base change of sections over an affine open of the base

Consider a cartesian square of schemes
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` affine, and an affine open `W` of `T` with `B = Γ(T, W)`. For a quasi-coherent
`𝒪_X`-module `ℱ` and an affine open `U` of `X`, the map
`B ⊗[A] Γ(ℱ, U) ⟶ Γ(g'^* ℱ, g'⁻¹ U ⊓ f'⁻¹ W)`, `b ⊗ m ↦ b • (g'^* m)|`, is bijective
(`AlgebraicGeometry.Scheme.Modules.bijective_sectionsBaseChangeOpen`). This is
`AlgebraicGeometry.Scheme.Modules.bijective_sectionsModuleBaseChange` with the affine scheme `T`
replaced by an affine open of an arbitrary scheme `T`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe u

open CategoryTheory Limits TensorProduct Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules) (W : T.Opens)
  [Algebra Γ(S, ⊤) Γ(T, W)]
  (hg : algebraMap Γ(S, ⊤) Γ(T, W) = (g.appLE ⊤ W (le_top.trans g.preimage_top.ge)).hom)

include H hg in
/-- The functions on the base act compatibly on the sections of `ℱ` and on the restricted
sections of `g'^* ℱ`. -/
lemma presheaf_map_pullbackSection_smul {UX : X.Opens} {Z : Y.Opens}
    (hZ : Z ≤ g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ W) (a : Γ(S, ⊤)) (m : sectionsModule f ℱ UX) :
    ((pullback g').obj ℱ).presheaf.map (homOfLE (hZ.trans inf_le_left)).op
      (pullbackSection g' (a • m)) =
      f'.appLE W Z (hZ.trans inf_le_right) (algebraMap Γ(S, ⊤) Γ(T, W) a) •
        ((pullback g').obj ℱ).presheaf.map (homOfLE (hZ.trans inf_le_left)).op
          (pullbackSection g' m) := by
  change ((pullback g').obj ℱ).presheaf.map _ (pullbackSection g'
    (X.presheaf.map (homOfLE (le_top : UX ≤ ⊤)).op (f.appTop a) • (show Γ(ℱ, UX) from m))) = _
  rw [pullbackSection_smul, Scheme.Modules.map_smul, hg]
  congr 1
  have sectionSquare :
      f.appLE ⊤ UX (by simp) ≫ g'.appLE UX Z (hZ.trans inf_le_left) =
        g.appLE ⊤ W (by simp) ≫ f'.appLE W Z (hZ.trans inf_le_right) := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, H.w]
  exact congrArg (fun sectionMap : Γ(S, ⊤) ⟶ Γ(Y, Z) ↦ sectionMap a) sectionSquare

/-- The pullback of sections `Γ(ℱ, U) ⟶ Γ(g'^* ℱ, Z)` for `Z ≤ g'⁻¹ U`, as an additive map. -/
noncomputable def pullbackSectionRestrictAddHom {UX : X.Opens} {Z : Y.Opens}
    (hZ : Z ≤ g' ⁻¹ᵁ UX) : sectionsModule f ℱ UX →+ Γ((pullback g').obj ℱ, Z) where
  toFun m := ((pullback g').obj ℱ).presheaf.map (homOfLE hZ).op (pullbackSection g' m)
  map_zero' := by
    change ((pullback g').obj ℱ).presheaf.map (homOfLE hZ).op
      (pullbackSection g' (0 : Γ(ℱ, UX))) = 0
    rw [show pullbackSection g' (0 : Γ(ℱ, UX)) = 0 from
      map_zero (((pullbackPushforwardAdjunction g').unit.app ℱ).app UX).hom, map_zero]
  map_add' m m' := by
    change ((pullback g').obj ℱ).presheaf.map (homOfLE hZ).op
      (pullbackSection g' ((show Γ(ℱ, UX) from m) + (show Γ(ℱ, UX) from m'))) = _
    rw [pullbackSection_add g' (moduleSheaf := ℱ) (openSubset := UX), map_add]

omit [Algebra Γ(S, ⊤) Γ(T, W)] in
lemma pullbackSectionRestrictAddHom_apply {UX : X.Opens} {Z : Y.Opens} (hZ : Z ≤ g' ⁻¹ᵁ UX)
    (m : sectionsModule f ℱ UX) :
    pullbackSectionRestrictAddHom (f := f) ℱ hZ m =
      ((pullback g').obj ℱ).presheaf.map (homOfLE hZ).op (pullbackSection g' m) :=
  rfl

/-- The additive map `B ⊗[A] Γ(ℱ, U) ⟶ Γ(g'^* ℱ, Z)`, `b ⊗ m ↦ b • (g'^* m)|_Z`, for an open
`Z ≤ g'⁻¹ U ⊓ f'⁻¹ W`, with `A = Γ(S, ⊤)` and `B = Γ(T, W)`. -/
noncomputable def sectionsBaseChangeOpen {UX : X.Opens} {Z : Y.Opens}
    (hZ : Z ≤ g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ W) :
    Γ(T, W) ⊗[Γ(S, ⊤)] sectionsModule f ℱ UX →+ Γ((pullback g').obj ℱ, Z) :=
  TensorProduct.liftAddHom (R := Γ(S, ⊤)) (M := Γ(T, W)) (N := sectionsModule f ℱ UX)
    (P := Γ((pullback g').obj ℱ, Z))
    { toFun b := (DistribSMul.toAddMonoidHom _ (f'.appLE W Z (hZ.trans inf_le_right) b)).comp
        (pullbackSectionRestrictAddHom (f := f) ℱ (hZ.trans inf_le_left))
      map_zero' := AddMonoidHom.ext fun m ↦ by
        simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply, map_zero,
          zero_smul, AddMonoidHom.zero_apply]
      map_add' b b' := AddMonoidHom.ext fun m ↦ by
        simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply, map_add,
          add_smul, AddMonoidHom.add_apply] }
    (fun a b m ↦ by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.comp_apply,
        DistribSMul.toAddMonoidHom_apply]
      rw [pullbackSectionRestrictAddHom_apply, pullbackSectionRestrictAddHom_apply,
        presheaf_map_pullbackSection_smul H ℱ W hg hZ, smul_smul, Algebra.smul_def, map_mul,
        mul_comm])

lemma sectionsBaseChangeOpen_tmul {UX : X.Opens} {Z : Y.Opens}
    (hZ : Z ≤ g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ W) (b : Γ(T, W)) (m : sectionsModule f ℱ UX) :
    sectionsBaseChangeOpen H ℱ W hg hZ (b ⊗ₜ m) =
      f'.appLE W Z (hZ.trans inf_le_right) b •
        ((pullback g').obj ℱ).presheaf.map (homOfLE (hZ.trans inf_le_left)).op
          (pullbackSection g' m) :=
  TensorProduct.liftAddHom_tmul (R := Γ(S, ⊤)) (M := Γ(T, W)) (N := sectionsModule f ℱ UX)
    (P := Γ((pullback g').obj ℱ, Z)) _ _ _ _

/-- **Base change of sections over an affine open of the base.** If `S` is affine, `ℱ` is
quasi-coherent, `W` an affine open of `T` and `U` an affine open of `X`, the map
`Γ(T, W) ⊗[Γ(S, ⊤)] Γ(ℱ, U) ⟶ Γ(g'^* ℱ, g'⁻¹ U ⊓ f'⁻¹ W)` is bijective. -/
theorem bijective_sectionsBaseChangeOpen [IsAffine S]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (hW : IsAffineOpen W)
    {UX : X.Opens} (hUX : IsAffineOpen UX) :
    Function.Bijective (sectionsBaseChangeOpen H ℱ W hg (le_refl (g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ W))) := by
  set Z := g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ W
  have hUST : W ≤ g ⁻¹ᵁ ⊤ := by simp
  have hUSX : UX ≤ f ⁻¹ᵁ ⊤ := by simp
  have : IsAffine (⊤ : S.Opens).toScheme := isAffineOpen_top S
  have : IsAffine W.toScheme := hW
  have : IsAffine UX.toScheme := hUX
  have hZ : IsAffineOpen Z :=
    .of_isIso (Scheme.Hom.isPullback_resLE H hUST hUSX rfl).isoPullback.hom
  let : Algebra Γ(S, ⊤) Γ(X, UX) := (f.appLE ⊤ UX (by simp)).hom.toAlgebra
  let : Algebra Γ(X, UX) Γ(Y, Z) := (g'.appLE UX Z inf_le_left).hom.toAlgebra
  let : Module Γ(X, UX) (sectionsModule f ℱ UX) := inferInstanceAs (Module Γ(X, UX) Γ(ℱ, UX))
  have : IsScalarTower Γ(S, ⊤) Γ(X, UX) (sectionsModule f ℱ UX) := ⟨fun a r m ↦ by
    change (f.appLE ⊤ UX _ a * r) • (m : Γ(ℱ, UX)) =
      X.presheaf.map (homOfLE (le_top : UX ≤ ⊤)).op (f.appTop a) • r • (m : Γ(ℱ, UX))
    rw [mul_smul]
    rfl⟩
  obtain ⟨e₁, he₁⟩ := exists_linearEquiv_pullback_sections g' ℱ hUX hZ inf_le_left
  have hpush := (isIso_pushoutSection_iff H hUST hUSX (rfl : Z = _)).mp
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX rfl (isAffineOpen_top S) hW hUX)
  let ε := hpush.flip.tensorEquiv (baseAlgebra' := Γ(X, UX))
    (extensionAlgebra := Γ(T, W)) rfl (by rw [hg]; rfl)
  have hε (r : Γ(X, UX)) (b : Γ(T, W)) : ε (r ⊗ₜ b) = g'.appLE UX Z inf_le_left r *
      f'.appLE W Z inf_le_right b :=
    hpush.flip.tensorEquiv_tmul _ _ r b
  let εₗ : Γ(X, UX) ⊗[Γ(S, ⊤)] Γ(T, W) ≃ₗ[Γ(X, UX)] Γ(Y, Z) :=
    { ε.toAddEquiv with
      map_smul' r x := by
        change ε (r • x) = r • ε x
        rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, hε, map_one, mul_one, Algebra.smul_def]
        rfl }
  let Φ : Γ(T, W) ⊗[Γ(S, ⊤)] sectionsModule f ℱ UX ≃+ Γ((pullback g').obj ℱ, Z) :=
    (TensorProduct.comm Γ(S, ⊤) Γ(T, W) (sectionsModule f ℱ UX)).toAddEquiv.trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(S, ⊤) Γ(X, UX) Γ(X, UX)
        (sectionsModule f ℱ UX) Γ(T, W)).symm.toAddEquiv.trans
      ((εₗ.lTensor (sectionsModule f ℱ UX)).toAddEquiv.trans
      ((TensorProduct.comm Γ(X, UX) (sectionsModule f ℱ UX) Γ(Y, Z)).toAddEquiv.trans
        e₁.toAddEquiv)))
  suffices h : ∀ x, sectionsBaseChangeOpen H ℱ W hg (le_refl Z) x = Φ x by
    have : ⇑(sectionsBaseChangeOpen H ℱ W hg (le_refl Z)) = ⇑Φ := funext h
    rw [this]
    exact Φ.bijective
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b m =>
    rw [sectionsBaseChangeOpen_tmul]
    change _ = e₁ (TensorProduct.comm _ _ _ (εₗ.lTensor _
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(S, ⊤) Γ(X, UX) Γ(X, UX)
        (sectionsModule f ℱ UX) Γ(T, W)).symm (m ⊗ₜ b))))
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.lTensor_tmul,
      TensorProduct.comm_tmul]
    change _ = e₁ (ε (1 ⊗ₜ b) ⊗ₜ (m : Γ(ℱ, UX)))
    rw [hε, map_one, one_mul, ← mul_one (f'.appLE W Z _ b), ← smul_eq_mul,
      ← TensorProduct.smul_tmul', e₁.map_smul, he₁, smul_eq_mul, mul_one]

/-- The base change of sections is compatible with restriction. -/
lemma presheaf_map_sectionsBaseChangeOpen {UX UX' : X.Opens} (hU : UX' ≤ UX) {Z Z' : Y.Opens}
    (hZ : Z ≤ g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ W) (hZ' : Z' ≤ g' ⁻¹ᵁ UX' ⊓ f' ⁻¹ᵁ W) (hZZ : Z' ≤ Z)
    (x : Γ(T, W) ⊗[Γ(S, ⊤)] sectionsModule f ℱ UX) :
    ((pullback g').obj ℱ).presheaf.map (homOfLE hZZ).op (sectionsBaseChangeOpen H ℱ W hg hZ x) =
      sectionsBaseChangeOpen H ℱ W hg hZ'
        ((sectionsModuleRestrict f ℱ hU).baseChange Γ(T, W) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m =>
    rw [LinearMap.baseChange_tmul, sectionsBaseChangeOpen_tmul, sectionsBaseChangeOpen_tmul,
      Scheme.Modules.map_smul, sectionsModuleRestrict_apply,
      pullbackSection_map g' (M := ℱ) hU m]
    congr 1
    · rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

/-- The base-change map is linear over functions on the new base open. -/
lemma sectionsBaseChangeOpen_smul {UX : X.Opens} {Z : Y.Opens} (hZ : Z ≤ g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ W)
    (b : Γ(T, W)) (w : Γ(T, W) ⊗[Γ(S, ⊤)] sectionsModule f ℱ UX) :
    sectionsBaseChangeOpen H ℱ W hg hZ (b • w) =
      f'.appLE W Z (hZ.trans inf_le_right) b • sectionsBaseChangeOpen H ℱ W hg hZ w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul b' m =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, sectionsBaseChangeOpen_tmul,
      sectionsBaseChangeOpen_tmul, map_mul, mul_smul]

end AlgebraicGeometry.Scheme.Modules
