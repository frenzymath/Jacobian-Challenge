import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Unit ideals at finitely generated stages

An ideal that becomes the unit ideal in a filtered union of subalgebras already
becomes the unit ideal at a finitely generated stage, also after tensor product.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

namespace Subalgebra

variable {R₀ A : Type*} [CommRing R₀] [CommRing A] [Algebra R₀ A]

/-- An ideal of a finitely generated subalgebra `R` of `A` generating the unit ideal of `A`
generates the unit ideal of some finitely generated subalgebra containing `R`. -/
theorem exists_map_inclusion_eq_top {R : Subalgebra R₀ A} (hR : R.FG) (J : Ideal R)
    (hJ : J.map R.val = ⊤) :
    ∃ (R' : Subalgebra R₀ A) (h : R ≤ R'), R'.FG ∧ J.map (inclusion h) = ⊤ := by
  classical
  have hm {R' R'' : Subalgebra R₀ A} (h : R ≤ R') (h' : R' ≤ R'') (y : R')
      (hy : y ∈ J.map (inclusion h)) : inclusion h' y ∈ J.map (inclusion (h.trans h')) := by
    refine (Ideal.map_le_iff_le_comap.mpr ?_ :
      J.map (inclusion h) ≤ (J.map (inclusion (h.trans h'))).comap (inclusion h')) hy
    intro j hj
    rw [Ideal.mem_comap]
    exact Ideal.mem_map_of_mem (inclusion (h.trans h')) hj
  have key : ∀ x ∈ J.map R.val, ∃ (R' : Subalgebra R₀ A) (h : R ≤ R'), R'.FG ∧
      ∃ y ∈ J.map (inclusion h), (y : A) = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact ⟨R, le_rfl, hR, inclusion le_rfl j, Ideal.mem_map_of_mem _ hj, rfl⟩
    | zero => exact ⟨R, le_rfl, hR, 0, zero_mem _, rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨R₁, h₁, hR₁, y₁, hy₁, rfl⟩ := hx
      obtain ⟨R₂, h₂, hR₂, y₂, hy₂, rfl⟩ := hy
      refine ⟨R₁ ⊔ R₂, h₁.trans le_sup_left, hR₁.sup hR₂,
        inclusion le_sup_left y₁ + inclusion le_sup_right y₂,
        add_mem (hm h₁ le_sup_left y₁ hy₁) (hm h₂ le_sup_right y₂ hy₂), ?_⟩
      simp
    | smul a x _ hx =>
      obtain ⟨R₁, h₁, hR₁, y₁, hy₁, rfl⟩ := hx
      let R₂ := R₁ ⊔ Algebra.adjoin R₀ (({a} : Finset A) : Set A)
      have h₂ : R₁ ≤ R₂ := le_sup_left
      have ha : a ∈ R₂ :=
        (le_sup_right : Algebra.adjoin R₀ _ ≤ R₂) (Algebra.subset_adjoin (by simp))
      refine ⟨R₂, h₁.trans h₂, hR₁.sup (fg_adjoin_finset _), ⟨a, ha⟩ * inclusion h₂ y₁,
        Ideal.mul_mem_left _ _ (hm h₁ h₂ y₁ hy₁), ?_⟩
      simp
  obtain ⟨R', h, hR', y, hy, hy1⟩ := key 1 (hJ ▸ Submodule.mem_top)
  refine ⟨R', h, hR', (Ideal.eq_top_iff_one _).mpr ?_⟩
  convert hy
  exact Subtype.ext hy1.symm

variable {S₀ : Type*} [CommRing S₀] [Algebra R₀ S₀]

/-- An ideal of `R ⊗[R₀] S₀`, for a finitely generated subalgebra `R` of `A`, generating the unit
ideal of `A ⊗[R₀] S₀` generates the unit ideal of `R' ⊗[R₀] S₀` for some finitely generated
subalgebra `R'` containing `R`. -/
theorem exists_map_tensorProduct_inclusion_eq_top {R : Subalgebra R₀ A} (hR : R.FG)
    (J : Ideal (R ⊗[R₀] S₀)) (hJ : J.map (Algebra.TensorProduct.map R.val (AlgHom.id R₀ S₀)) = ⊤) :
    ∃ (R' : Subalgebra R₀ A) (h : R ≤ R'), R'.FG ∧
      J.map (Algebra.TensorProduct.map (inclusion h) (AlgHom.id R₀ S₀)) = ⊤ := by
  classical
  let ι (R : Subalgebra R₀ A) : R ⊗[R₀] S₀ →ₐ[R₀] A ⊗[R₀] S₀ :=
    Algebra.TensorProduct.map R.val (AlgHom.id R₀ S₀)
  let κ {R R' : Subalgebra R₀ A} (h : R ≤ R') : R ⊗[R₀] S₀ →ₐ[R₀] R' ⊗[R₀] S₀ :=
    Algebra.TensorProduct.map (inclusion h) (AlgHom.id R₀ S₀)
  have hικ {R R' : Subalgebra R₀ A} (h : R ≤ R') (x) : ι R' (κ h x) = ι R x := by
    rw [← AlgHom.comp_apply]
    congr 1
    ext <;> rfl
  have hκκ {R R' R'' : Subalgebra R₀ A} (h : R ≤ R') (h' : R' ≤ R'') (x : R ⊗[R₀] S₀) :
      κ h' (κ h x) = κ (h.trans h') x := by
    rw [← AlgHom.comp_apply]
    congr 1
    ext <;> rfl
  have hlin (R : Subalgebra R₀ A) : (ι R).toLinearMap = R.val.toLinearMap.rTensor S₀ :=
    TensorProduct.ext' fun _ _ ↦ rfl
  have hlin' {R R' : Subalgebra R₀ A} (h : R ≤ R') :
      (κ h).toLinearMap = (inclusion h).toLinearMap.rTensor S₀ :=
    TensorProduct.ext' fun _ _ ↦ rfl
  have hm {R' R'' : Subalgebra R₀ A} (h : R ≤ R') (h' : R' ≤ R'') (y : R' ⊗[R₀] S₀)
      (hy : y ∈ J.map (κ h)) : κ h' y ∈ J.map (κ (h.trans h')) := by
    refine (Ideal.map_le_iff_le_comap.mpr ?_ :
      J.map (κ h) ≤ (J.map (κ (h.trans h'))).comap (κ h')) hy
    intro j hj
    change κ h' (κ h j) ∈ J.map (κ (h.trans h'))
    rw [hκκ]
    exact Ideal.mem_map_of_mem _ hj
  have key : ∀ x ∈ J.map (ι R), ∃ (R' : Subalgebra R₀ A) (h : R ≤ R'), R'.FG ∧
      ∃ y ∈ J.map (κ h), ι R' y = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact ⟨R, le_rfl, hR, κ (le_refl R) j, Ideal.mem_map_of_mem _ hj, hικ _ _⟩
    | zero => exact ⟨R, le_rfl, hR, 0, zero_mem _, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨R₁, h₁, hR₁, y₁, hy₁, rfl⟩ := hx
      obtain ⟨R₂, h₂, hR₂, y₂, hy₂, rfl⟩ := hy
      exact ⟨R₁ ⊔ R₂, h₁.trans le_sup_left, hR₁.sup hR₂,
        κ (le_sup_left : R₁ ≤ R₁ ⊔ R₂) y₁ + κ (le_sup_right : R₂ ≤ R₁ ⊔ R₂) y₂,
        add_mem (hm h₁ le_sup_left y₁ hy₁) (hm h₂ le_sup_right y₂ hy₂), by
          rw [map_add, hικ, hικ]⟩
    | smul a x _ hx =>
      obtain ⟨R₁, h₁, hR₁, y₁, hy₁, rfl⟩ := hx
      obtain ⟨R₂, hR₂, ⟨a', ha'⟩⟩ := TensorProduct.Algebra.exists_of_fg (N := S₀) a
      refine ⟨R₁ ⊔ R₂, h₁.trans le_sup_left, hR₁.sup hR₂,
        κ (le_sup_right : R₂ ≤ R₁ ⊔ R₂) a' * κ (le_sup_left : R₁ ≤ R₁ ⊔ R₂) y₁,
        Ideal.mul_mem_left _ _ (hm h₁ _ y₁ hy₁), ?_⟩
      rw [map_mul, hικ, hικ, smul_eq_mul, ← ha', ← hlin]
      rfl
  obtain ⟨R', h, hR', y, hy, hy1⟩ := key 1 (hJ ▸ Submodule.mem_top)
  have hy1' : R'.val.toLinearMap.rTensor S₀ y = R'.val.toLinearMap.rTensor S₀ 1 := by
    rw [← hlin, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, hy1, map_one]
  obtain ⟨R'', h', hR'', hy''⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hR' hy1'
  refine ⟨R'', h.trans h', hR'', (Ideal.eq_top_iff_one _).mpr ?_⟩
  have := hm h h' y hy
  rwa [← AlgHom.toLinearMap_apply, hlin', hy'', ← hlin', AlgHom.toLinearMap_apply,
    map_one] at this

end Subalgebra
