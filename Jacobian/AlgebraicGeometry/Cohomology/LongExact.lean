import Jacobian.AlgebraicGeometry.Cohomology.Basic
import Jacobian.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Long exact cohomology and Euler characteristics

The exact underlying abelian-sheaf functor gives connecting maps for a short
exact sequence of module sheaves. Naturality makes these maps linear over
global functions. A finite-dimensional long exact sequence, vanishing in high
degrees, gives additivity of the Euler characteristic.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {S : ShortComplex X.Modules}

local instance preservesZeroMorphisms_toSheaf_modules :
    Functor.PreservesZeroMorphisms (C := X.Modules)
      (D := Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf) where
  map_zero := by intros; ext openSubset sectionValue; rfl

/-- The image of a short exact sequence of `𝒪_X`-modules among abelian sheaves is short exact,
since `SheafOfModules.toSheaf` is exact. -/
lemma shortExact_map_toSheaf (hS : S.ShortExact) : (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).ShortExact := by
  letI : PreservesFiniteLimits (C := X.Modules)
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf) :=
    inferInstanceAs (PreservesFiniteLimits (C := SheafOfModules.{u} X.ringCatSheaf)
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  letI : PreservesFiniteColimits (C := X.Modules)
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf) :=
    inferInstanceAs (PreservesFiniteColimits (C := SheafOfModules.{u} X.ringCatSheaf)
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
  exact hS.map_of_exact (SheafOfModules.toSheaf.{u} X.ringCatSheaf)

/-- The map induced on cohomology by `φ : M ⟶ N` is composition with the degree-`0` class of
`φ`. -/
lemma H.map_apply_eq_comp {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) (z : H M n) :
    H.map φ n z = Ext.comp (Y := (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj M) z (Ext.mk₀ ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map φ)) (add_zero n) :=
  rfl

/-- Multiplication by a global function `a` on `H^n(X, M)` is the map induced on cohomology by
multiplication by `a` on `M`. -/
lemma smul_H_eq_map (M : X.Modules) (n : ℕ) (a : Γ(X, ⊤)) (z : H M n) :
    a • z = H.map (smulHom M a) n z :=
  rfl

/-- The connecting map `δ : H^n(M₃) ⟶ H^{n+1}(M₁)` of the long exact cohomology sequence of a short
exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0`: composition with its extension class. -/
noncomputable def H.δ (hS : S.ShortExact) (n : ℕ) : H S.X₃ n →+ H S.X₁ (n + 1) :=
  (shortExact_map_toSheaf hS).extClass.postcomp _ rfl

lemma H.δ_apply (hS : S.ShortExact) (n : ℕ) (z : H S.X₃ n) :
    H.δ hS n z = Ext.comp (Y := (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj S.X₃) z (shortExact_map_toSheaf hS).extClass rfl :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The connecting map is linear over the global functions: multiplication by `a : Γ(X, 𝒪_X)`
is an endomorphism of the short exact sequence, and the extension class is natural. -/
lemma H.δ_smul (hS : S.ShortExact) (n : ℕ) (a : Γ(X, ⊤)) (z : H S.X₃ n) :
    H.δ hS n (a • z) = a • H.δ hS n z := by
  let φ : S ⟶ S :=
    { τ₁ := smulHom S.X₁ a
      τ₂ := smulHom S.X₂ a
      τ₃ := smulHom S.X₃ a
      comm₁₂ := smulHom_naturality S.f a
      comm₂₃ := smulHom_naturality S.g a }
  have h : (shortExact_map_toSheaf hS).extClass.comp (Ext.mk₀ ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map (smulHom S.X₁ a)))
      (add_zero 1) =
      (Ext.mk₀ ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map (smulHom S.X₃ a))).comp (shortExact_map_toSheaf hS).extClass
      (zero_add 1) :=
    have hS' := shortExact_map_toSheaf hS
    let φ' : S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf) ⟶ S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf) :=
      (Functor.mapShortComplex (C := X.Modules)
        (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).map φ
    ShortComplex.ShortExact.extClass_naturality hS' hS' φ'
  rw [smul_H_eq_map, smul_H_eq_map, H.δ_apply, H.δ_apply, H.map_apply_eq_comp,
    H.map_apply_eq_comp, Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero, h]

/-- **Left exactness of `H⁰`.** For a monomorphism `M₁ ⟶ M₂`, the map `H⁰(M₁) ⟶ H⁰(M₂)` is
injective. -/
lemma H.injective_map_zero_of_shortExact (hS : S.ShortExact) :
    Function.Injective (H.map S.f 0) :=
  have : Mono ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map S.f) := (shortExact_map_toSheaf hS).mono_f
  Ext.postcomp_mk₀_injective_of_mono _ ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map S.f)

set_option maxHeartbeats 800000 in
/-- Exactness of `H^n(M₁) ⟶ H^n(M₂) ⟶ H^n(M₃)`. -/
lemma H.ker_map_g_eq_range_map_f (hS : S.ShortExact) (n : ℕ) :
    (H.map S.g n).ker = (H.map S.f n).range := by
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hS' := shortExact_map_toSheaf hS
    change Ext.comp x (Ext.mk₀ ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map S.g))
      (add_zero n) = 0 at hx
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₂
      (C := Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u})
      ((constantSheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) hS' x hx
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    rw [AddMonoidHom.mem_ker, ← H.map_comp_apply, S.zero, H.map_zero_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- Exactness of `H^n(M₂) ⟶ H^n(M₃) ⟶ H^{n+1}(M₁)`. -/
lemma H.ker_δ_eq_range_map_g (hS : S.ShortExact) (n : ℕ) :
    (H.δ hS n).ker = (H.map S.g n).range := by
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hS' := shortExact_map_toSheaf hS
    change Ext.comp x hS'.extClass rfl = 0 at hx
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃
      (C := Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u})
      ((constantSheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) hS' x rfl hx
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    have h0 : (Ext.mk₀ ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map S.g)).comp (shortExact_map_toSheaf hS).extClass
        (zero_add 1) = 0 :=
      (shortExact_map_toSheaf hS).comp_extClass
    rw [AddMonoidHom.mem_ker, H.δ_apply, H.map_apply_eq_comp, Ext.comp_assoc_of_second_deg_zero,
      h0, Ext.comp_zero]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- Exactness of `H^n(M₃) ⟶ H^{n+1}(M₁) ⟶ H^{n+1}(M₂)`. -/
lemma H.ker_map_f_eq_range_δ (hS : S.ShortExact) (n : ℕ) :
    (H.map S.f (n + 1)).ker = (H.δ hS n).range := by
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hS' := shortExact_map_toSheaf hS
    change Ext.comp x (Ext.mk₀ ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map S.f))
      (add_zero (n + 1)) = 0 at hx
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
      (C := Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u})
      ((constantSheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) hS' x hx rfl
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    have h0 : (shortExact_map_toSheaf hS).extClass.comp (Ext.mk₀ ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map S.f))
        (add_zero 1) = 0 :=
      (shortExact_map_toSheaf hS).extClass_comp
    rw [AddMonoidHom.mem_ker, H.δ_apply, H.map_apply_eq_comp, Ext.comp_assoc_of_third_deg_zero,
      h0, Ext.comp_zero]

section Field

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

/-- The connecting map as a `k`-linear map. -/
noncomputable def H.δLinearMap (hS : S.ShortExact) (n : ℕ) : S.X₃.H n →ₗ[k] S.X₁.H (n + 1) where
  toFun := H.δ hS n
  map_add' := map_add _
  map_smul' c := H.δ_smul hS n (globalSectionsRingHom k c)

/-- **Additivity of the Euler characteristic.** Let `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` be a short exact
sequence of `𝒪_X`-modules on a `k`-scheme `X` whose cohomology groups are finite-dimensional and
vanish in degrees above `N`. Then `χ(M₂) = χ(M₁) + χ(M₃)`.

Write `a_q`, `b_q` and `c_q` for the ranks of `H^q(M₁) ⟶ H^q(M₂)`, `H^q(M₂) ⟶ H^q(M₃)` and
`δ : H^q(M₃) ⟶ H^{q+1}(M₁)`. Exactness of the long exact sequence gives `h^q(M₁) = c_{q-1} + a_q`,
`h^q(M₂) = a_q + b_q` and `h^q(M₃) = b_q + c_q`, and the alternating sum of
`h^q(M₂) - h^q(M₁) - h^q(M₃) = -(c_{q-1} + c_q)` telescopes to `± c_N = 0`.
 -/
theorem eulerChar_eq_add_of_shortExact (hS : S.ShortExact) (N : ℕ)
    [∀ q, FiniteDimensional k (S.X₁.H q)] [∀ q, FiniteDimensional k (S.X₂.H q)]
    [∀ q, FiniteDimensional k (S.X₃.H q)]
    (h₁ : ∀ q, N < q → Subsingleton (S.X₁.H q)) (h₂ : ∀ q, N < q → Subsingleton (S.X₂.H q))
    (h₃ : ∀ q, N < q → Subsingleton (S.X₃.H q)) :
    S.X₂.eulerChar k = S.X₁.eulerChar k + S.X₃.eulerChar k := by
  let f q := H.mapLinearMap k S.f q
  let g q := H.mapLinearMap k S.g q
  let d q := H.δLinearMap k hS q
  let a q : ℤ := Module.finrank k (LinearMap.range (f q))
  let b q : ℤ := Module.finrank k (LinearMap.range (g q))
  let c q : ℤ := Module.finrank k (LinearMap.range (d q))
  have hker_g q : LinearMap.ker (g q) = LinearMap.range (f q) := by
    ext x
    exact SetLike.ext_iff.mp (H.ker_map_g_eq_range_map_f hS q) x
  have hker_d q : LinearMap.ker (d q) = LinearMap.range (g q) := by
    ext x
    exact SetLike.ext_iff.mp (H.ker_δ_eq_range_map_g hS q) x
  have hker_f q : LinearMap.ker (f (q + 1)) = LinearMap.range (d q) := by
    ext x
    exact SetLike.ext_iff.mp (H.ker_map_f_eq_range_δ hS q) x
  have hker_f₀ : LinearMap.ker (f 0) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (H.injective_map_zero_of_shortExact hS)
  have e₂ q : (S.X₂.finrankH k q : ℤ) = a q + b q := by
    have := LinearMap.finrank_range_add_finrank_ker (g q)
    rw [hker_g] at this
    simp only [finrankH, a, b]
    omega
  have e₃ q : (S.X₃.finrankH k q : ℤ) = b q + c q := by
    have := LinearMap.finrank_range_add_finrank_ker (d q)
    rw [hker_d] at this
    simp only [finrankH, b, c]
    omega
  have e₁ q : (S.X₁.finrankH k (q + 1) : ℤ) = c q + a (q + 1) := by
    have := LinearMap.finrank_range_add_finrank_ker (f (q + 1))
    rw [hker_f] at this
    simp only [finrankH, a, c]
    omega
  have e₁₀ : (S.X₁.finrankH k 0 : ℤ) = a 0 := by
    have := LinearMap.finrank_range_add_finrank_ker (f 0)
    rw [hker_f₀, finrank_bot] at this
    simp only [finrankH, a]
    omega
  have hcN : c N = 0 := by
    have := h₁ (N + 1) (by omega)
    simp only [c, Module.finrank_zero_of_subsingleton, Nat.cast_zero]
  have key (M : ℕ) : ∑ q ∈ Finset.range (M + 1), (-1 : ℤ) ^ q *
      ((S.X₂.finrankH k q : ℤ) - S.X₁.finrankH k q - S.X₃.finrankH k q) = -(-1) ^ M * c M := by
    induction M with
    | zero => simp [e₁₀, e₂, e₃]
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, e₁, e₂, e₃, pow_succ]
      ring
  have hsupp (M : X.Modules) (hM : ∀ q, N < q → Subsingleton (M.H q)) :
      (Function.support fun q : ℕ ↦ (-1 : ℤ) ^ q * (M.finrankH k q : ℤ)) ⊆
        (Finset.range (N + 1) : Set ℕ) := by
    intro q hq
    by_contra hqN
    have : N < q := by simpa using hqN
    have := hM q this
    exact hq (by simp [finrankH, Module.finrank_zero_of_subsingleton])
  simp only [eulerChar]
  rw [finsum_eq_sum_of_support_subset _ (hsupp _ h₁),
    finsum_eq_sum_of_support_subset _ (hsupp _ h₂), finsum_eq_sum_of_support_subset _ (hsupp _ h₃)]
  have := key N
  rw [hcN, mul_zero] at this
  simp only [mul_sub, Finset.sum_sub_distrib] at this
  linarith

end Field

end AlgebraicGeometry.Scheme.Modules
