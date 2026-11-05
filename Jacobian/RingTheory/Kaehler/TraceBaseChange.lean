import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Kaehler.TensorProduct
import Jacobian.RingTheory.Kaehler.Trace

/-!
# Base change of the trace of differentials

Let `k → R → B` be ring maps with `B` finite free over `R`, `D : R → R` a `k`-derivation, and
`k → k'` a ring map. Then `B' = k' ⊗[k] B` is a finite free algebra over `R' = k' ⊗[k] R`
(`Algebra.TensorProduct.baseChangeBasis`), `D` extends to a `k'`-derivation `D'` of `R'`
(`Derivation.baseChange`), and the trace derivation of `B'` restricts to that of `B`
(`Algebra.traceDeriv_baseChange`). If `k → k'` has a `k`-linear retraction (e.g. `k` is a field),
duality for the trace of differentials descends from `B'` to `B`
(`KaehlerDifferential.bijective_liftKaehlerDifferential_traceDerivation_of_baseChange`).
-/


open TensorProduct

namespace Algebra.TensorProduct

variable (k k' R B : Type*) [CommRing k] [CommRing k'] [Algebra k k'] [CommRing R] [Algebra k R]
  [CommRing B] [Algebra R B] [Algebra k B] [IsScalarTower k R B]

/-- The `k' ⊗[k] R`-algebra structure on `k' ⊗[k] B` for an `R`-algebra `B`. -/
noncomputable abbrev baseChangeAlgebra : Algebra (k' ⊗[k] R) (k' ⊗[k] B) :=
  (map (AlgHom.id k' k') (IsScalarTower.toAlgHom k R B)).toRingHom.toAlgebra

attribute [local instance] baseChangeAlgebra

variable {k k' R B} in
/-- The algebra map `k' ⊗[k] R → k' ⊗[k] B` is `x ⊗ r ↦ x ⊗ r`. -/
lemma baseChangeAlgebra_algebraMap_tmul (x : k') (r : R) :
    algebraMap (k' ⊗[k] R) (k' ⊗[k] B) (x ⊗ₜ r) = x ⊗ₜ algebraMap R B r := rfl

variable {k k' R B} in
/-- `(x ⊗ r) • (x' ⊗ b) = x x' ⊗ r • b`. -/
lemma baseChangeAlgebra_smul_tmul (x x' : k') (r : R) (b : B) :
    (x ⊗ₜ[k] r) • (x' ⊗ₜ[k] b) = (x * x') ⊗ₜ (r • b) := by
  rw [Algebra.smul_def, baseChangeAlgebra_algebraMap_tmul, tmul_mul_tmul, Algebra.smul_def]

/-- `k' → k' ⊗[k] R → k' ⊗[k] B` is a scalar tower. -/
lemma baseChangeAlgebra_isScalarTower : IsScalarTower k' (k' ⊗[k] R) (k' ⊗[k] B) :=
  .of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra]
    simp [Algebra.TensorProduct.algebraMap_apply]

attribute [local instance] baseChangeAlgebra_isScalarTower

variable {k k' R B} {ι : Type*} [DecidableEq ι] (b : Module.Basis ι R B)

/-- Auxiliary `k'`-linear version of `Algebra.TensorProduct.baseChangeRepr`. -/
noncomputable def baseChangeReprAux : (k' ⊗[k] B) ≃ₗ[k'] (ι →₀ k' ⊗[k] R) :=
  (LinearEquiv.baseChange k k' B (ι →₀ R) (b.repr.restrictScalars k)).trans
    (finsuppRight k k' k' R ι)

/-- The coordinates of `x ⊗ y` are `x ⊗ yᵢ`. -/
lemma baseChangeReprAux_tmul (x : k') (y : B) (i : ι) :
    baseChangeReprAux (k' := k') b (x ⊗ₜ[k] y) i = x ⊗ₜ[k] b.repr y i := by
  simp [baseChangeReprAux, finsuppRight_apply_tmul_apply]

/-- `Algebra.TensorProduct.baseChangeReprAux` is `k' ⊗[k] R`-linear. -/
lemma baseChangeReprAux_smul (r : k' ⊗[k] R) (y : k' ⊗[k] B) :
    baseChangeReprAux b (r • y) = r • baseChangeReprAux b y := by
  induction r with
  | zero => simp
  | add r r' hr hr' => simp only [add_smul, map_add, hr, hr']
  | tmul x r =>
    induction y with
    | zero => simp
    | add y y' hy hy' => simp only [smul_add, map_add, hy, hy']
    | tmul x' c =>
      ext i
      rw [baseChangeAlgebra_smul_tmul, baseChangeReprAux_tmul, Finsupp.smul_apply,
        baseChangeReprAux_tmul, smul_eq_mul, tmul_mul_tmul, map_smul, Finsupp.smul_apply,
        smul_eq_mul]

/-- The coordinates of `k' ⊗[k] B` over `k' ⊗[k] R` in the base change of a basis of `B`. -/
noncomputable def baseChangeRepr : (k' ⊗[k] B) ≃ₗ[k' ⊗[k] R] (ι →₀ k' ⊗[k] R) where
  __ := baseChangeReprAux b
  map_smul' := baseChangeReprAux_smul b

/-- The coordinates of `x ⊗ y` are `x ⊗ yᵢ`. -/
lemma baseChangeRepr_tmul (x : k') (y : B) (i : ι) :
    baseChangeRepr b (x ⊗ₜ[k] y) i = x ⊗ₜ[k] b.repr y i :=
  baseChangeReprAux_tmul b x y i

/-- The basis `1 ⊗ bᵢ` of `k' ⊗[k] B` over `k' ⊗[k] R`. -/
noncomputable def baseChangeBasis : Module.Basis ι (k' ⊗[k] R) (k' ⊗[k] B) :=
  .ofRepr (baseChangeRepr b)

/-- The coordinates of `x ⊗ y` in the basis `1 ⊗ bᵢ` are `x ⊗ yᵢ`. -/
lemma baseChangeBasis_repr_tmul (x : k') (y : B) (i : ι) :
    (baseChangeBasis (k' := k') b).repr (x ⊗ₜ[k] y) i = x ⊗ₜ[k] b.repr y i :=
  baseChangeRepr_tmul b x y i

/-- The elements of `Algebra.TensorProduct.baseChangeBasis` are `1 ⊗ bᵢ`. -/
lemma baseChangeBasis_apply (i : ι) : baseChangeBasis (k' := k') b i = 1 ⊗ₜ[k] b i := by
  classical
  refine (baseChangeBasis (k' := k') b).repr.injective (Finsupp.ext fun j ↦ ?_)
  rw [baseChangeBasis_repr_tmul, Module.Basis.repr_self, Module.Basis.repr_self,
    Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp [Algebra.TensorProduct.one_def]

omit [DecidableEq ι] in
/-- `k' ⊗[k] B` is free over `k' ⊗[k] R` if `B` is free over `R`. -/
lemma free_baseChange [Module.Free R B] : Module.Free (k' ⊗[k] R) (k' ⊗[k] B) :=
  haveI := Classical.decEq (Module.Free.ChooseBasisIndex R B)
  .of_basis (baseChangeBasis (Module.Free.chooseBasis R B))

omit [DecidableEq ι] in
/-- `k' ⊗[k] B` is finite over `k' ⊗[k] R` if `B` is finite free over `R`. -/
lemma finite_baseChange [Module.Free R B] [Module.Finite R B] :
    Module.Finite (k' ⊗[k] R) (k' ⊗[k] B) :=
  haveI := Classical.decEq (Module.Free.ChooseBasisIndex R B)
  .of_basis (baseChangeBasis (Module.Free.chooseBasis R B))


/-- Two `k' ⊗[k] R`-linear maps out of `k' ⊗[k] B` agree if they agree on `1 ⊗ B`. -/
lemma baseChange_linearMap_ext {M : Type*} [AddCommGroup M] [Module (k' ⊗[k] R) M]
    {f g : (k' ⊗[k] B) →ₗ[k' ⊗[k] R] M} (h : ∀ c : B, f (1 ⊗ₜ c) = g (1 ⊗ₜ c)) : f = g := by
  refine LinearMap.ext fun y ↦ ?_
  induction y with
  | zero => simp
  | add y y' hy hy' => rw [map_add, map_add, hy, hy']
  | tmul x c =>
    have : x ⊗ₜ[k] c = (x ⊗ₜ[k] (1 : R)) • ((1 : k') ⊗ₜ[k] c) := by
      rw [baseChangeAlgebra_smul_tmul, mul_one, one_smul]
    rw [this, LinearMap.map_smul, LinearMap.map_smul, h]

/-- The base change `k' ⊗[k] B → k' ⊗[k] R` of an `R`-linear map `B → R`. -/
noncomputable def baseChangeLinearMap (φ : B →ₗ[R] R) :
    (k' ⊗[k] B) →ₗ[k' ⊗[k] R] (k' ⊗[k] R) where
  toFun := (φ.restrictScalars k).baseChange k'
  map_add' := map_add _
  map_smul' r y := by
    induction r with
    | zero => simp
    | add r r' hr hr' => simp only [add_smul, map_add, hr, hr', RingHom.id_apply]
    | tmul x r =>
      induction y with
      | zero => simp
      | add y y' hy hy' => simp only [smul_add, map_add, hy, hy']
      | tmul x' c =>
        rw [baseChangeAlgebra_smul_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
          RingHom.id_apply, smul_eq_mul, tmul_mul_tmul, LinearMap.restrictScalars_apply,
          LinearMap.restrictScalars_apply, LinearMap.map_smul, smul_eq_mul]

/-- `φ'(x ⊗ c) = x ⊗ φ(c)`. -/
@[simp]
lemma baseChangeLinearMap_tmul (φ : B →ₗ[R] R) (x : k') (c : B) :
    baseChangeLinearMap φ (x ⊗ₜ[k] c) = x ⊗ₜ φ c := rfl
end Algebra.TensorProduct

namespace Derivation

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] (k' : Type*) [CommRing k']
  [Algebra k k'] (D : Derivation k R R)

/-- The base change `k' ⊗[k] R → k' ⊗[k] R` of a `k`-derivation of `R`. -/
noncomputable def baseChange : Derivation k' (k' ⊗[k] R) (k' ⊗[k] R) :=
  Derivation.mk' ((D : R →ₗ[k] R).baseChange k') fun a c ↦ by
    induction a with
    | zero => simp
    | add a a' ha ha' => simp only [add_mul, map_add, ha, ha', add_smul, smul_add]; abel
    | tmul x r =>
      induction c with
      | zero => simp
      | add c c' hc hc' => simp only [mul_add, map_add, hc, hc', smul_add, add_smul]; abel
      | tmul x' r' =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul,
          Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, tmul_add, mul_comm x x']

/-- `D'(x ⊗ r) = x ⊗ D(r)`. -/
@[simp]
lemma baseChange_tmul (x : k') (r : R) : D.baseChange k' (x ⊗ₜ r) = x ⊗ₜ D r := rfl

end Derivation

namespace Algebra

open TensorProduct Matrix

attribute [local instance] TensorProduct.baseChangeAlgebra
  TensorProduct.baseChangeAlgebra_isScalarTower

variable {k R B : Type*} [CommRing k] [CommRing R] [Algebra k R] [CommRing B] [Algebra R B]
  [Algebra k B] [IsScalarTower k R B] (k' : Type*) [CommRing k'] [Algebra k k']
  (D : Derivation k R R)

/-- The matrix of multiplication by `1 ⊗ a` in the basis `1 ⊗ bᵢ` is that of `a` in `b`. -/
lemma leftMulMatrix_baseChangeBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R B) (a : B) :
    leftMulMatrix (TensorProduct.baseChangeBasis (k' := k') b) (1 ⊗ₜ[k] a) =
      (leftMulMatrix b a).map (TensorProduct.includeRight (R := k) (A := k')) := by
  ext i j
  rw [leftMulMatrix_eq_repr_mul, TensorProduct.baseChangeBasis_apply, tmul_mul_tmul, mul_one,
    TensorProduct.baseChangeBasis_repr_tmul, Matrix.map_apply, leftMulMatrix_eq_repr_mul,
    TensorProduct.includeRight_apply]

/-- `Tr(X D(Y))` commutes with base change along `R → k' ⊗[k] R`. -/
lemma traceDerivForm_map_includeRight {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n R)
    (Y : Matrix n m R) :
    traceDerivForm (D.baseChange k') (X.map (TensorProduct.includeRight (R := k) (A := k')))
      (Y.map TensorProduct.includeRight) = 1 ⊗ₜ traceDerivForm D X Y := by
  simp [traceDerivForm, tmul_sum, Algebra.TensorProduct.tmul_mul_tmul]

variable [Module.Free R B] [Module.Finite R B]

attribute [local instance] TensorProduct.free_baseChange TensorProduct.finite_baseChange

/-- The trace derivation of `k' ⊗[k] B` restricts to that of `B`. -/
lemma traceDeriv_baseChange (a c : B) :
    traceDeriv (D.baseChange k') ((1 : k') ⊗ₜ[k] a) (1 ⊗ₜ c) = 1 ⊗ₜ traceDeriv D a c := by
  classical
  set b := Module.Free.chooseBasis R B
  rw [traceDeriv_eq _ (TensorProduct.baseChangeBasis (k' := k') b), traceDerivAux,
    leftMulMatrix_baseChangeBasis, leftMulMatrix_baseChangeBasis,
    traceDerivForm_map_includeRight]
  rfl

end Algebra

namespace KaehlerDifferential

open Algebra

attribute [local instance] TensorProduct.baseChangeAlgebra
  TensorProduct.baseChangeAlgebra_isScalarTower TensorProduct.free_baseChange
  TensorProduct.finite_baseChange TensorProduct.rightAlgebra precompModule
  precompModule_isScalarTower

variable {k R B : Type*} [CommRing k] [CommRing R] [Algebra k R] [CommRing B] [Algebra R B]
  [Algebra k B] [IsScalarTower k R B] [Module.Free R B] [Module.Finite R B]
  (k' : Type*) [CommRing k'] [Algebra k k'] (D : Derivation k R R)

/-- The isomorphism `Ω ≅ Hom_R(-, R)` induced by the trace derivation commutes with base change
along `k → k'`. -/
lemma liftKaehlerDifferential_traceDerivation_map (ω : Ω[B⁄k]) (c : B) :
    (traceDerivation (B := k' ⊗[k] B) (D.baseChange k')).liftKaehlerDifferential
      (KaehlerDifferential.map k k' B (k' ⊗[k] B) ω) (1 ⊗ₜ[k] c) =
      1 ⊗ₜ (traceDerivation D).liftKaehlerDifferential ω c := by
  have hω : ω ∈ (⊤ : Submodule B Ω[B⁄k]) := Submodule.mem_top
  rw [← KaehlerDifferential.span_range_derivation] at hω
  induction hω using Submodule.span_induction generalizing c with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D, traceDerivation_apply, traceDerivation_apply,
      TensorProduct.right_algebraMap_apply, traceDeriv_baseChange]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, TensorProduct.tmul_add]
  | smul b x _ hx =>
    rw [LinearMap.map_smul, LinearMap.map_smul, precompModule_smul_apply, ← hx,
      ← algebraMap_smul (k' ⊗[k] B) b, LinearMap.map_smul, precompModule_smul_apply,
      TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- **Duality for the trace of differentials descends along base change.** If `k → k'` has a
`k`-linear retraction and the trace derivation of `k' ⊗[k] B` over `k' ⊗[k] R` induces an
isomorphism `Ω ≅ Hom(-, k' ⊗[k] R)`, then so does the trace derivation of `B` over `R`. -/
theorem bijective_liftKaehlerDifferential_traceDerivation_of_baseChange (l : k' →ₗ[k] k)
    (hl : l 1 = 1)
    (h : Function.Bijective
      (traceDerivation (B := k' ⊗[k] B) (D.baseChange k')).liftKaehlerDifferential) :
    Function.Bijective (traceDerivation (B := B) D).liftKaehlerDifferential := by
  set Ψ := (traceDerivation (B := B) D).liftKaehlerDifferential
  set Ψ' := (traceDerivation (B := k' ⊗[k] B) (D.baseChange k')).liftKaehlerDifferential
  let L : k' ⊗[k] Ω[B⁄k] →ₗ[k] Ω[B⁄k] := (TensorProduct.lid k _).toLinearMap ∘ₗ l.rTensor _
  let Λ : k' ⊗[k] R →ₗ[k] R := (TensorProduct.lid k R).toLinearMap ∘ₗ l.rTensor R
  have hL (x : k') (ω : Ω[B⁄k]) : L (x ⊗ₜ ω) = l x • ω := by simp [L]
  have hΛ (x : k') (r : R) : Λ (x ⊗ₜ r) = l x • r := by simp [Λ]
  let E := tensorKaehlerEquivBase k k' B (k' ⊗[k] B)
  have hE (x : k') (ω : Ω[B⁄k]) (c : B) : Ψ' (E (x ⊗ₜ ω)) (1 ⊗ₜ c) = x ⊗ₜ Ψ ω c := by
    rw [tensorKaehlerEquivBase_tmul, LinearMap.map_smul_of_tower, LinearMap.smul_apply,
      liftKaehlerDifferential_traceDerivation_map, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have key (z : k' ⊗[k] Ω[B⁄k]) (c : B) : Λ (Ψ' (E z) (1 ⊗ₜ c)) = Ψ (L z) c := by
    induction z with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']
    | tmul x ω =>
      rw [hE, hΛ, hL, LinearMap.map_smul_of_tower, LinearMap.smul_apply]
  refine ⟨fun ω ω' hωω' ↦ ?_, fun φ ↦ ?_⟩
  · have h1 : Ψ' (E (1 ⊗ₜ ω)) = Ψ' (E (1 ⊗ₜ ω')) :=
      TensorProduct.baseChange_linearMap_ext fun c ↦ by rw [hE, hE, hωω']
    have h2 := congrArg L (E.injective (h.1 h1))
    rwa [hL, hL, hl, one_smul, one_smul] at h2
  · obtain ⟨m, hm⟩ := h.2 (TensorProduct.baseChangeLinearMap (k' := k') φ)
    obtain ⟨z, rfl⟩ := E.surjective m
    refine ⟨L z, LinearMap.ext fun c ↦ ?_⟩
    rw [← key z c, hm, TensorProduct.baseChangeLinearMap_tmul, hΛ, hl, one_smul]


omit [Module.Free R B] [Module.Finite R B] in
/-- If `Ω_{B/k}` is locally generated by one element near every maximal ideal, then so is
`Ω_{k' ⊗[k] B/k'}` for an integral extension `k → k'`. -/
lemma exists_smul_eq_smul_baseChange [Algebra.IsIntegral k k']
    (hsm : ∀ q : Ideal B, q.IsMaximal →
      ∃ ω₀ : Ω[B⁄k], ∃ s ∉ q, ∀ ω : Ω[B⁄k], ∃ b : B, s • ω = b • ω₀)
    (q : Ideal (k' ⊗[k] B)) (hq : q.IsMaximal) :
    ∃ ω₀ : Ω[k' ⊗[k] B⁄k'], ∃ s ∉ q, ∀ ω : Ω[k' ⊗[k] B⁄k'], ∃ b : k' ⊗[k] B,
      s • ω = b • ω₀ := by
  have : Algebra.IsIntegral B (k' ⊗[k] B) := ⟨fun y ↦ by
    induction y with
    | zero => exact isIntegral_zero
    | add y y' hy hy' => exact hy.add hy'
    | tmul x b =>
      have hx : IsIntegral B (x ⊗ₜ[k] (1 : B)) :=
        ((Algebra.IsIntegral.isIntegral (R := k) x).map
          (Algebra.TensorProduct.includeLeft (S := k) (B := B))).tower_top
      have hb : IsIntegral B ((1 : k') ⊗ₜ[k] b) := isIntegral_algebraMap
      have := hx.mul hb
      rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this⟩
  obtain ⟨ω₀, s, hs, h⟩ := hsm (q.comap (algebraMap B (k' ⊗[k] B)))
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q)
  refine ⟨KaehlerDifferential.map k k' B (k' ⊗[k] B) ω₀, algebraMap B _ s, hs, fun ω ↦ ?_⟩
  obtain ⟨z, rfl⟩ := (tensorKaehlerEquivBase k k' B (k' ⊗[k] B)).surjective ω
  induction z with
  | zero => exact ⟨0, by simp⟩
  | add z z' hz hz' =>
    obtain ⟨b, hb⟩ := hz
    obtain ⟨b', hb'⟩ := hz'
    exact ⟨b + b', by rw [map_add, smul_add, hb, hb', add_smul]⟩
  | tmul x ω =>
    obtain ⟨b, hb⟩ := h ω
    refine ⟨algebraMap k' _ x * algebraMap B _ b, ?_⟩
    rw [tensorKaehlerEquivBase_tmul, smul_comm, algebraMap_smul, ← LinearMap.map_smul, hb,
      LinearMap.map_smul, ← algebraMap_smul (k' ⊗[k] B) b, mul_smul, algebraMap_smul]
    rw [algebraMap_smul]

omit [Module.Free R B] [Module.Finite R B] in
/-- If `Ω_{B/R}` is killed by a nonzerodivisor, then so is `Ω_{k' ⊗[k] B/k' ⊗[k] R}` for a flat
extension `k → k'`. -/
lemma exists_mem_nonZeroDivisors_smul_eq_zero_baseChange [Module.Flat k k']
    (hunr : ∃ s ∈ nonZeroDivisors B, ∀ ω : Ω[B⁄R], s • ω = 0) :
    ∃ s ∈ nonZeroDivisors (k' ⊗[k] B), ∀ ω : Ω[k' ⊗[k] B⁄k' ⊗[k] R], s • ω = 0 := by
  obtain ⟨s, hs, hsΩ⟩ := hunr
  let : Algebra R (k' ⊗[k] B) :=
    ((algebraMap (k' ⊗[k] R) (k' ⊗[k] B)).comp (algebraMap R (k' ⊗[k] R))).toAlgebra
  have : IsScalarTower R (k' ⊗[k] R) (k' ⊗[k] B) := .of_algebraMap_eq' rfl
  have : IsScalarTower R B (k' ⊗[k] B) := .of_algebraMap_eq fun r ↦ rfl
  refine ⟨algebraMap B (k' ⊗[k] B) s, mem_nonZeroDivisors_iff_right.2 fun y hy ↦ ?_, fun ω ↦ ?_⟩
  · have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := k')
      (LinearMap.mulRight k s) fun x x' hxx' ↦
        sub_eq_zero.1 <| (mem_nonZeroDivisors_iff_right.1 hs) (x - x') (by
          simp only [LinearMap.mulRight_apply] at hxx'
          rw [sub_mul, hxx', sub_self])
    have hmul (z : k' ⊗[k] B) :
        ((LinearMap.mulRight k s).lTensor k') z = z * algebraMap B _ s := by
      induction z with
      | zero => simp
      | add z z' hz hz' => rw [map_add, hz, hz', add_mul]
      | tmul x b => simp [TensorProduct.right_algebraMap_apply,
          Algebra.TensorProduct.tmul_mul_tmul]
    exact hinj ((hmul y).trans (hy.trans (map_zero _).symm))
  · have hD (b : B) : algebraMap B (k' ⊗[k] B) s •
        KaehlerDifferential.D (k' ⊗[k] R) (k' ⊗[k] B) (1 ⊗ₜ b) = 0 := by
      rw [algebraMap_smul, ← TensorProduct.right_algebraMap_apply, ← KaehlerDifferential.map_D R,
        ← LinearMap.map_smul, hsΩ, map_zero]
    have hω : ω ∈ (⊤ : Submodule (k' ⊗[k] B) _) := Submodule.mem_top
    rw [← KaehlerDifferential.span_range_derivation] at hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      induction y with
      | zero => simp
      | add y y' hy hy' => rw [map_add, smul_add, hy, hy', add_zero]
      | tmul x b =>
        have : x ⊗ₜ[k] b = (x ⊗ₜ[k] (1 : R)) • ((1 : k') ⊗ₜ[k] b) := by
          rw [TensorProduct.baseChangeAlgebra_smul_tmul, mul_one, one_smul]
        rw [this, Derivation.map_smul, smul_comm, hD, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
    | smul b x _ hx => rw [smul_comm, hx, smul_zero]

end KaehlerDifferential
