import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Comparing arbitrary resolutions with injective resolutions

A resolution admits a comparison map into an injective resolution extending a map on the resolved objects.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory Category Limits Injective HomologicalComplex
namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] {Z : C} {K : CochainComplex C ℕ}
  (ι : (single₀ C).obj Z ⟶ K) [QuasiIso ι]

include ι in
/-- The target of a quasi-isomorphism from `single₀ Z` is exact in positive degrees. -/
lemma exactAt_succ_of_quasiIso_single₀ (n : ℕ) : K.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt ι (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance

include ι in
/-- The target `K` of a quasi-isomorphism from `single₀ Z` is exact at `Kⁿ⁺¹`:
`Kⁿ ⟶ Kⁿ⁺¹ ⟶ Kⁿ⁺²` is exact. -/
lemma exact_succ_of_quasiIso_single₀ (n : ℕ) :
    (ShortComplex.mk _ _ (K.d_comp_d n (n + 1) (n + 2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 (exactAt_succ_of_quasiIso_single₀ ι n)

omit [QuasiIso ι] in
@[reassoc (attr := simp)]
lemma ι_f_zero_comp_d_zero_one_of_single₀ : ι.f 0 ≫ K.d 0 1 = 0 := by
  rw [ι.comm, (isZero_single_obj_X _ _ _ 1 (by simp)).eq_of_src (ι.f 1) 0, comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `Z` is the kernel of `K⁰ ⟶ K¹` when `ι : single₀ Z ⟶ K` is a quasi-isomorphism. -/
def isLimitKernelForkOfQuasiIsoSingle₀ :
    IsLimit (KernelFork.ofι _ (ι_f_zero_comp_d_zero_one_of_single₀ ι)) := by
  refine IsLimit.ofIsoLimit (K.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
  refine Fork.ext ((singleObjHomologySelfIso _ _ _).symm ≪≫
    isoOfQuasiIsoAt ι 0 ≪≫ K.isoHomologyπ₀.symm) ?_
  rw [← cancel_epi (singleObjHomologySelfIso (ComplexShape.up ℕ) _ _).hom,
    ← cancel_epi (isoHomologyπ₀ _).hom,
    ← cancel_epi (singleObjCyclesSelfIso (ComplexShape.up ℕ) _ _).inv]
  simp

/-- If `ι : single₀ Z ⟶ K` is a quasi-isomorphism, then `Z ⟶ K⁰ ⟶ K¹` is exact. -/
lemma exact₀_of_quasiIso_single₀ :
    (ShortComplex.mk _ _ (ι_f_zero_comp_d_zero_one_of_single₀ ι)).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (isLimitKernelForkOfQuasiIsoSingle₀ ι)

instance mono_f_zero_of_quasiIso_single₀ : Mono (ι.f 0) :=
  mono_of_isLimit_fork (isLimitKernelForkOfQuasiIsoSingle₀ ι)

end CochainComplex

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]

namespace InjectiveResolution

open CochainComplex

variable {Y Z : C} {K : CochainComplex C ℕ}

/-- Auxiliary construction for `descOfQuasiIso`. -/
def descOfQuasiIsoFZero (f : Z ⟶ Y) (I : InjectiveResolution Y) (ι : (single₀ C).obj Z ⟶ K)
    [QuasiIso ι] : K.X 0 ⟶ I.cocomplex.X 0 :=
  factorThru (f ≫ I.ι.f 0) (ι.f 0)

@[reassoc (attr := simp)]
lemma comp_descOfQuasiIsoFZero (f : Z ⟶ Y) (I : InjectiveResolution Y)
    (ι : (single₀ C).obj Z ⟶ K) [QuasiIso ι] :
    ι.f 0 ≫ descOfQuasiIsoFZero f I ι = f ≫ I.ι.f 0 :=
  comp_factorThru _ _

/-- Auxiliary construction for `descOfQuasiIso`. -/
def descOfQuasiIsoFOne (f : Z ⟶ Y) (I : InjectiveResolution Y) (ι : (single₀ C).obj Z ⟶ K)
    [QuasiIso ι] : K.X 1 ⟶ I.cocomplex.X 1 :=
  (exact₀_of_quasiIso_single₀ ι).descToInjective (descOfQuasiIsoFZero f I ι ≫ I.cocomplex.d 0 1)
    (by simp)

@[reassoc (attr := simp)]
lemma d_comp_descOfQuasiIsoFOne (f : Z ⟶ Y) (I : InjectiveResolution Y)
    (ι : (single₀ C).obj Z ⟶ K) [QuasiIso ι] :
    K.d 0 1 ≫ descOfQuasiIsoFOne f I ι = descOfQuasiIsoFZero f I ι ≫ I.cocomplex.d 0 1 :=
  (exact₀_of_quasiIso_single₀ ι).comp_descToInjective _ _

/-- Auxiliary construction for `descOfQuasiIso`. -/
def descOfQuasiIsoFSucc (I : InjectiveResolution Y) (ι : (single₀ C).obj Z ⟶ K) [QuasiIso ι]
    (n : ℕ) (g : K.X n ⟶ I.cocomplex.X n) (g' : K.X (n + 1) ⟶ I.cocomplex.X (n + 1))
    (w : K.d n (n + 1) ≫ g' = g ≫ I.cocomplex.d n (n + 1)) :
    Σ' g'' : K.X (n + 2) ⟶ I.cocomplex.X (n + 2),
      K.d (n + 1) (n + 2) ≫ g'' = g' ≫ I.cocomplex.d (n + 1) (n + 2) :=
  ⟨(exact_succ_of_quasiIso_single₀ ι n).descToInjective
    (g' ≫ I.cocomplex.d (n + 1) (n + 2)) (by simp [reassoc_of% w]),
      (exact_succ_of_quasiIso_single₀ ι n).comp_descToInjective _ _⟩

/-- A morphism `f : Z ⟶ Y` lifts to a cochain map `K ⟶ I.cocomplex` from any resolution
`ι : single₀ Z ⟶ K` of `Z` to an injective resolution `I` of `Y`. This generalises
`InjectiveResolution.desc`, where `K` is also an injective resolution. -/
def descOfQuasiIso (f : Z ⟶ Y) (I : InjectiveResolution Y) (ι : (single₀ C).obj Z ⟶ K)
    [QuasiIso ι] : K ⟶ I.cocomplex :=
  CochainComplex.mkHom _ _ (descOfQuasiIsoFZero f I ι) (descOfQuasiIsoFOne f I ι)
    (d_comp_descOfQuasiIsoFOne f I ι).symm fun n ⟨g, g', w⟩ ↦
      ⟨(descOfQuasiIsoFSucc I ι n g g' w.symm).1, (descOfQuasiIsoFSucc I ι n g g' w.symm).2.symm⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The lift `descOfQuasiIso f I ι` is compatible with `f`:
```
  single₀ Z ──ι──▶ K
      │               │
  single₀ f      descOfQuasiIso f I ι
      ▼               ▼
  single₀ Y ──I.ι──▶ I.cocomplex
```
-/
@[reassoc (attr := simp)]
theorem descOfQuasiIso_commutes (f : Z ⟶ Y) (I : InjectiveResolution Y)
    (ι : (single₀ C).obj Z ⟶ K) [QuasiIso ι] :
    ι ≫ descOfQuasiIso f I ι = (single₀ C).map f ≫ I.ι := by
  ext
  simp [descOfQuasiIso]

/-- Every resolution `ι : single₀ Z ⟶ K` of `Z` maps to any injective resolution `I` of `Z`
by a cochain map `φ : K ⟶ I.cocomplex` compatible with the augmentations. -/
theorem exists_comp_eq_ι_of_quasiIso (I : InjectiveResolution Z) (ι : (single₀ C).obj Z ⟶ K)
    [QuasiIso ι] : ∃ φ : K ⟶ I.cocomplex, ι ≫ φ = I.ι :=
  ⟨descOfQuasiIso (𝟙 Z) I ι, by simp⟩

/-- The lift `descOfQuasiIso (𝟙 Z) I ι` of the identity from a resolution `ι` of `Z` to an
injective resolution `I` of `Z` is a quasi-isomorphism. -/
instance quasiIso_descOfQuasiIso_id (I : InjectiveResolution Z) (ι : (single₀ C).obj Z ⟶ K)
    [QuasiIso ι] : QuasiIso (descOfQuasiIso (𝟙 Z) I ι) := by
  have : QuasiIso (ι ≫ descOfQuasiIso (𝟙 Z) I ι) := by
    rw [descOfQuasiIso_commutes, Functor.map_id, id_comp]
    infer_instance
  exact quasiIso_of_comp_left ι _

end InjectiveResolution
end CategoryTheory
