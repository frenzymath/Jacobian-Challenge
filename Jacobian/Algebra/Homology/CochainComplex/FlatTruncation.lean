import Jacobian.Algebra.Homology.CochainComplex.FlatCycles
import Jacobian.Algebra.Homology.CochainComplex.FlatBaseChange
import Jacobian.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Tensor-compatible truncation of flat complexes

An exact tail with flat cycles can be truncated without changing its cohomology
after any extension of scalars. The criterion uses the actual scalar-extension
functor and does not require the original complex to be bounded above.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory Limits TensorProduct

namespace CochainComplex

variable {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]

/-- Exactness of scalar extension is exactness of the tensored differentials. -/
lemma exactAt_extendScalars_iff (C : CochainComplex (ModuleCat.{u} A) ℤ) (degree : ℤ) :
    (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex _).obj C).ExactAt
        (degree + 1) ↔
      Function.Exact ((C.d degree (degree + 1)).hom.lTensor B)
        ((C.d (degree + 1) (degree + 1 + 1)).hom.lTensor B) := by
  rw [exactAt_iff_exact]
  have naturality {M N : ModuleCat.{u} A} (map : M ⟶ N) :
      ((ModuleCat.extendScalars (algebraMap A B)).map map).hom ∘ₗ
          (ModuleCat.tensorEquivExtendScalars A B M).toLinearMap =
        (ModuleCat.tensorEquivExtendScalars A B N).toLinearMap ∘ₗ map.hom.baseChange B := by
    ext tensorValue : 1
    induction tensorValue using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul scalar moduleValue => rfl
    | add left right left_eq right_eq => simp only [map_add, left_eq, right_eq]
  have comparison := Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := ModuleCat.tensorEquivExtendScalars A B (C.X degree))
    (e₂ := ModuleCat.tensorEquivExtendScalars A B (C.X (degree + 1)))
    (e₃ := ModuleCat.tensorEquivExtendScalars A B (C.X (degree + 1 + 1)))
    (naturality (C.d degree (degree + 1)))
    (naturality (C.d (degree + 1) (degree + 1 + 1)))
  change Function.Exact
      (((ModuleCat.extendScalars (algebraMap A B)).map (C.d degree (degree + 1))).hom)
      (((ModuleCat.extendScalars (algebraMap A B)).map
        (C.d (degree + 1) (degree + 1 + 1))).hom) ↔
    Function.Exact ((C.d degree (degree + 1)).hom.baseChange B)
      ((C.d (degree + 1) (degree + 1 + 1)).hom.baseChange B)
  exact comparison

variable {K L : CochainComplex (ModuleCat.{u} A) ℤ} (φ : K ⟶ L)

/-- If `K` vanishes in degree `k + 1`, the cycles of the mapping cone of `φ` in
degree `k` are those of `L`. -/
lemma flat_ker_d_mappingCone (k : ℤ) (h₁ : IsZero (K.X (k + 1)))
    (hL : Module.Flat A (LinearMap.ker (L.d k (k + 1)).hom)) :
    Module.Flat A (LinearMap.ker ((mappingCone φ).d k (k + 1)).hom) := by
  have hsec (j : ℤ) (hj : IsZero (K.X (j + 1))) (x : (mappingCone φ).X j) :
      ((mappingCone.inr φ).f j).hom (((mappingCone.snd φ).v j j (add_zero j)).hom x) = x := by
    have := congrArg (fun f ↦ f.hom x) (mappingCone.id_X φ j (j + 1) rfl)
    simpa [hj.eq_of_tgt ((mappingCone.fst φ).1.v j (j + 1) rfl) 0] using this
  have hret (j : ℤ) (y : L.X j) :
      ((mappingCone.snd φ).v j j (add_zero j)).hom (((mappingCone.inr φ).f j).hom y) = y := by
    rw [← ModuleCat.comp_apply, mappingCone.inr_f_snd_v]
    rfl
  let e : L.X k ≃ₗ[A] (mappingCone φ).X k :=
    { toFun := ((mappingCone.inr φ).f k).hom
      map_add' := map_add _
      map_smul' := map_smul _
      invFun := ((mappingCone.snd φ).v k k (add_zero k)).hom
      left_inv := hret k
      right_inv := hsec k h₁ }
  have heq : LinearMap.ker ((mappingCone φ).d k (k + 1)).hom =
      (LinearMap.ker (L.d k (k + 1)).hom).map (e : L.X k →ₗ[A] (mappingCone φ).X k) := by
    ext x
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
    change _ ↔ (L.d k (k + 1)).hom (((mappingCone.snd φ).v k k (add_zero k)).hom x) = 0
    conv_lhs => rw [← hsec k h₁ x, ← ModuleCat.comp_apply, mappingCone.inr_f_d,
      ModuleCat.comp_apply]
    constructor
    · intro h
      rw [← hret (k + 1) ((L.d k (k + 1)).hom _), h, map_zero]
    · intro h
      rw [h, map_zero]
  rw [heq]
  exact Module.Flat.of_linearEquiv (e.submoduleMap _).symm


/-- Flat complexes with eventually flat cone cycles remain quasi-isomorphic after any
extension of scalars. Neither complex needs to be bounded above. -/
theorem quasiIso_extendScalars_of_eventually_flat_cycles [QuasiIso φ]
    (hK : ∀ degree, Module.Flat A (K.X degree))
    (hL : ∀ degree, Module.Flat A (L.X degree)) {bound : ℤ}
    (flatTail : ∀ degree, bound ≤ degree →
      Module.Flat A (LinearMap.ker ((mappingCone φ).d degree (degree + 1)).hom)) :
    QuasiIso (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex _).map φ) := by
  have acyclic := (mappingCone.quasiIso_iff_acyclic φ).mp inferInstance
  have flatTerms := mappingCone_flat_X φ hK hL
  have flatCycles (degree : ℤ) :
      Module.Flat A (LinearMap.ker ((mappingCone φ).d degree (degree + 1)).hom) :=
    flat_ker_d_of_exactAt flatTerms (m := degree + 1)
      (fun index _ ↦ acyclic index) flatTail degree (by omega)
  rw [mappingCone.quasiIso_iff_acyclic]
  intro degree
  refine HomologicalComplex.ExactAt.of_iso ?_
    (mappingCone.mapHomologicalComplexIso φ (ModuleCat.extendScalars (algebraMap A B)))
  obtain ⟨index, rfl⟩ : ∃ index, degree = index + 1 := ⟨degree - 1, by omega⟩
  rw [exactAt_extendScalars_iff]
  exact exact_lTensor_d B (m := index + 1) (fun degree _ ↦ acyclic degree)
    (fun degree _ ↦ flatCycles degree) index le_rfl

/-- An exact tail with flat cycles can be truncated compatibly with scalar extension. -/
theorem quasiIso_extendScalars_ιTruncLE (C : CochainComplex (ModuleCat.{u} A) ℤ) (bound : ℤ)
    (flatTerms : ∀ degree, Module.Flat A (C.X degree))
    (exactTail : ∀ degree, bound < degree → C.ExactAt degree)
    (flatCycles : ∀ degree, bound ≤ degree →
      Module.Flat A (LinearMap.ker (C.d degree (degree + 1)).hom)) :
    QuasiIso (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex _).map
      (C.ιTruncLE bound)) := by
  have : C.IsLE bound := (C.isLE_iff bound).mpr exactTail
  refine quasiIso_extendScalars_of_eventually_flat_cycles B (C.ιTruncLE bound)
    (flat_truncLE_X C bound flatTerms (flatCycles bound le_rfl)) flatTerms
    (bound := bound) fun degree degreeBound ↦ ?_
  exact flat_ker_d_mappingCone (C.ιTruncLE bound) degree
    ((C.truncLE bound).isZero_of_isStrictlyLE bound _ (by omega))
    (flatCycles degree degreeBound)

end CochainComplex
