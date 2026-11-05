import Jacobian.FieldTheory.IntermediateField.FilteredColimit
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Tensor diagonals over algebraic extensions

The kernel of multiplication dies over firstFactor finite intermediate field. Multiplication
therefore exhibits the extension as the filtered colimit of its tensor diagonals.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe fieldUniverse

open TensorProduct

namespace IntermediateField

section Kernel

variable {baseField extensionField : Type*} [Field baseField] [Field extensionField] [Algebra baseField extensionField]

/-- For `element ∈ subextension`, the elements `1 ⊗ element` and `element ⊗ 1` of `extensionField ⊗_L extensionField` agree. -/
lemma one_tmul_eq_tmul_one (subextension : IntermediateField baseField extensionField) {element : extensionField} (hs : element ∈ subextension) :
    (1 : extensionField) ⊗ₜ[subextension] element = element ⊗ₜ[subextension] (1 : extensionField) := by
  have scalarExpression : element = (⟨element, hs⟩ : subextension) • (1 : extensionField) := by
    rw [Algebra.smul_def, mul_one]
    rfl
  rw [scalarExpression, smul_tmul]

/-- **The kernel of multiplication dies at firstFactor finite level.** Let `extensionField/baseField` be algebraic and let
`tensorElement ∈ extensionField ⊗_F extensionField` be killed by the multiplication map `extensionField ⊗_F extensionField → extensionField`. Then the image of `tensorElement` in
`extensionField ⊗_L extensionField` vanishes for some intermediate field `subextension` which is finite over `baseField`. -/
theorem exists_finiteDimensional_mapOfCompatibleSMul_eq_zero [Algebra.IsAlgebraic baseField extensionField]
    (tensorElement : extensionField ⊗[baseField] extensionField) (hx : Algebra.TensorProduct.lmul' baseField tensorElement = 0) :
    ∃ subextension : IntermediateField baseField extensionField, FiniteDimensional baseField subextension ∧
      mapOfCompatibleSMul subextension baseField extensionField extensionField extensionField tensorElement = 0 := by
  have hmem : tensorElement ∈ (KaehlerDifferential.ideal baseField extensionField).restrictScalars extensionField := by
    change tensorElement ∈ RingHom.ker (Algebra.TensorProduct.lmul' baseField (S := extensionField))
    exact hx
  rw [← KaehlerDifferential.submodule_span_range_eq_ideal,
    Finsupp.mem_span_range_iff_exists_finsupp] at hmem
  obtain ⟨coefficients, rfl⟩ := hmem
  let subextension := IntermediateField.adjoin baseField (coefficients.support : Set extensionField)
  have hL : FiniteDimensional baseField subextension :=
    IntermediateField.finiteDimensional_adjoin fun element _ ↦ Algebra.IsIntegral.isIntegral element
  refine ⟨subextension, hL, ?_⟩
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun element hs ↦ ?_
  rw [map_smul, map_sub, mapOfCompatibleSMul_tmul, mapOfCompatibleSMul_tmul,
    one_tmul_eq_tmul_one subextension (IntermediateField.subset_adjoin baseField _ hs), sub_self, smul_zero]


end Kernel

section Colimit

open CategoryTheory Limits

variable (baseField extensionField : Type fieldUniverse) [Field baseField]
  [Field extensionField] [Algebra baseField extensionField]

/-- The diagram `subextension ↦ extensionField ⊗_L extensionField` over the finite subextensions of `extensionField/baseField`. -/
noncomputable def diagonalDiagram : FiniteSubext baseField extensionField ⥤ CommRingCat.{fieldUniverse} where
  obj subextension := .of (extensionField ⊗[subextension.1] extensionField)
  map {subextension largerSubextension} transition :=
    letI : Algebra subextension.1 largerSubextension.1 := (IntermediateField.inclusion (leOfHom transition)).toRingHom.toAlgebra
    haveI : IsScalarTower subextension.1 largerSubextension.1 extensionField := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
    CommRingCat.ofHom
      (Algebra.TensorProduct.mapOfCompatibleSMul largerSubextension.1 subextension.1 extensionField extensionField extensionField).toRingHom
  map_id subextension := by
    refine CommRingCat.hom_ext (RingHom.ext fun tensorElement ↦ ?_)
    induction tensorElement using TensorProduct.induction_on with
    | zero => simp
    | tmul firstFactor secondFactor => rfl
    | add tensorElement secondTensor hx hy => simp_all
  map_comp transition nextTransition := by
    refine CommRingCat.hom_ext (RingHom.ext fun tensorElement ↦ ?_)
    induction tensorElement using TensorProduct.induction_on with
    | zero => simp
    | tmul firstFactor secondFactor => rfl
    | add tensorElement secondTensor hx hy => simp_all

/-- `extensionField` as firstFactor cocone over the diagram `subextension ↦ extensionField ⊗_L extensionField`, through the multiplication maps. -/
noncomputable def diagonalCocone : Cocone (diagonalDiagram baseField extensionField) where
  pt := .of extensionField
  ι :=
    { app subextension := CommRingCat.ofHom (Algebra.TensorProduct.lmul' subextension.1 (S := extensionField)).toRingHom
      naturality subextension largerSubextension transition := by
        refine CommRingCat.hom_ext (RingHom.ext fun tensorElement ↦ ?_)
        induction tensorElement using TensorProduct.induction_on with
        | zero => simp
        | tmul firstFactor secondFactor => rfl
        | add tensorElement secondTensor hx hy => simp_all }

variable {baseField extensionField} [Algebra.IsAlgebraic baseField extensionField]

/-- In firstFactor cocone over `subextension ↦ extensionField ⊗_L extensionField`, the images of `scalar ⊗ 1` and `1 ⊗ scalar` do not depend on `subextension` and
agree. -/
lemma diagonalCocone_app_tmul (cocone : Cocone (diagonalDiagram baseField extensionField)) (subextension : FiniteSubext baseField extensionField) (scalar : extensionField) :
    (cocone.ι.app subextension).hom (scalar ⊗ₜ 1) = (cocone.ι.app ⟨⊥, inferInstance⟩).hom (scalar ⊗ₜ 1) ∧
      (cocone.ι.app subextension).hom (1 ⊗ₜ scalar) = (cocone.ι.app ⟨⊥, inferInstance⟩).hom (scalar ⊗ₜ 1) := by
  have h₀ (commonSubextension : FiniteSubext baseField extensionField) (coefficient : extensionField) :
      (cocone.ι.app commonSubextension).hom (coefficient ⊗ₜ 1) = (cocone.ι.app ⟨⊥, inferInstance⟩).hom (coefficient ⊗ₜ 1) :=
    ConcreteCategory.congr_hom (cocone.w (homOfLE (show (⟨⊥, inferInstance⟩ : FiniteSubext baseField extensionField) ≤ commonSubextension from
      (bot_le : (⊥ : IntermediateField baseField extensionField) ≤ commonSubextension.1)))) (coefficient ⊗ₜ 1)
  refine ⟨h₀ subextension scalar, ?_⟩
  obtain ⟨commonSubextension, hLM, hcM⟩ :=
    @directed_of (FiniteSubext baseField extensionField) (· ≤ ·) (FiniteSubext.instIsDirected baseField extensionField) subextension
    (FiniteSubext.adjoin (baseField := baseField) scalar)
  have hc : scalar ∈ commonSubextension.1 := hcM (IntermediateField.mem_adjoin_simple_self baseField scalar)
  have h1 := ConcreteCategory.congr_hom (cocone.w (homOfLE hLM))
    (show (diagonalDiagram baseField extensionField).obj subextension from (1 : extensionField) ⊗ₜ scalar)
  refine h1.symm.trans ((congrArg (cocone.ι.app commonSubextension).hom (one_tmul_eq_tmul_one commonSubextension.1 hc)).trans ?_)
  exact h₀ commonSubextension scalar

/-- **`extensionField` is the filtered colimit of the rings `extensionField ⊗_L extensionField`** over the finite subextensions `subextension` of
an algebraic extension `extensionField/baseField`. -/
noncomputable def isColimitDiagonalCocone : IsColimit (diagonalCocone baseField extensionField) where
  desc cocone := CommRingCat.ofHom ((cocone.ι.app ⟨⊥, inferInstance⟩).hom.comp
    Algebra.TensorProduct.includeLeftRingHom)
  fac cocone subextension := by
    refine CommRingCat.hom_ext (RingHom.ext fun tensorElement ↦ ?_)
    induction tensorElement using TensorProduct.induction_on with
    | zero => simp
    | tmul firstFactor secondFactor =>
      have hab : (firstFactor ⊗ₜ[subextension.1] secondFactor : extensionField ⊗[subextension.1] extensionField) = (firstFactor ⊗ₜ 1) * (1 ⊗ₜ secondFactor) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      change (cocone.ι.app ⟨⊥, inferInstance⟩).hom ((firstFactor * secondFactor) ⊗ₜ 1) = (cocone.ι.app subextension).hom (firstFactor ⊗ₜ secondFactor)
      rw [hab, map_mul, (diagonalCocone_app_tmul cocone subextension firstFactor).1, (diagonalCocone_app_tmul cocone subextension secondFactor).2]
      erw [← map_mul]
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rfl
    | add tensorElement secondTensor hx hy => simp_all
  uniq cocone candidateMap hm := by
    ext element
    have equality := ConcreteCategory.congr_hom (hm ⟨⊥, inferInstance⟩)
      (show (diagonalDiagram baseField extensionField).obj ⟨⊥, inferInstance⟩ from element ⊗ₜ (1 : extensionField))
    change candidateMap.hom (element * 1) = _ at equality
    rw [mul_one] at equality
    exact equality

end Colimit

end IntermediateField
