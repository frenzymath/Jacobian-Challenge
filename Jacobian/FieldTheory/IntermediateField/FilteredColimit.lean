import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Algebraic extensions as filtered colimits of finite subextensions

Finite intermediate fields form a directed system. Its inclusions exhibit the
whole algebraic extension as a colimit of commutative rings.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe fieldUniverse

open CategoryTheory Limits

namespace IntermediateField

variable (baseField extensionField : Type fieldUniverse) [Field baseField]
  [Field extensionField] [Algebra baseField extensionField]

/-- The intermediate fields of `extensionField/baseField` which are finite over `baseField`, ordered by inclusion. -/
abbrev FiniteSubext : Type fieldUniverse := {subextension : IntermediateField baseField extensionField // FiniteDimensional baseField subextension}

instance FiniteSubext.instNonempty : Nonempty (FiniteSubext baseField extensionField) := ⟨⟨⊥, inferInstance⟩⟩

instance FiniteSubext.instIsDirected : IsDirected (FiniteSubext baseField extensionField) (· ≤ ·) where
  directed firstSubextension secondSubextension := by
    have := firstSubextension.2
    have := secondSubextension.2
    exact ⟨⟨firstSubextension.1 ⊔ secondSubextension.1, IntermediateField.finiteDimensional_sup _ _⟩, le_sup_left (a := firstSubextension.1),
      le_sup_right (a := firstSubextension.1)⟩

instance FiniteSubext.instIsFiltered : IsFiltered (FiniteSubext baseField extensionField) :=
  @isFiltered_of_directed_le_nonempty _ _ (FiniteSubext.instIsDirected baseField extensionField) _

variable {baseField extensionField} [Algebra.IsAlgebraic baseField extensionField]

/-- The finite subextension `baseField(element)` of `extensionField/baseField`. -/
noncomputable def FiniteSubext.adjoin (element : extensionField) : FiniteSubext baseField extensionField :=
  ⟨IntermediateField.adjoin baseField {element},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral element)⟩

variable (baseField extensionField) in
/-- The diagram `subextension ↦ subextension` of the finite subextensions of `extensionField/baseField`. -/
noncomputable def subextDiagram : FiniteSubext baseField extensionField ⥤ CommRingCat.{fieldUniverse} where
  obj subextension := .of subextension.1
  map {subextension L'} transition := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom transition)).toRingHom

variable (baseField extensionField) in
/-- `extensionField` as a cocone over its finite subextensions. -/
noncomputable def subextCocone : Cocone (subextDiagram baseField extensionField) where
  pt := .of extensionField
  ι := { app subextension := CommRingCat.ofHom (algebraMap subextension.1 extensionField) }

/-- In a cocone over the finite subextensions, the image of `element ∈ subextension` does not depend on `subextension`. -/
lemma subextCocone_app_adjoin (cocone : Cocone (subextDiagram baseField extensionField)) (subextension : FiniteSubext baseField extensionField) (element : subextension.1) :
    (cocone.ι.app (FiniteSubext.adjoin (element : extensionField))).hom
      ⟨element, IntermediateField.mem_adjoin_simple_self baseField (element : extensionField)⟩ = (cocone.ι.app subextension).hom element := by
  obtain ⟨commonSubextension, hLM, hxM⟩ :=
    @directed_of (FiniteSubext baseField extensionField) (· ≤ ·) (FiniteSubext.instIsDirected baseField extensionField) subextension
      (FiniteSubext.adjoin (element : extensionField))
  exact (ConcreteCategory.congr_hom (cocone.w (homOfLE hxM))
    ⟨element, IntermediateField.mem_adjoin_simple_self baseField (element : extensionField)⟩).symm.trans
    (ConcreteCategory.congr_hom (cocone.w (homOfLE hLM)) element)

/-- **`extensionField` is the filtered colimit of its finite subextensions**, for `extensionField/baseField` algebraic. -/
noncomputable def isColimitSubextCocone : IsColimit (subextCocone baseField extensionField) where
  desc cocone := CommRingCat.ofHom
    { toFun element := (cocone.ι.app (FiniteSubext.adjoin element)).hom
        ⟨element, IntermediateField.mem_adjoin_simple_self baseField element⟩
      map_one' := (subextCocone_app_adjoin cocone ⟨⊥, inferInstance⟩ 1).trans (map_one _)
      map_mul' element secondElement := by
        obtain ⟨commonSubextension, hM₁, hM₂⟩ := @directed_of (FiniteSubext baseField extensionField) (· ≤ ·)
          (FiniteSubext.instIsDirected baseField extensionField) (FiniteSubext.adjoin element) (FiniteSubext.adjoin secondElement)
        have hx : element ∈ commonSubextension.1 := hM₁ (IntermediateField.mem_adjoin_simple_self baseField element)
        have hy : secondElement ∈ commonSubextension.1 := hM₂ (IntermediateField.mem_adjoin_simple_self baseField secondElement)
        exact (subextCocone_app_adjoin cocone commonSubextension ⟨element * secondElement, mul_mem hx hy⟩).trans
          ((map_mul (cocone.ι.app commonSubextension).hom (⟨element, hx⟩ : commonSubextension.1) ⟨secondElement, hy⟩).trans (congrArg₂ (· * ·)
            (subextCocone_app_adjoin cocone commonSubextension ⟨element, hx⟩).symm (subextCocone_app_adjoin cocone commonSubextension ⟨secondElement, hy⟩).symm))
      map_zero' := (subextCocone_app_adjoin cocone ⟨⊥, inferInstance⟩ 0).trans (map_zero _)
      map_add' element secondElement := by
        obtain ⟨commonSubextension, hM₁, hM₂⟩ := @directed_of (FiniteSubext baseField extensionField) (· ≤ ·)
          (FiniteSubext.instIsDirected baseField extensionField) (FiniteSubext.adjoin element) (FiniteSubext.adjoin secondElement)
        have hx : element ∈ commonSubextension.1 := hM₁ (IntermediateField.mem_adjoin_simple_self baseField element)
        have hy : secondElement ∈ commonSubextension.1 := hM₂ (IntermediateField.mem_adjoin_simple_self baseField secondElement)
        exact (subextCocone_app_adjoin cocone commonSubextension ⟨element + secondElement, add_mem hx hy⟩).trans
          ((map_add (cocone.ι.app commonSubextension).hom (⟨element, hx⟩ : commonSubextension.1) ⟨secondElement, hy⟩).trans (congrArg₂ (· + ·)
            (subextCocone_app_adjoin cocone commonSubextension ⟨element, hx⟩).symm (subextCocone_app_adjoin cocone commonSubextension ⟨secondElement, hy⟩).symm)) }
  fac cocone subextension := by
    refine CommRingCat.hom_ext (RingHom.ext fun element ↦ ?_)
    exact subextCocone_app_adjoin cocone subextension element
  uniq cocone candidateMap hm := by
    refine CommRingCat.hom_ext (RingHom.ext fun (element : extensionField) ↦ ?_)
    exact (ConcreteCategory.congr_hom (hm (FiniteSubext.adjoin element))
      ⟨element, IntermediateField.mem_adjoin_simple_self baseField element⟩)

end IntermediateField
