import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Splitting an Option-indexed product

The product over `Option` is a binary product of the `none` factor and the
product of the `some` factors.
-/

noncomputable section

universe w v u

namespace CategoryTheory.Limits

variable {categoryType : Type u} [Category.{v} categoryType]

set_option backward.isDefEq.respectTransparency false in
private def binaryFanOptionPi {indexType : Type w} (family : Option indexType → categoryType)
    [HasProduct family] [HasProduct fun index ↦ family (some index)] :
    IsLimit (BinaryFan.mk (Pi.π family none) (Pi.lift fun index ↦ Pi.π family (some index)) :
      BinaryFan (family none) (∏ᶜ fun index ↦ family (some index))) :=
  BinaryFan.isLimitMk
    (fun cone ↦ Pi.lift fun index ↦ match index with
      | none => cone.fst
      | some index => cone.snd ≫ Pi.π (fun index ↦ family (some index)) index)
    (fun cone ↦ by simp)
    (fun cone ↦ by ext index; simp)
    (fun cone candidate first_eq remaining_eq ↦ by
      refine Pi.hom_ext _ _ fun index ↦ ?_
      match index with
      | none => simpa using first_eq
      | some index => rw [← remaining_eq]; simp)

/-- Split an Option-indexed product into its distinguished factor and the remaining product. -/
def piOptionIso {indexType : Type w} (family : Option indexType → categoryType)
    [HasProduct family] [HasProduct fun index ↦ family (some index)]
    [HasBinaryProduct (family none) (∏ᶜ fun index ↦ family (some index))] :
    (∏ᶜ family) ≅ family none ⨯ (∏ᶜ fun index ↦ family (some index)) :=
  (binaryFanOptionPi family).conePointUniqueUpToIso
    (limit.isLimit (pair (family none) (∏ᶜ fun index ↦ family (some index))))

end CategoryTheory.Limits
