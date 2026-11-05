import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Products and base change

Cartesian squares are unchanged by replacing a terminal base, and products of
base changes are base changes of products.
-/

namespace CategoryTheory.IsPullback

open Limits

variable {categoryType : Type*} [Category* categoryType]

/-- A cartesian square over a terminal object is cartesian over any other terminal object. -/
theorem of_isTerminal {productObject firstObject secondObject baseObject targetBase : categoryType}
    {firstProjection : productObject ⟶ firstObject} {secondProjection : productObject ⟶ secondObject}
    {firstMap : firstObject ⟶ baseObject} {secondMap : secondObject ⟶ baseObject}
    (square : IsPullback firstProjection secondProjection firstMap secondMap)
    (terminalBase : IsTerminal baseObject)
    {targetFirst : firstObject ⟶ targetBase} {targetSecond : secondObject ⟶ targetBase}
    (terminalTarget : IsTerminal targetBase) :
    IsPullback firstProjection secondProjection targetFirst targetSecond :=
  mk' (terminalTarget.hom_ext _ _)
    (fun _ _ _ first_eq second_eq ↦ square.hom_ext first_eq second_eq)
    (fun _ firstLeg secondLeg _ ↦ ⟨square.lift firstLeg secondLeg (terminalBase.hom_ext _ _),
      square.lift_fst .., square.lift_snd ..⟩)

variable {baseObject sourceBase firstObject secondObject pulledFirst pulledSecond sourceProduct targetProduct : categoryType}
    {baseMap : sourceBase ⟶ baseObject} {firstMap : firstObject ⟶ baseObject}
    {secondMap : secondObject ⟶ baseObject}
    {firstStructure : pulledFirst ⟶ sourceBase} {firstProjection : pulledFirst ⟶ firstObject}
    {secondStructure : pulledSecond ⟶ sourceBase} {secondProjection : pulledSecond ⟶ secondObject}
    {sourceFirst : sourceProduct ⟶ pulledFirst} {sourceSecond : sourceProduct ⟶ pulledSecond}
    {targetFirst : targetProduct ⟶ firstObject} {targetSecond : targetProduct ⟶ secondObject}

/-- A product of two base changes is a base change of the product. -/
theorem baseChange_pullback' (firstSquare : IsPullback firstStructure firstProjection baseMap firstMap)
    (secondSquare : IsPullback secondStructure secondProjection baseMap secondMap)
    (sourceSquare : IsPullback sourceFirst sourceSecond firstStructure secondStructure)
    (targetSquare : IsPullback targetFirst targetSecond firstMap secondMap)
    {productMap : sourceProduct ⟶ targetProduct}
    (first_eq : productMap ≫ targetFirst = sourceFirst ≫ firstProjection)
    (second_eq : productMap ≫ targetSecond = sourceSecond ≫ secondProjection) :
    IsPullback (sourceFirst ≫ firstStructure) productMap baseMap (targetFirst ≫ firstMap) := by
  have square : IsPullback productMap sourceFirst targetFirst firstProjection := by
    refine of_right ?_ first_eq targetSquare.flip
    rw [second_eq, ← firstSquare.w]
    exact sourceSquare.flip.paste_horiz secondSquare.flip
  exact (square.paste_vert firstSquare.flip).flip

end CategoryTheory.IsPullback
