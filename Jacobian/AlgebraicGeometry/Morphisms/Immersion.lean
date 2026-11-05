import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Composition of immersions with open immersions

An immersion followed by an open immersion is an immersion. This gives the
right-composition property used when checking immersions on a cover of the target.
-/

namespace AlgebraicGeometry.IsImmersion

instance respectsRight_isOpenImmersion :
    CategoryTheory.MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion where
  postcomp openImmersion isOpenImmersion immersion isImmersion := by
    have : IsOpenImmersion openImmersion := isOpenImmersion
    have : IsImmersion immersion := isImmersion
    infer_instance

end AlgebraicGeometry.IsImmersion
