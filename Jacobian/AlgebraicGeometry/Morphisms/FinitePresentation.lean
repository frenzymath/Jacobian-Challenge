import Jacobian.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.FinitePresentation

/-!
# Cancellation for locally finitely presented morphisms

If a composite is locally of finite presentation and its second factor is
locally of finite type, its first factor is locally of finite presentation.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Cancel a locally finite type second factor from local finite presentation. -/
theorem LocallyOfFinitePresentation.of_comp {source middle target : Scheme.{u}}
    (firstMap : source ⟶ middle) (secondMap : middle ⟶ target)
    [LocallyOfFinitePresentation (firstMap ≫ secondMap)] [LocallyOfFiniteType secondMap] :
    LocallyOfFinitePresentation firstMap :=
  HasRingHomProperty.of_comp_of (P' := @LocallyOfFiniteType)
    (fun _ _ finiteType finitePresentation ↦
      finitePresentation.of_comp_finiteType _ finiteType) ‹_› ‹_›

end AlgebraicGeometry
