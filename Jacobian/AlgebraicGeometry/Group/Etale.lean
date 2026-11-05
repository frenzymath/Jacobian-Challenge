import Jacobian.AlgebraicGeometry.Morphisms.EtaleSection
import Jacobian.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-!
# Triviality of connected étale group schemes

The unit section identifies a preconnected separated étale commutative group
scheme over a nonempty base with the trivial group scheme. In particular, this
applies to geometrically irreducible smooth group schemes of relative dimension
zero over a field.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace CategoryTheory.CommGrp

/-- A preconnected separated étale commutative group scheme over a nonempty
base is the trivial group scheme. -/
theorem nonempty_iso_trivial_of_etale {base : Scheme.{u}}
    (group : CommGrp (Over base)) [Etale group.X.hom] [IsSeparated group.X.hom]
    [PreconnectedSpace group.X.left] [Nonempty base] :
    Nonempty (group ≅ trivial (Over base)) := by
  haveI : IsIso (η[group.X]).left :=
    isIso_section_of_etale_connected group.X.hom (η[group.X]).left (Over.w _)
  haveI : IsIso ((Over.forget base).map (η[group.X])) :=
    inferInstanceAs (IsIso (η[group.X]).left)
  haveI : IsIso (η[group.X]) :=
    isIso_of_reflects_iso (η[group.X]) (Over.forget base)
  let unitIso : 𝟙_ (Over base) ≅ group.X := asIso (η[group.X])
  exact ⟨(mkIso' unitIso).symm⟩

/-- A geometrically irreducible smooth commutative group scheme of relative
dimension zero over a field is trivial. -/
theorem nonempty_iso_trivial_of_smoothOfRelativeDimension_zero
    {baseField : Type u} [Field baseField]
    (group : CommGrp (Over (Spec (.of baseField))))
    [SmoothOfRelativeDimension 0 group.X.hom] [IsSeparated group.X.hom]
    [GeometricallyIrreducible group.X.hom] :
    Nonempty (group ≅ trivial (Over (Spec (.of baseField)))) := by
  haveI : Etale group.X.hom :=
    (Etale.iff_smoothOfRelativeDimension_zero _).mpr inferInstance
  letI : IrreducibleSpace group.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := group.X.hom)
  exact nonempty_iso_trivial_of_etale group

end CategoryTheory.CommGrp
