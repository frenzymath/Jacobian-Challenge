import Jacobian.AlgebraicGeometry.Hilbert.Separated
import Jacobian.AlgebraicGeometry.Hilbert.UniversalFamily
import Jacobian.AlgebraicGeometry.Curve.AffineNeighborhood
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Hilbert schemes from affine neighborhoods of finite sets

If every finite subset of a separated scheme lies in an affine open, all its
finite flat Hilbert functors are representable. The condition is imposed on
the source and therefore supplies the required neighborhoods in every fiber.
For smooth proper geometrically integral curves the finite-set condition holds,
so their finite flat Hilbert functors are representable in every degree.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Finite subsets with affine neighborhoods give representing schemes for every degree. -/
theorem isRepresentable_hilbertPresheaf_of_finite_affine_neighborhoods
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (affineNeighborhoods : ∀ finiteSet : Finset X,
      ∃ affineOpen : X.affineOpens, ∀ point ∈ finiteSet, point ∈ affineOpen.1)
    (degree : ℕ) : (hilbertPresheaf f degree).IsRepresentable := by
  classical
  refine isRepresentable_hilbertPresheaf f degree fun parameter finiteSet _ ↦ ?_
  obtain ⟨affineOpen, contains⟩ :=
    affineNeighborhoods (finiteSet.image (f.fiberι parameter).base)
  exact ⟨affineOpen, fun point membership ↦
    contains _ (Finset.mem_image_of_mem _ membership)⟩

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
  (structureMap : source ⟶ Spec (.of baseField))

/-- Every finite set on a smooth proper geometrically integral curve lies in an affine open. -/
theorem exists_affineOpens_forall_mem_of_curve [SmoothOfRelativeDimension 1 structureMap]
    [IsProper structureMap] [GeometricallyIntegral structureMap] (points : Finset source) :
    ∃ neighborhood : source.affineOpens, ∀ point ∈ points, point ∈ neighborhood.1 := by
  letI : Subsingleton (Spec (.of baseField)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum baseField))
  letI : IsIntegral source := GeometricallyIntegral.isIntegral_of_subsingleton structureMap
  exact exists_affineOpens_forall_mem_of_smooth_integral_curve structureMap points

/-- Every finite flat Hilbert functor of a smooth proper geometrically integral curve is
representable, over an arbitrary field and without a chosen rational point. -/
theorem isRepresentable_hilbertPresheaf_curve [SmoothOfRelativeDimension 1 structureMap]
    [IsProper structureMap] [GeometricallyIntegral structureMap] (degree : ℕ) :
    (hilbertPresheaf structureMap degree).IsRepresentable :=
  isRepresentable_hilbertPresheaf_of_finite_affine_neighborhoods structureMap
    (exists_affineOpens_forall_mem_of_curve structureMap) degree

end AlgebraicGeometry
