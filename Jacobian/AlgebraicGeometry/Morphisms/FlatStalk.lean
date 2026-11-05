import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Flat.Localization

/-!
# Flatness of the spectrum of a local ring

The canonical map from the spectrum of a stalk factors through any affine
neighbourhood as a localization followed by an open immersion.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

instance IsAffineOpen.flat_fromSpecStalk {scheme : Scheme.{u}} {openSubset : scheme.Opens}
    (affine : IsAffineOpen openSubset) {point : scheme} (membership : point ∈ openSubset) :
    Flat (affine.fromSpecStalk membership) := by
  dsimp [IsAffineOpen.fromSpecStalk]
  have : Flat (Spec.map (scheme.presheaf.germ openSubset point membership)) := by
    rw [Flat.SpecMap_iff]
    let : Algebra Γ(scheme, openSubset) (scheme.presheaf.stalk point) :=
      (scheme.presheaf.germ openSubset point membership).hom.toAlgebra
    have := affine.isLocalization_stalk ⟨point, membership⟩
    exact RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat _ (affine.primeIdealOf ⟨point, membership⟩).asIdeal.primeCompl)
  infer_instance

instance Scheme.flat_fromSpecStalk (scheme : Scheme.{u}) (point : scheme) :
    Flat (scheme.fromSpecStalk point) :=
  IsAffineOpen.flat_fromSpecStalk _ _

end AlgebraicGeometry
