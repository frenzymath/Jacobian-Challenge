import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Jacobian.RingTheory.Smooth.Reduced

/-!
# Geometric reducedness and integrality of smooth morphisms

A scheme smooth over a field is reduced, as can be checked on its standard smooth
affine neighborhoods. Applying this after base change to fields proves geometric
reducedness of smooth morphisms. Together with geometric irreducibility this gives
geometric integrality.

See the Stacks Project, Tags 056T and 01VB, for smoothness over fields and its
stability under base change.
-/

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {source target : Scheme.{schemeUniverse}}

/-- A scheme smooth over a field is reduced. -/
theorem Smooth.isReduced_of_field {BaseField : Type schemeUniverse} [Field BaseField]
    (morphism : source ⟶ Spec (.of BaseField)) [Smooth morphism] : IsReduced source := by
  choose baseOpen baseAffine sourceOpen sourceAffine mem_sourceOpen mapsTo standardSmooth
    using Smooth.exists_isStandardSmooth morphism
  have localReduced (point : source) : IsReduced (sourceOpen point).toScheme := by
    have : IsAffine (sourceOpen point).toScheme := sourceAffine point
    have : Nonempty (baseOpen point) :=
      ⟨⟨morphism point, mapsTo point (mem_sourceOpen point)⟩⟩
    have : IsDomain Γ(Spec (CommRingCat.of BaseField), baseOpen point) := inferInstance
    have : _root_.IsReduced Γ(source, sourceOpen point) :=
      (standardSmooth point).isReduced_of_isDomain
    have : _root_.IsReduced Γ((sourceOpen point).toScheme, ⊤) :=
      isReduced_of_injective (sourceOpen point).topIso.commRingCatIsoToRingEquiv
        (RingEquiv.injective _)
    exact isReduced_of_isAffine_isReduced _
  let cover : source.OpenCover := Scheme.Cover.mkOfCovers source
    (fun point ↦ (sourceOpen point).toScheme) (fun point ↦ (sourceOpen point).ι)
    (fun point ↦ ⟨point, ⟨point, mem_sourceOpen point⟩, rfl⟩) (fun point ↦ inferInstance)
  have : ∀ index, IsReduced (cover.X index) := localReduced
  exact IsReduced.of_openCover _ cover

/-- Smooth morphisms have geometrically reduced fibers. -/
instance Smooth.geometricallyReduced (morphism : source ⟶ target) [Smooth morphism] :
    GeometricallyReduced morphism := by
  rw [geometricallyReduced_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro BaseField _ basePoint
  exact Smooth.isReduced_of_field (pullback.snd morphism basePoint)

/-- A smooth geometrically irreducible morphism is geometrically integral. -/
instance (priority := low) Smooth.geometricallyIntegral (morphism : source ⟶ target)
    [Smooth morphism] [GeometricallyIrreducible morphism] : GeometricallyIntegral morphism :=
  .of_geometricallyReduced_of_geometricallyIrreducible morphism

end AlgebraicGeometry
