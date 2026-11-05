import Jacobian.RingTheory.Norm.Prime
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Basic opens defined by norms

On an affine open where a finite morphism is free, the norm of a section is
nonvanishing precisely when that section is nonvanishing at every point of the fibre.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

private theorem IsAffineOpen.fromSpec_mem_basicOpen_iff
    {base : Scheme.{schemeUniverse}} {openSubset : base.Opens} (affine : IsAffineOpen openSubset)
    (prime : PrimeSpectrum Γ(base, openSubset)) (element : Γ(base, openSubset)) :
    affine.fromSpec prime ∈ base.basicOpen element ↔ element ∉ prime.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← affine.fromSpec_preimage_basicOpen]
  rfl

/-- The basic open defined by a norm consists of fibres on which the section never vanishes. -/
theorem mem_basicOpen_norm_of_free {base source : Scheme.{schemeUniverse}}
    (projection : source ⟶ base) [IsFinite projection] {openSubset : base.Opens}
    (affine : IsAffineOpen openSubset)
    (hfree : letI := (projection.app openSubset).hom.toAlgebra; Module.Free Γ(base, openSubset) Γ(source, projection ⁻¹ᵁ openSubset))
    (element : Γ(source, projection ⁻¹ᵁ openSubset)) {point : base} (point_mem : point ∈ openSubset) :
    letI := (projection.app openSubset).hom.toAlgebra
    point ∈ base.basicOpen (Algebra.norm Γ(base, openSubset) element) ↔
      ∀ fiberPoint, projection fiberPoint = point → fiberPoint ∈ source.basicOpen element := by
  letI := (projection.app openSubset).hom.toAlgebra
  letI := hfree
  have preimageAffine : IsAffineOpen (projection ⁻¹ᵁ openSubset) := affine.preimage projection
  obtain ⟨prime, rfl⟩ : point ∈ Set.range affine.fromSpec := by rwa [affine.range_fromSpec]
  have point_map (overPrime : Spec Γ(source, projection ⁻¹ᵁ openSubset)) :
      projection (preimageAffine.fromSpec overPrime) = affine.fromSpec (PrimeSpectrum.comap (projection.app openSubset).hom overPrime) := by
    have := congrArg (fun g ↦ g overPrime) (IsAffineOpen.SpecMap_appLE_fromSpec projection affine preimageAffine le_rfl)
    simp only [Scheme.Hom.comp_apply, Spec.map_apply] at this
    rw [← this, ← Scheme.Hom.app_eq_appLE]
  rw [affine.fromSpec_mem_basicOpen_iff]
  have : Module.Finite Γ(base, openSubset) Γ(source, projection ⁻¹ᵁ openSubset) := projection.finite_app openSubset affine
  refine (Algebra.norm_notMem_iff prime.asIdeal element).trans
    ⟨fun fiber_nonvanishing fiberPoint fiber_eq ↦ ?_,
      fun fiber_nonvanishing overIdeal overIdeal_isPrime overIdeal_comap ↦ ?_⟩
  · obtain ⟨overPrime, rfl⟩ : fiberPoint ∈ Set.range preimageAffine.fromSpec := by
      rw [preimageAffine.range_fromSpec]
      change projection fiberPoint ∈ openSubset
      rw [fiber_eq]
      exact (Set.ext_iff.mp affine.range_fromSpec _).mp ⟨prime, rfl⟩
    rw [preimageAffine.fromSpec_mem_basicOpen_iff]
    refine fiber_nonvanishing overPrime.asIdeal overPrime.isPrime ?_
    rw [point_map] at fiber_eq
    exact congrArg PrimeSpectrum.asIdeal (affine.fromSpec.isOpenEmbedding.injective fiber_eq)
  · have := fiber_nonvanishing (preimageAffine.fromSpec ⟨overIdeal, overIdeal_isPrime⟩) (by
      rw [point_map]
      congr 1
      exact PrimeSpectrum.ext overIdeal_comap)
    rwa [preimageAffine.fromSpec_mem_basicOpen_iff] at this
end AlgebraicGeometry
