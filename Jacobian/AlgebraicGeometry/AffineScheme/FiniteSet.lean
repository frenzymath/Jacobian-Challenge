import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Ideal.Operations

/-!
# Basic open neighborhoods of finite sets

Prime avoidance places a finite set of points in one basic open contained in
a prescribed open subset of an affine scheme.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- **Prime avoidance in `Spec R`.** A finite set of points of an open subset `O` of
`PrimeSpectrum R` is contained in a basic open `D(r) ⊆ O`. -/
theorem _root_.PrimeSpectrum.exists_basicOpen_le_of_finite {R : Type*} [CommRing R]
    {O : Set (PrimeSpectrum R)} (hO : IsOpen O) {t : Set (PrimeSpectrum R)} (ht : t.Finite)
    (htO : t ⊆ O) :
    ∃ r : R, t ⊆ PrimeSpectrum.basicOpen r ∧ (PrimeSpectrum.basicOpen r : Set _) ⊆ O := by
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Oᶜ).mp hO.isClosed_compl
  have hJt : ¬ (J : Set R) ⊆ ⋃ I ∈ PrimeSpectrum.asIdeal '' t, ((id I : Ideal R) : Set R) := by
    rw [Ideal.subset_union_prime_finite (ht.image _) (f := id) ⊥ ⊥
      (by grind [PrimeSpectrum.isPrime])]
    rintro ⟨_, ⟨p, hp, rfl⟩, hle⟩
    have : p ∈ Oᶜ := hJ ▸ (PrimeSpectrum.mem_zeroLocus _ _).mpr hle
    exact this (htO hp)
  obtain ⟨r, hrJ, hr⟩ := Set.not_subset.mp hJt
  refine ⟨r, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · simp only [Set.mem_iUnion, Set.mem_image, id] at hr
    exact (PrimeSpectrum.mem_basicOpen _ _).mpr fun h ↦ hr ⟨_, ⟨p, hp, rfl⟩, h⟩
  · by_contra h
    have : p ∈ PrimeSpectrum.zeroLocus (J : Set R) := hJ ▸ h
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hp (this hrJ)

/-- **Prime avoidance for affine opens.** A finite set of points of an open `O` contained in an
affine open `U` lies in a basic open `D(r) ⊆ O` of `U`. -/
theorem IsAffineOpen.exists_basicOpen_le_of_finite {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {O : X.Opens} (hO : O ≤ U) {s : Set X} (hs : s.Finite)
    (hsO : s ⊆ O) : ∃ r : Γ(X, U), s ⊆ X.basicOpen r ∧ X.basicOpen r ≤ O := by
  obtain ⟨r, hsr, hrO⟩ := PrimeSpectrum.exists_basicOpen_le_of_finite
    (hU.fromSpec ⁻¹ᵁ O).isOpen (hs.preimage hU.fromSpec.isOpenEmbedding.injective.injOn)
    (Set.preimage_mono hsO)
  refine ⟨r, fun x hx ↦ ?_, ?_⟩
  · obtain ⟨y, rfl⟩ : x ∈ Set.range hU.fromSpec := hU.range_fromSpec ▸ hO (hsO hx)
    rw [SetLike.mem_coe, ← Scheme.Hom.mem_preimage, hU.fromSpec_preimage_basicOpen]
    exact hsr hx
  · rw [← hU.fromSpec_image_basicOpen]
    rintro _ ⟨y, hy, rfl⟩
    exact hrO hy


end AlgebraicGeometry
