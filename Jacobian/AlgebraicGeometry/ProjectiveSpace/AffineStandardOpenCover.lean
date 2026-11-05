import Jacobian.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverImmersion
import Jacobian.AlgebraicGeometry.AffineScheme.FiniteSet
import Jacobian.AlgebraicGeometry.Morphisms.ImmersionAffine
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Charts
import Jacobian.AlgebraicGeometry.ProjectiveSpace.OfSections
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Affine standard-open preimages for projective immersions

A quasi-compact projective immersion can be replaced by a morphism whose
standard-open preimages are affine, using extension of homogeneous sections.
-/

set_option backward.isDefEq.respectTransparency false

set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

section
universe schemeUniverse

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_isAffineOpen_preimage_of_isImmersion {scheme base : Scheme.{schemeUniverse}} [IsAffine base]
    {coordinateIndex : Type schemeUniverse} [Finite coordinateIndex] (secondIndex : scheme ⟶ ℙ(coordinateIndex; base)) [IsImmersion secondIndex] [QuasiCompact secondIndex] [CompactSpace scheme]
    [QuasiSeparatedSpace scheme] :
    ∃ (newIndex : Type schemeUniverse) (_ : Finite newIndex) (ψ : scheme ⟶ ℙ(newIndex; base)),
      ψ ≫ ℙ(newIndex; base) ↘ base = secondIndex ≫ ℙ(coordinateIndex; base) ↘ base ∧
        ∀ otherCoordinate, IsAffineOpen (ψ ⁻¹ᵁ ProjectiveSpace.standardOpen newIndex base otherCoordinate) := by
  classical
  let restriction := secondIndex ≫ ProjectiveSpace.toIntegralModel coordinateIndex base
  have hX (index : coordinateIndex) : MvPolynomial.X index ∈
      MvPolynomial.homogeneousSubmodule coordinateIndex (ULift.{schemeUniverse} ℤ) 1 :=
    MvPolynomial.X_mem_homogeneousSubmodule_one _ index
  have hpre (index : coordinateIndex) : restriction ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule coordinateIndex (ULift.{schemeUniverse} ℤ))
      (MvPolynomial.X index) = secondIndex ⁻¹ᵁ ProjectiveSpace.standardOpen coordinateIndex base index := rfl
  have hcov : ⨆ index, restriction ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule coordinateIndex (ULift.{schemeUniverse} ℤ))
      (MvPolynomial.X index) = ⊤ := by
    simp only [hpre]
    rw [← Scheme.Hom.preimage_iSup, ProjectiveSpace.iSup_standardOpen, Scheme.Hom.preimage_top]
  let coordinates := Scheme.CoordinateCover.ofProj _ restriction one_pos _ hX hcov
  have hU (index : coordinateIndex) : IsCompact (coordinates.opens index : Set scheme) :=
    QuasiCompact.isCompact_preimage (f := secondIndex) _ (ProjectiveSpace.standardOpen coordinateIndex base index).2
      (ProjectiveSpace.isAffineOpen_standardOpen coordinateIndex base index).isCompact
  have hU' (index : coordinateIndex) : IsQuasiSeparated (coordinates.opens index : Set scheme) := .of_quasiSeparatedSpace _

  have key (point : scheme) : ∃ (index : coordinateIndex) (element : Γ(ℙ(coordinateIndex; base), ProjectiveSpace.standardOpen coordinateIndex base index)),
      point ∈ secondIndex ⁻¹ᵁ ℙ(coordinateIndex; base).basicOpen element ∧ ℙ(coordinateIndex; base).basicOpen element ≤ secondIndex.coborderRange := by
    obtain ⟨index, hi⟩ := Opens.mem_iSup.mp (hcov.ge (Set.mem_univ point))
    obtain ⟨element, hr, hrO⟩ :=
      (ProjectiveSpace.isAffineOpen_standardOpen coordinateIndex base index).exists_basicOpen_le_of_finite
      (inf_le_left : ProjectiveSpace.standardOpen coordinateIndex base index ⊓ secondIndex.coborderRange ≤ _)
      (Set.finite_singleton (secondIndex point)) (by
        rw [Set.singleton_subset_iff]
        exact ⟨hi, subset_coborder ⟨point, rfl⟩⟩)
    exact ⟨index, element, hr rfl, hrO.trans inf_le_right⟩
  choose index element hxr hrO using key
  have hext (point : scheme) := coordinates.exists_section hU hU' (index point) (secondIndex.app _ (element point))
  choose N₀ hN₀ using hext
  obtain ⟨otherElement, ht⟩ := CompactSpace.elim_nhds_subcover
    (fun point ↦ (secondIndex ⁻¹ᵁ ℙ(coordinateIndex; base).basicOpen (element point) : Set scheme))
    fun point ↦ (secondIndex ⁻¹ᵁ ℙ(coordinateIndex; base).basicOpen (element point)).isOpen.mem_nhds (hxr point)
  set powerBound := otherElement.sup N₀
  have hσ (point : otherElement) := hN₀ point powerBound (Finset.le_sup point.2)
  choose sectionFamily hσs hσU using hσ
  have hnv (point : otherElement) : (sectionFamily point).nonvanishing = secondIndex ⁻¹ᵁ ℙ(coordinateIndex; base).basicOpen (element point) := by
    rw [Scheme.CoordinateCover.nonvanishing_eq_basicOpen sectionFamily (fun point ↦ index point) hσU, hσs,
      Scheme.preimage_basicOpen]
  have hcov' : ⨆ point : otherElement, (sectionFamily point).nonvanishing = ⊤ := by
    refine top_le_iff.mp fun sourcePoint _ ↦ ?_
    obtain ⟨point, hx, hy⟩ := Set.mem_iUnion₂.mp (ht.ge (Set.mem_univ sourcePoint))
    exact Opens.mem_iSup.mpr ⟨⟨point, hx⟩, by rw [hnv]; exact hy⟩
  let 𝒟' := Scheme.CoordinateCover.ofSections sectionFamily (fun point ↦ index point) hσU hcov'
  have hgen (coordinate : otherElement) : Ideal.span (Set.range fun otherCoordinate ↦ (𝒟'.coordPow otherCoordinate 1).localSection coordinate) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨coordinate, rfl⟩) (by simp [𝒟'.ratio_self])
  refine ⟨otherElement, inferInstance, Scheme.CoordinateCover.hom _ hgen (secondIndex ≫ ℙ(coordinateIndex; base) ↘ base), by simp,
    fun otherCoordinate ↦ ?_⟩
  rw [Scheme.CoordinateCover.preimage_hom_standardOpen,
    Scheme.CoordinateCover.nonvanishing_coordPow _ _ one_pos,
    Scheme.CoordinateCover.ofSections_U, hnv]
  exact secondIndex.isAffineOpen_preimage_of_le_coborderRange
    ((ProjectiveSpace.isAffineOpen_standardOpen coordinateIndex base _).basicOpen _) (hrO otherCoordinate)

end AlgebraicGeometry
