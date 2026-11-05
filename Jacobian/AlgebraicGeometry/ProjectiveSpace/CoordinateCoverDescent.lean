import Jacobian.AlgebraicGeometry.Norm.FiniteFieldBaseChange
import Jacobian.AlgebraicGeometry.ProjectiveSpace.CoordinateCover
import Jacobian.AlgebraicGeometry.ProjectiveSpace.Charts
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.FiniteSet
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-!
# Descent of affine coordinate covers along finite field extensions

Norms descend the coordinate ratios to saturated opens. Finite homogeneous
prime avoidance produces enough such opens to cover the base scheme.
-/

set_option backward.isDefEq.respectTransparency false

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section
universe schemeUniverse

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

variable {baseField extensionField : Type schemeUniverse} [Field baseField] [Field extensionField] [Algebra baseField extensionField] [Module.Finite baseField extensionField]
  {scheme source : Scheme.{schemeUniverse}} {function : scheme ⟶ Spec (.of baseField)} {projection : source ⟶ scheme} {extensionStructure : source ⟶ Spec (.of extensionField)}
  (pullbackSquare : IsPullback projection extensionStructure function (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))

namespace Scheme.CoordinateCover

variable {coverIndex : Type schemeUniverse} (coordinates : source.CoordinateCover coverIndex)

include pullbackSquare in

def saturatedPart (openSubset : source.Opens) : scheme.Opens :=
  ⟨(projection '' (openSubset : Set source)ᶜ)ᶜ, by
    have := isFinite_of_isPullback_spec pullbackSquare
    exact (projection.isClosedMap _ openSubset.isOpen.isClosed_compl).isOpen_compl⟩

lemma mem_saturatedPart {openSubset : source.Opens} {point : scheme} :
    point ∈ saturatedPart pullbackSquare openSubset ↔ ∀ sourcePoint, projection sourcePoint = point → sourcePoint ∈ openSubset := by
  change point ∉ projection '' (openSubset : Set source)ᶜ ↔ _
  simp only [Set.mem_image, Set.mem_compl_iff, SetLike.mem_coe, not_exists, not_and]
  exact ⟨fun compatibility sourcePoint hy ↦ by_contra fun h' ↦ compatibility sourcePoint h' hy, fun compatibility sourcePoint h' hy ↦ h' (compatibility sourcePoint hy)⟩

lemma preimage_saturatedPart_le (openSubset : source.Opens) : projection ⁻¹ᵁ saturatedPart pullbackSquare openSubset ≤ openSubset :=
  fun sourcePoint hy ↦ (mem_saturatedPart pullbackSquare).mp hy sourcePoint rfl

def normRatio (coordinates : source.CoordinateCover coverIndex) (index secondIndex : coverIndex) : Γ(scheme, saturatedPart pullbackSquare (coordinates.opens index)) :=
  projection.normAt _ (source.presheaf.map (homOfLE (preimage_saturatedPart_le pullbackSquare (coordinates.opens index))).op (coordinates.ratio index secondIndex))

variable {coordinates} (h𝒟 : ∀ index, IsAffineOpen (coordinates.opens index))
  (hfib : ∀ point : scheme, ∃ index, ∀ sourcePoint, projection sourcePoint = point → sourcePoint ∈ coordinates.opens index)

include h𝒟 hfib in

lemma isAffineOpen_preimage_saturatedPart (index : coverIndex) :
    IsAffineOpen (projection ⁻¹ᵁ saturatedPart pullbackSquare (coordinates.opens index)) := by
  have := isFinite_of_isPullback_spec pullbackSquare
  set Z := projection ⁻¹ᵁ saturatedPart pullbackSquare (coordinates.opens index)

  let C : Type schemeUniverse := {baseRing : scheme.Opens // IsAffineOpen baseRing ∧ ∃ secondIndex, baseRing ≤ saturatedPart pullbackSquare (coordinates.opens secondIndex)}
  have hC (baseRing : C) : IsAffineOpen (Z ⊓ projection ⁻¹ᵁ baseRing.1) := by
    obtain ⟨hA, secondIndex, hAj⟩ := baseRing.2
    have hA' : IsAffineOpen (projection ⁻¹ᵁ baseRing.1) := hA.preimage projection
    have hle : projection ⁻¹ᵁ baseRing.1 ≤ coordinates.opens secondIndex := (projection.preimage_mono hAj).trans (preimage_saturatedPart_le pullbackSquare _)
    set powerBound := projection.normAt baseRing.1 (source.presheaf.map (homOfLE hle).op (coordinates.ratio secondIndex index))
    have : Z ⊓ projection ⁻¹ᵁ baseRing.1 = source.basicOpen (projection.app baseRing.1 powerBound) := by
      rw [← Scheme.preimage_basicOpen]
      ext sourcePoint
      change projection sourcePoint ∈ saturatedPart pullbackSquare (coordinates.opens index) ∧ projection sourcePoint ∈ baseRing.1 ↔ projection sourcePoint ∈ scheme.basicOpen powerBound
      refine ⟨fun ⟨hy, hyA⟩ ↦ ?_, fun hy ↦ ?_⟩
      · refine (mem_basicOpen_normAt pullbackSquare hA _ hyA).mpr fun y' hy' ↦ ?_
        rw [Scheme.basicOpen_res, coordinates.basicOpen_ratio]
        have hy'A : y' ∈ projection ⁻¹ᵁ baseRing.1 := by change projection y' ∈ baseRing.1; rw [hy']; exact hyA
        exact ⟨hy'A, hle hy'A, (mem_saturatedPart pullbackSquare).mp hy y' hy'⟩
      · have hyA : projection sourcePoint ∈ baseRing.1 := scheme.basicOpen_le powerBound hy
        refine ⟨(mem_saturatedPart pullbackSquare).mpr fun y' hy' ↦ ?_, hyA⟩
        have := (mem_basicOpen_normAt pullbackSquare hA _ hyA).mp hy y' hy'
        rw [Scheme.basicOpen_res, coordinates.basicOpen_ratio] at this
        exact this.2.2
    rw [this]
    exact hA'.basicOpen _

  have hcov : ⨆ baseRing : C, (⟨projection ⁻¹ᵁ baseRing.1, baseRing.2.1.preimage projection⟩ : source.affineOpens).1 = ⊤ := by
    refine top_le_iff.mp fun sourcePoint _ ↦ ?_
    obtain ⟨secondIndex, hj⟩ := hfib (projection sourcePoint)
    obtain ⟨_, ⟨baseRing, hA, rfl⟩, hyA, hAj⟩ := scheme.isBasis_affineOpens.exists_subset_of_mem_open
      (a := projection sourcePoint) ((mem_saturatedPart pullbackSquare).mpr hj) (saturatedPart pullbackSquare (coordinates.opens secondIndex)).isOpen
    exact Opens.mem_iSup.mpr ⟨⟨baseRing, hA, secondIndex, hAj⟩, hyA⟩
  have hZ : IsAffineHom Z.ι := by
    refine HasAffineProperty.of_iSup_eq_top (P := @IsAffineHom)
      (fun baseRing : C ↦ (⟨projection ⁻¹ᵁ baseRing.1, baseRing.2.1.preimage projection⟩ : source.affineOpens)) hcov fun baseRing ↦ ?_
    change IsAffine (Z.ι ⁻¹ᵁ projection ⁻¹ᵁ baseRing.1).toScheme
    have : IsAffineOpen (Z.ι ''ᵁ (Z.ι ⁻¹ᵁ projection ⁻¹ᵁ baseRing.1)) := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact hC baseRing
    exact (Z.ι.isAffineOpen_iff_of_isOpenImmersion).mp this

  have hZi : IsAffineHom (source.homOfLE (preimage_saturatedPart_le pullbackSquare (coordinates.opens index))) := by
    refine ⟨fun openSubset hV ↦ ?_⟩
    have compatibility := ((coordinates.opens index).ι.isAffineOpen_iff_of_isOpenImmersion.mpr hV).preimage Z.ι
    have equivalence : source.homOfLE (preimage_saturatedPart_le pullbackSquare (coordinates.opens index)) ⁻¹ᵁ openSubset =
        Z.ι ⁻¹ᵁ (coordinates.opens index).ι ''ᵁ openSubset := by
      rw [← Scheme.homOfLE_ι _ (preimage_saturatedPart_le pullbackSquare _), Scheme.Hom.comp_preimage,
        Scheme.Hom.preimage_image_eq]
    rw [equivalence]
    exact compatibility
  have : IsAffine (coordinates.opens index).toScheme := h𝒟 index
  exact isAffine_of_isAffineHom (source.homOfLE (preimage_saturatedPart_le pullbackSquare (coordinates.opens index)))

include h𝒟 hfib in
lemma isAffineOpen_saturatedPart (index : coverIndex) : IsAffineOpen (saturatedPart pullbackSquare (coordinates.opens index)) :=
  isAffineOpen_of_isAffineOpen_preimage pullbackSquare (isAffineOpen_preimage_saturatedPart pullbackSquare h𝒟 hfib index)

include h𝒟 hfib in
lemma basicOpen_normRatio (index secondIndex : coverIndex) :
    scheme.basicOpen (normRatio pullbackSquare coordinates index secondIndex) = saturatedPart pullbackSquare (coordinates.opens index) ⊓ saturatedPart pullbackSquare (coordinates.opens secondIndex) := by
  have hW := isAffineOpen_saturatedPart pullbackSquare h𝒟 hfib index
  ext point
  refine ⟨fun hx ↦ ⟨scheme.basicOpen_le _ hx, ?_⟩, fun ⟨hxi, hxj⟩ ↦ ?_⟩
  · have := (mem_basicOpen_normAt pullbackSquare hW _ (scheme.basicOpen_le _ hx)).mp hx
    refine (mem_saturatedPart pullbackSquare).mpr fun sourcePoint hy ↦ ?_
    have compatibility := this sourcePoint hy
    rw [Scheme.basicOpen_res, coordinates.basicOpen_ratio] at compatibility
    exact compatibility.2.2
  · refine (mem_basicOpen_normAt pullbackSquare hW _ hxi).mpr fun sourcePoint hy ↦ ?_
    rw [Scheme.basicOpen_res, coordinates.basicOpen_ratio]
    have hyW : sourcePoint ∈ projection ⁻¹ᵁ saturatedPart pullbackSquare (coordinates.opens index) := by
      rw [Scheme.Hom.mem_preimage, hy]; exact hxi
    exact ⟨hyW, preimage_saturatedPart_le pullbackSquare _ hyW, (mem_saturatedPart pullbackSquare).mp hxj sourcePoint hy⟩

include pullbackSquare h𝒟 hfib in

theorem exists_descent : ∃ 𝒟' : scheme.CoordinateCover coverIndex, ∀ index, IsAffineOpen (𝒟'.opens index) := by
  refine ⟨{ opens := fun index ↦ saturatedPart pullbackSquare (coordinates.opens index)
            ratio := normRatio pullbackSquare coordinates
            ratio_self := fun index ↦ by simp [normRatio, coordinates.ratio_self]
            basicOpen_ratio := basicOpen_normRatio pullbackSquare h𝒟 hfib
            ratio_mul := fun index secondIndex thirdIndex ↦ ?_
            iSup_U := ?_ }, isAffineOpen_saturatedPart pullbackSquare h𝒟 hfib⟩
  · set openSubset := saturatedPart pullbackSquare (coordinates.opens index) ⊓ saturatedPart pullbackSquare (coordinates.opens secondIndex)
    have hVi : openSubset = scheme.basicOpen (normRatio pullbackSquare coordinates index secondIndex) := (basicOpen_normRatio pullbackSquare h𝒟 hfib index secondIndex).symm
    have hVj : openSubset = scheme.basicOpen (normRatio pullbackSquare coordinates secondIndex index) := by
      rw [basicOpen_normRatio pullbackSquare h𝒟 hfib secondIndex index, inf_comm]
    have hi := isAffineOpen_saturatedPart pullbackSquare h𝒟 hfib index
    have hj := isAffineOpen_saturatedPart pullbackSquare h𝒟 hfib secondIndex
    rw [normRatio, normRatio, normRatio,
      ← normAt_map_of_eq_basicOpen pullbackSquare hi _ hVi, ← normAt_map_of_eq_basicOpen pullbackSquare hi _ hVi,
      ← normAt_map_of_eq_basicOpen pullbackSquare hj _ hVj, ← map_mul]
    congr 1
    have hle : projection ⁻¹ᵁ openSubset ≤ coordinates.opens index ⊓ coordinates.opens secondIndex :=
      le_inf ((projection.preimage_mono inf_le_left).trans (preimage_saturatedPart_le pullbackSquare _))
        ((projection.preimage_mono inf_le_right).trans (preimage_saturatedPart_le pullbackSquare _))
    have := congrArg (source.presheaf.map (homOfLE hle).op) (coordinates.ratio_mul index secondIndex thirdIndex)
    simp only [map_mul, Scheme.presheaf_map_map] at this ⊢
    exact this
  · refine top_le_iff.mp fun point _ ↦ ?_
    obtain ⟨index, hi⟩ := hfib point
    exact Opens.mem_iSup.mpr ⟨index, (mem_saturatedPart pullbackSquare).mpr hi⟩

end Scheme.CoordinateCover

attribute [local instance] MvPolynomial.gradedAlgebra

include pullbackSquare in

theorem exists_coordinateCover_of_isPullback [CompactSpace scheme] {newIndex : Type schemeUniverse}
    (ψ : source ⟶ ℙ(newIndex; Spec (.of extensionField)))
    (hψ : ∀ otherCoordinate, IsAffineOpen (ψ ⁻¹ᵁ ProjectiveSpace.standardOpen newIndex (Spec (.of extensionField)) otherCoordinate)) :
    ∃ (coverIndex : Type schemeUniverse) (_ : Finite coverIndex) (coordinates : scheme.CoordinateCover coverIndex), ∀ index, IsAffineOpen (coordinates.opens index) := by
  classical
  have := isFinite_of_isPullback_spec pullbackSquare
  have hψa : IsAffineHom ψ := HasAffineProperty.of_iSup_eq_top (P := @IsAffineHom)
    (fun otherCoordinate ↦ ⟨_, ProjectiveSpace.isAffineOpen_standardOpen newIndex (Spec (.of extensionField)) otherCoordinate⟩)
    (ProjectiveSpace.iSup_standardOpen _ _) fun otherCoordinate ↦ hψ otherCoordinate
  have hτ : IsAffineHom (ProjectiveSpace.toIntegralModel newIndex (Spec (.of extensionField))) :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ inferInstance
  set grading := MvPolynomial.homogeneousSubmodule newIndex (ULift.{schemeUniverse} ℤ)
  let restriction := ψ ≫ ProjectiveSpace.toIntegralModel newIndex (Spec (.of extensionField))
  have hρ {degree : ℕ} (hd : 0 < degree) {G : MvPolynomial newIndex (ULift.{schemeUniverse} ℤ)} (hG : G ∈ grading degree) :
      IsAffineOpen (restriction ⁻¹ᵁ Proj.basicOpen grading G) :=
    ((Proj.isAffineOpen_basicOpen grading G hG hd).preimage _).preimage ψ

  have key (point : scheme) : ∃ degree > 0, ∃ G ∈ grading degree, ∀ sourcePoint, projection sourcePoint = point → sourcePoint ∈ restriction ⁻¹ᵁ Proj.basicOpen grading G := by
    have hfin : (projection ⁻¹' {point}).Finite := projection.finite_preimage_singleton point
    obtain ⟨degree, hd, G, hG, hGs⟩ :=
      ProjectiveSpectrum.exists_homogeneous_notMem_of_finset (hfin.toFinset.image restriction)
    exact ⟨degree, hd, G, hG, fun sourcePoint hy ↦ hGs (restriction sourcePoint) (Finset.mem_image_of_mem _ (by simpa using hy))⟩
  choose degree hd G hG hGx using key
  obtain ⟨otherElement, ht⟩ := CompactSpace.elim_nhds_subcover
    (fun point ↦ (Scheme.CoordinateCover.saturatedPart pullbackSquare (restriction ⁻¹ᵁ Proj.basicOpen grading (G point)) : Set scheme))
    fun point ↦ (Scheme.CoordinateCover.saturatedPart pullbackSquare _).isOpen.mem_nhds
      ((Scheme.CoordinateCover.mem_saturatedPart pullbackSquare).mpr (hGx point))
  set D := ∏ point ∈ otherElement, degree point
  have hdD (point : otherElement) : degree point ∣ D := Finset.dvd_prod_of_mem _ point.2
  have hD : 0 < D := Finset.prod_pos fun point _ ↦ hd point
  let finiteSet : otherElement → MvPolynomial newIndex (ULift.{schemeUniverse} ℤ) := fun point ↦ G point ^ (D / degree point)
  have hF (point : otherElement) : finiteSet point ∈ grading D := by
    have := SetLike.pow_mem_graded (D / degree point) (hG point)
    rwa [smul_eq_mul, Nat.div_mul_cancel (hdD point)] at this
  have hFb (point : otherElement) : Proj.basicOpen grading (finiteSet point) = Proj.basicOpen grading (G point) :=
    Proj.basicOpen_pow _ _ _ (Nat.div_pos (Nat.le_of_dvd hD (hdD point)) (hd point))

  have hfib (x' : scheme) : ∃ index : otherElement, ∀ sourcePoint, projection sourcePoint = x' → sourcePoint ∈ restriction ⁻¹ᵁ Proj.basicOpen grading (finiteSet index) := by
    obtain ⟨point, hx, hx'⟩ := Set.mem_iUnion₂.mp (ht.ge (Set.mem_univ x'))
    refine ⟨⟨point, hx⟩, fun sourcePoint hy ↦ ?_⟩
    rw [hFb]
    exact (Scheme.CoordinateCover.mem_saturatedPart pullbackSquare).mp hx' sourcePoint hy
  have hcovY : ⨆ index : otherElement, restriction ⁻¹ᵁ Proj.basicOpen grading (finiteSet index) = ⊤ := by
    refine top_le_iff.mp fun sourcePoint _ ↦ ?_
    obtain ⟨index, hi⟩ := hfib (projection sourcePoint)
    exact Opens.mem_iSup.mpr ⟨index, hi sourcePoint rfl⟩
  let coordinates := Scheme.CoordinateCover.ofProj grading restriction hD finiteSet hF hcovY
  obtain ⟨𝒟', h𝒟'⟩ := Scheme.CoordinateCover.exists_descent pullbackSquare (coordinates := coordinates)
    (fun index ↦ hρ hD (hF index)) hfib
  exact ⟨otherElement, inferInstance, 𝒟', h𝒟'⟩

end AlgebraicGeometry
