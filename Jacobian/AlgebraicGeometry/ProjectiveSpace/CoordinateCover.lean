import Jacobian.AlgebraicGeometry.ProjectiveSpace.SectionsNaturality
import Jacobian.AlgebraicGeometry.Scheme.GluingMorphisms
import Jacobian.AlgebraicGeometry.Scheme.Sections
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.ChartSections
import Jacobian.RingTheory.GradedAlgebra.HomogeneousLocalization.Fractions
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Coordinate covers and their homogeneous sections

Compatible coordinate ratios on an open cover describe homogeneous sections
and morphisms to projective space. Powers of coordinate sections extend local
sections; projective spectra supply canonical coordinate covers.
-/

set_option backward.isDefEq.respectTransparency false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

structure Scheme.CoordinateCover (scheme : Scheme.{schemeUniverse}) (coverIndex : Type schemeUniverse) where

  opens : coverIndex → scheme.Opens

  ratio (index secondIndex : coverIndex) : Γ(scheme, opens index)
  ratio_self (index : coverIndex) : ratio index index = 1
  basicOpen_ratio (index secondIndex : coverIndex) : scheme.basicOpen (ratio index secondIndex) = opens index ⊓ opens secondIndex
  ratio_mul (index secondIndex thirdIndex : coverIndex) :
    scheme.presheaf.map (homOfLE (inf_le_left : opens index ⊓ opens secondIndex ≤ opens index)).op (ratio index thirdIndex) =
      scheme.presheaf.map (homOfLE (inf_le_left : opens index ⊓ opens secondIndex ≤ opens index)).op (ratio index secondIndex) *
        scheme.presheaf.map (homOfLE (inf_le_right : opens index ⊓ opens secondIndex ≤ opens secondIndex)).op (ratio secondIndex thirdIndex)
  iSup_U : ⨆ index, opens index = ⊤

namespace Scheme.CoordinateCover

variable {scheme : Scheme.{schemeUniverse}} {coverIndex : Type schemeUniverse} (coordinates : scheme.CoordinateCover coverIndex)

lemma isUnit_ratio_map (index secondIndex : coverIndex) :
    IsUnit (scheme.presheaf.map (homOfLE (inf_le_left : coordinates.opens index ⊓ coordinates.opens secondIndex ≤ coordinates.opens index)).op (coordinates.ratio index secondIndex)) :=
  scheme.isUnit_map_of_le_basicOpen _ (coordinates.basicOpen_ratio index secondIndex).ge

@[ext]
structure Section (exponent : ℕ) where

  localSection (index : coverIndex) : Γ(scheme, coordinates.opens index)
  s_eq (index secondIndex : coverIndex) :
    scheme.presheaf.map (homOfLE (inf_le_left : coordinates.opens index ⊓ coordinates.opens secondIndex ≤ coordinates.opens index)).op (localSection index) =
      scheme.presheaf.map (homOfLE (inf_le_left : coordinates.opens index ⊓ coordinates.opens secondIndex ≤ coordinates.opens index)).op (coordinates.ratio index secondIndex) ^ exponent *
        scheme.presheaf.map (homOfLE (inf_le_right : coordinates.opens index ⊓ coordinates.opens secondIndex ≤ coordinates.opens secondIndex)).op (localSection secondIndex)

variable {coordinates}

namespace Section

def mul {otherExponent exponent : ℕ} (sectionFamily : coordinates.Section otherExponent) (otherSection : coordinates.Section exponent) : coordinates.Section (otherExponent + exponent) where
  localSection index := sectionFamily.localSection index * otherSection.localSection index
  s_eq index secondIndex := by
    rw [map_mul, map_mul, sectionFamily.s_eq index secondIndex, otherSection.s_eq index secondIndex, pow_add]
    ring

@[simp]
lemma mul_s {otherExponent exponent : ℕ} (sectionFamily : coordinates.Section otherExponent) (otherSection : coordinates.Section exponent) (index : coverIndex) :
    (sectionFamily.mul otherSection).localSection index = sectionFamily.localSection index * otherSection.localSection index := rfl

def nonvanishing {exponent : ℕ} (sectionFamily : coordinates.Section exponent) : scheme.Opens :=
  ⨆ index, scheme.basicOpen (sectionFamily.localSection index)

lemma basicOpen_inf_le {exponent : ℕ} (sectionFamily : coordinates.Section exponent) (index secondIndex : coverIndex) :
    scheme.basicOpen (sectionFamily.localSection index) ⊓ coordinates.opens secondIndex ≤ scheme.basicOpen (sectionFamily.localSection secondIndex) := by
  have compatibility := congrArg scheme.basicOpen (sectionFamily.s_eq index secondIndex)
  rw [Scheme.basicOpen_res, Scheme.basicOpen_mul, Scheme.basicOpen_res,
    scheme.basicOpen_of_isUnit ((coordinates.isUnit_ratio_map index secondIndex).pow exponent)] at compatibility
  intro point ⟨hxi, hxj⟩
  have hx : point ∈ (coordinates.opens index ⊓ coordinates.opens secondIndex) ⊓ scheme.basicOpen (sectionFamily.localSection index) := ⟨⟨scheme.basicOpen_le _ hxi, hxj⟩, hxi⟩
  rw [compatibility] at hx
  exact hx.2.2

lemma nonvanishing_inf {exponent : ℕ} (sectionFamily : coordinates.Section exponent) (secondIndex : coverIndex) :
    sectionFamily.nonvanishing ⊓ coordinates.opens secondIndex = scheme.basicOpen (sectionFamily.localSection secondIndex) := by
  refine le_antisymm ?_ (le_inf (le_iSup (fun index ↦ scheme.basicOpen (sectionFamily.localSection index)) secondIndex) (scheme.basicOpen_le _))
  rw [nonvanishing, iSup_inf_eq]
  exact iSup_le fun index ↦ sectionFamily.basicOpen_inf_le index secondIndex

end Section

def coord (thirdIndex : coverIndex) : coordinates.Section 1 where
  localSection index := coordinates.ratio index thirdIndex
  s_eq index secondIndex := by rw [pow_one, coordinates.ratio_mul]

@[simp]
lemma coord_s (thirdIndex index : coverIndex) : (coordinates.coord thirdIndex).localSection index = coordinates.ratio index thirdIndex := rfl

def coordPow (thirdIndex : coverIndex) : (exponent : ℕ) → coordinates.Section exponent
  | 0 => ⟨fun _ ↦ 1, fun index secondIndex ↦ by simp⟩
  | exponent + 1 => (coordPow thirdIndex exponent).mul (coordinates.coord thirdIndex)

@[simp]
lemma coordPow_s (thirdIndex : coverIndex) (exponent : ℕ) (index : coverIndex) : (coordinates.coordPow thirdIndex exponent).localSection index = coordinates.ratio index thirdIndex ^ exponent := by
  induction exponent with
  | zero => simp [coordPow]
  | succ exponent ih => simp [coordPow, ih, pow_succ]

section Hom

variable {coordinateIndex : Type schemeUniverse} {powerBound : ℕ} (sectionFamily : coordinateIndex → coordinates.Section powerBound)
  (hσ : ∀ index, Ideal.span (Set.range fun coordinate ↦ (sectionFamily coordinate).localSection index) = ⊤) {base : Scheme.{schemeUniverse}} (structureMap : scheme ⟶ base)

include hσ in
lemma span_topIso_inv (index : coverIndex) :
    Ideal.span (Set.range fun coordinate ↦ (coordinates.opens index).topIso.inv ((sectionFamily coordinate).localSection index)) = ⊤ := by
  have := Ideal.map_span (coordinates.opens index).topIso.inv.hom (Set.range fun coordinate ↦ (sectionFamily coordinate).localSection index)
  rw [hσ index, Ideal.map_top, ← Set.range_comp] at this
  exact this.symm

def localHom (index : coverIndex) : (coordinates.opens index).toScheme ⟶ ℙ(coordinateIndex; base) :=
  ProjectiveSpace.homOfSections ((coordinates.opens index).ι ≫ structureMap) (fun coordinate ↦ (coordinates.opens index).topIso.inv ((sectionFamily coordinate).localSection index))
    (span_topIso_inv sectionFamily hσ index)

lemma homOfLE_localHom {openSubset : scheme.Opens} (index : coverIndex) (compatibility : openSubset ≤ coordinates.opens index) :
    scheme.homOfLE compatibility ≫ localHom sectionFamily hσ structureMap index = ProjectiveSpace.homOfSections (openSubset.ι ≫ structureMap)
      (fun coordinate ↦ openSubset.topIso.inv (scheme.presheaf.map (homOfLE compatibility).op ((sectionFamily coordinate).localSection index)))
      (by
        have := ProjectiveSpace.span_range_appTop_eq_top (scheme.homOfLE compatibility) (span_topIso_inv sectionFamily hσ index)
        simp only [Scheme.homOfLE_appTop_topIso_inv] at this
        exact this) := by
  rw [localHom, ProjectiveSpace.comp_homOfSections]
  congr 1
  · simp
  · funext coordinate
    exact Scheme.homOfLE_appTop_topIso_inv _ _

lemma localHom_compat (index secondIndex : coverIndex) :
    scheme.homOfLE (inf_le_left : coordinates.opens index ⊓ coordinates.opens secondIndex ≤ coordinates.opens index) ≫ localHom sectionFamily hσ structureMap index =
      scheme.homOfLE (inf_le_right : coordinates.opens index ⊓ coordinates.opens secondIndex ≤ coordinates.opens secondIndex) ≫ localHom sectionFamily hσ structureMap secondIndex := by
  rw [homOfLE_localHom, homOfLE_localHom]
  obtain ⟨schemeUniverse, hu⟩ := (coordinates.isUnit_ratio_map index secondIndex).pow powerBound
  refine (ProjectiveSpace.homOfSections_eq_of_unit_mul _
    ((Units.map (coordinates.opens index ⊓ coordinates.opens secondIndex).topIso.inv.hom.toMonoidHom schemeUniverse)⁻¹) _ _ fun coordinate ↦ ?_)
  rw [Units.eq_inv_mul_iff_mul_eq, Units.coe_map]
  change (coordinates.opens index ⊓ coordinates.opens secondIndex).topIso.inv.hom _ * (coordinates.opens index ⊓ coordinates.opens secondIndex).topIso.inv.hom _ =
    (coordinates.opens index ⊓ coordinates.opens secondIndex).topIso.inv.hom _
  rw [← map_mul, hu, ← (sectionFamily coordinate).s_eq]

def hom : scheme ⟶ ℙ(coordinateIndex; base) :=
  Scheme.Opens.glueMorphismsOfTop coordinates.opens coordinates.iSup_U (localHom sectionFamily hσ structureMap) (localHom_compat sectionFamily hσ structureMap)

@[reassoc (attr := simp)]
lemma ι_hom (index : coverIndex) : (coordinates.opens index).ι ≫ hom sectionFamily hσ structureMap = localHom sectionFamily hσ structureMap index :=
  Scheme.Opens.ι_glueMorphismsOfTop _ _ _ _ index

@[reassoc (attr := simp)]
lemma hom_over : hom sectionFamily hσ structureMap ≫ ℙ(coordinateIndex; base) ↘ base = structureMap :=
  Scheme.Opens.hom_ext_of_iSup_eq_top coordinates.opens coordinates.iSup_U _ _ fun index ↦ by
    rw [ι_hom_assoc, localHom, ProjectiveSpace.homOfSections_over]

lemma preimage_hom_standardOpen (coordinate : coordinateIndex) :
    hom sectionFamily hσ structureMap ⁻¹ᵁ ProjectiveSpace.standardOpen coordinateIndex base coordinate = (sectionFamily coordinate).nonvanishing := by
  have key (index : coverIndex) : (coordinates.opens index).ι ''ᵁ ((coordinates.opens index).ι ⁻¹ᵁ (hom sectionFamily hσ structureMap ⁻¹ᵁ
      ProjectiveSpace.standardOpen coordinateIndex base coordinate)) = scheme.basicOpen ((sectionFamily coordinate).localSection index) := by
    rw [← Scheme.Hom.comp_preimage, ι_hom, localHom,
      ProjectiveSpace.homOfSections_preimage_standardOpen,
      Scheme.Opens.ι_image_basicOpen_topIso_inv]
  apply le_antisymm
  · intro point hx
    obtain ⟨index, hi⟩ := Opens.mem_iSup.mp (coordinates.iSup_U.ge (Set.mem_univ point))
    refine Opens.mem_iSup.mpr ⟨index, ?_⟩
    rw [← key index]
    exact ⟨⟨point, hi⟩, hx, rfl⟩
  · refine iSup_le fun index ↦ ?_
    rw [← key index]
    exact Scheme.Hom.image_preimage_le _ _

end Hom

section Extension

variable (coordinates)

lemma exists_extension_aux [Finite coverIndex] (hU : ∀ index, IsCompact (coordinates.opens index : Set scheme))
    (hU' : ∀ index, IsQuasiSeparated (coordinates.opens index : Set scheme)) (i₀ : coverIndex) (compatibility : Γ(scheme, coordinates.opens i₀)) :
    ∃ (otherExponent : ℕ) (equivalence : ∀ thirdIndex, Γ(scheme, coordinates.opens thirdIndex)), ∀ thirdIndex,
      scheme.presheaf.map (homOfLE (scheme.basicOpen_le (coordinates.ratio thirdIndex i₀))).op (equivalence thirdIndex) =
        scheme.presheaf.map (homOfLE ((coordinates.basicOpen_ratio thirdIndex i₀).le.trans inf_le_right)).op compatibility *
          scheme.presheaf.map (homOfLE (scheme.basicOpen_le (coordinates.ratio thirdIndex i₀))).op (coordinates.ratio thirdIndex i₀) ^ otherExponent := by
  have := Fintype.ofFinite coverIndex
  have pullbackSquare (thirdIndex : coverIndex) := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated scheme (coordinates.opens thirdIndex) (hU thirdIndex) (hU' thirdIndex)
    (coordinates.ratio thirdIndex i₀)
    (scheme.presheaf.map (homOfLE ((coordinates.basicOpen_ratio thirdIndex i₀).le.trans inf_le_right)).op compatibility)
  choose exponent sourcePoint hy using pullbackSquare
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] at hy
  refine ⟨Finset.univ.sup exponent, fun thirdIndex ↦ sourcePoint thirdIndex * coordinates.ratio thirdIndex i₀ ^ (Finset.univ.sup exponent - exponent thirdIndex),
    fun thirdIndex ↦ ?_⟩
  rw [map_mul, hy, map_pow, mul_comm _ (scheme.presheaf.map _ compatibility), mul_assoc, ← pow_add,
    Nat.add_sub_cancel' (Finset.le_sup (Finset.mem_univ thirdIndex))]

theorem exists_section [Finite coverIndex] (hU : ∀ index, IsCompact (coordinates.opens index : Set scheme))
    (hU' : ∀ index, IsQuasiSeparated (coordinates.opens index : Set scheme)) (i₀ : coverIndex) (compatibility : Γ(scheme, coordinates.opens i₀)) :
    ∃ N₀ : ℕ, ∀ powerBound ≥ N₀, ∃ sectionFamily : coordinates.Section powerBound, sectionFamily.localSection i₀ = compatibility ∧ sectionFamily.nonvanishing ≤ coordinates.opens i₀ := by
  have := Fintype.ofFinite coverIndex
  obtain ⟨otherExponent, equivalence, he⟩ := coordinates.exists_extension_aux hU hU' i₀ compatibility

  have hV (thirdIndex l' : coverIndex) : IsCompact ((coordinates.opens thirdIndex ⊓ coordinates.opens l' : scheme.Opens) : Set scheme) := by
    rw [← coordinates.basicOpen_ratio thirdIndex l']
    exact isCompact_basicOpen scheme (hU thirdIndex) _
  have Hδ (thirdIndex l' : coverIndex) : ∃ prime : ℕ,
      scheme.presheaf.map (homOfLE (inf_le_left : coordinates.opens thirdIndex ⊓ coordinates.opens l' ≤ coordinates.opens thirdIndex)).op (coordinates.ratio thirdIndex i₀) ^ prime *
        (scheme.presheaf.map (homOfLE (inf_le_left : coordinates.opens thirdIndex ⊓ coordinates.opens l' ≤ coordinates.opens thirdIndex)).op (equivalence thirdIndex) -
          scheme.presheaf.map (homOfLE (inf_le_left : coordinates.opens thirdIndex ⊓ coordinates.opens l' ≤ coordinates.opens thirdIndex)).op
            (coordinates.ratio thirdIndex l') ^ otherExponent *
          scheme.presheaf.map (homOfLE (inf_le_right : coordinates.opens thirdIndex ⊓ coordinates.opens l' ≤ coordinates.opens l')).op (equivalence l')) =
        0 := by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact scheme (hV thirdIndex l') _ _ ?_
    simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
    set smallerOpen := scheme.basicOpen
      (scheme.presheaf.map (homOfLE (inf_le_left : coordinates.opens thirdIndex ⊓ coordinates.opens l' ≤ coordinates.opens thirdIndex)).op (coordinates.ratio thirdIndex i₀))
    have hW : smallerOpen = coordinates.opens thirdIndex ⊓ coordinates.opens l' ⊓ coordinates.opens i₀ := by
      simp only [smallerOpen, Scheme.basicOpen_res, coordinates.basicOpen_ratio]
      rw [inf_comm (coordinates.opens thirdIndex), inf_assoc, inf_assoc, ← inf_assoc (coordinates.opens thirdIndex), inf_idem, inf_comm]
    have hWl : smallerOpen ≤ scheme.basicOpen (coordinates.ratio thirdIndex i₀) := by
      rw [hW, coordinates.basicOpen_ratio]
      exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hWl' : smallerOpen ≤ scheme.basicOpen (coordinates.ratio l' i₀) := by
      rw [hW, coordinates.basicOpen_ratio]
      exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hel := congrArg (scheme.presheaf.map (homOfLE hWl).op) (he thirdIndex)
    have hel' := congrArg (scheme.presheaf.map (homOfLE hWl').op) (he l')
    have hr := congrArg (scheme.presheaf.map (homOfLE (scheme.basicOpen_le _ :
      smallerOpen ≤ coordinates.opens thirdIndex ⊓ coordinates.opens l')).op) (coordinates.ratio_mul thirdIndex l' i₀)
    simp only [map_mul, map_pow, Scheme.presheaf_map_map] at hel hel' hr
    simp only [map_sub, map_mul, map_pow, Scheme.presheaf_map_map]
    rw [hel, hel', hr]
    ring
  choose prime hp using Hδ
  set primeIdeal := Finset.univ.sup fun ll : coverIndex × coverIndex ↦ prime ll.1 ll.2
  have hP (thirdIndex l' : coverIndex) := Finset.le_sup (f := fun ll : coverIndex × coverIndex ↦ prime ll.1 ll.2)
    (Finset.mem_univ (thirdIndex, l'))
  refine ⟨otherExponent + primeIdeal + 1, fun powerBound hN ↦ ?_⟩
  obtain ⟨fourthIndex, rfl⟩ := Nat.exists_eq_add_of_le hN
  let sectionFamily : coordinates.Section (otherExponent + primeIdeal + 1) :=
    { localSection := fun thirdIndex ↦ equivalence thirdIndex * coordinates.ratio thirdIndex i₀ ^ (primeIdeal + 1)
      s_eq := fun thirdIndex l' ↦ by
        have hδ := hp thirdIndex l'
        have hr := coordinates.ratio_mul thirdIndex l' i₀
        obtain ⟨extensionStructure, hq⟩ := Nat.exists_eq_add_of_le (hP thirdIndex l')
        simp only [map_mul, map_pow]
        rw [hr] at hδ ⊢
        rw [show primeIdeal = prime thirdIndex l' + extensionStructure from hq]
        linear_combination (scheme.presheaf.map (homOfLE (inf_le_left : coordinates.opens thirdIndex ⊓ coordinates.opens l' ≤ coordinates.opens thirdIndex)).op
          (coordinates.ratio thirdIndex l') * scheme.presheaf.map (homOfLE (inf_le_right :
            coordinates.opens thirdIndex ⊓ coordinates.opens l' ≤ coordinates.opens l')).op (coordinates.ratio l' i₀)) ^ (extensionStructure + 1) * hδ }
  have hσ : sectionFamily.nonvanishing ≤ coordinates.opens i₀ := iSup_le fun thirdIndex ↦ by
    change scheme.basicOpen (equivalence thirdIndex * coordinates.ratio thirdIndex i₀ ^ (primeIdeal + 1)) ≤ _
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_pow _ _ primeIdeal.succ_pos, coordinates.basicOpen_ratio]
    exact inf_le_right.trans inf_le_right
  have hσ₀ : sectionFamily.localSection i₀ = compatibility := by
    change equivalence i₀ * coordinates.ratio i₀ i₀ ^ (primeIdeal + 1) = compatibility
    rw [coordinates.ratio_self, one_pow, mul_one]
    have e₀ : scheme.basicOpen (coordinates.ratio i₀ i₀) = coordinates.opens i₀ := by rw [coordinates.ratio_self, scheme.basicOpen_one]
    refine scheme.eq_of_map_eq_of_eq e₀ ?_
    have := he i₀
    simp only [coordinates.ratio_self, map_one, one_pow, mul_one] at this
    exact this
  refine ⟨sectionFamily.mul (coordinates.coordPow i₀ fourthIndex), ?_, ?_⟩
  · simp [hσ₀, coordinates.ratio_self]
  · refine iSup_le fun thirdIndex ↦ ?_
    rw [Section.mul_s, Scheme.basicOpen_mul]
    exact inf_le_left.trans ((le_iSup (fun thirdIndex ↦ scheme.basicOpen (sectionFamily.localSection thirdIndex)) thirdIndex).trans hσ)

end Extension

section OfSections

variable {coordinateIndex : Type schemeUniverse} {powerBound : ℕ} (sectionFamily : coordinateIndex → coordinates.Section powerBound) (chosenIndex : coordinateIndex → coverIndex)
  (hc : ∀ coordinate, (sectionFamily coordinate).nonvanishing ≤ coordinates.opens (chosenIndex coordinate)) (hcov : ⨆ coordinate, (sectionFamily coordinate).nonvanishing = ⊤)

include hc in
lemma nonvanishing_eq_basicOpen (coordinate : coordinateIndex) :
    (sectionFamily coordinate).nonvanishing = scheme.basicOpen ((sectionFamily coordinate).localSection (chosenIndex coordinate)) := by
  rw [← (sectionFamily coordinate).nonvanishing_inf (chosenIndex coordinate), inf_eq_left.mpr (hc coordinate)]

lemma isUnit_map_s (coordinate : coordinateIndex) : IsUnit (scheme.presheaf.map (homOfLE (hc coordinate)).op ((sectionFamily coordinate).localSection (chosenIndex coordinate))) :=
  scheme.isUnit_map_of_le_basicOpen _ (nonvanishing_eq_basicOpen sectionFamily chosenIndex hc coordinate).le

def ofSections : scheme.CoordinateCover coordinateIndex where
  opens coordinate := (sectionFamily coordinate).nonvanishing
  ratio coordinate otherCoordinate := scheme.presheaf.map (homOfLE (hc coordinate)).op ((sectionFamily otherCoordinate).localSection (chosenIndex coordinate)) * ↑(isUnit_map_s sectionFamily chosenIndex hc coordinate).unit⁻¹
  ratio_self coordinate := IsUnit.mul_val_inv _
  basicOpen_ratio coordinate otherCoordinate := by
    have key := ((sectionFamily otherCoordinate).nonvanishing_inf (chosenIndex coordinate)).symm
    rw [Scheme.basicOpen_mul, scheme.basicOpen_of_isUnit (Units.isUnit _), Scheme.basicOpen_res]
    apply le_antisymm
    · rintro point ⟨⟨hxa, hxB⟩, -⟩
      exact ⟨hxa, (key.le hxB).1⟩
    · rintro point ⟨hxa, hxb⟩
      exact ⟨⟨hxa, key.ge ⟨hxb, hc coordinate hxa⟩⟩, hxa⟩
  ratio_mul coordinate otherCoordinate degree := by
    set smallerOpen := (sectionFamily coordinate).nonvanishing ⊓ (sectionFamily otherCoordinate).nonvanishing
    have hWa : smallerOpen ≤ coordinates.opens (chosenIndex coordinate) := inf_le_left.trans (hc coordinate)
    have hWb : smallerOpen ≤ coordinates.opens (chosenIndex otherCoordinate) := inf_le_right.trans (hc otherCoordinate)
    have hWab : smallerOpen ≤ coordinates.opens (chosenIndex coordinate) ⊓ coordinates.opens (chosenIndex otherCoordinate) := le_inf hWa hWb
    have hs (otherSection : coordinates.Section powerBound) := congrArg (scheme.presheaf.map (homOfLE hWab).op) (otherSection.s_eq (chosenIndex coordinate) (chosenIndex otherCoordinate))
    simp only [map_mul, map_pow, Scheme.presheaf_map_map] at hs
    have hva := congrArg (scheme.presheaf.map (homOfLE (inf_le_left :
      smallerOpen ≤ (sectionFamily coordinate).nonvanishing)).op) (isUnit_map_s sectionFamily chosenIndex hc coordinate).mul_val_inv
    have hvb := congrArg (scheme.presheaf.map (homOfLE (inf_le_right :
      smallerOpen ≤ (sectionFamily otherCoordinate).nonvanishing)).op) (isUnit_map_s sectionFamily chosenIndex hc otherCoordinate).mul_val_inv
    simp only [map_mul, map_one, Scheme.presheaf_map_map] at hva hvb ⊢
    rw [hs (sectionFamily degree), hs (sectionFamily otherCoordinate)]
    linear_combination (-(scheme.presheaf.map (homOfLE (hWab.trans inf_le_left)).op
      (coordinates.ratio (chosenIndex coordinate) (chosenIndex otherCoordinate)) ^ powerBound * scheme.presheaf.map (homOfLE hWb).op ((sectionFamily degree).localSection (chosenIndex otherCoordinate)) *
      scheme.presheaf.map (homOfLE (inf_le_left : smallerOpen ≤ (sectionFamily coordinate).nonvanishing)).op
        ↑(isUnit_map_s sectionFamily chosenIndex hc coordinate).unit⁻¹)) * hvb
  iSup_U := hcov

@[simp]
lemma ofSections_U (coordinate : coordinateIndex) : (ofSections sectionFamily chosenIndex hc hcov).opens coordinate = (sectionFamily coordinate).nonvanishing := rfl

end OfSections

end Scheme.CoordinateCover

namespace Proj

open HomogeneousLocalization

variable {gradingIndex : Type schemeUniverse} {baseRing : Type schemeUniverse} [CommRing baseRing] [SetLike gradingIndex baseRing] [AddSubgroupClass gradingIndex baseRing]
  (grading : ℕ → gradingIndex) [GradedRing grading] {degree : ℕ} {function structureMap compatibility : baseRing}

def ratio (hf : function ∈ grading degree) (hg : structureMap ∈ grading degree) : Γ(Proj grading, basicOpen grading function) :=
  awayToSection grading function (Away.mk grading hf 1 structureMap (by simpa using hg))

@[simp]
lemma ratio_self (hf : function ∈ grading degree) : ratio grading hf hf = 1 := by
  have fractionEq : Away.mk grading hf 1 function (by simpa using hf) = 1 := by
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, HomogeneousLocalization.val_one]
    simpa only [pow_one] using
      Localization.mk_self (⟨function, 1, by simp⟩ : Submonoid.powers function)
  dsimp only [ratio]
  rw [fractionEq]
  exact map_one (awayToSection grading function).hom

lemma basicOpen_ratio (hd : 0 < degree) (hf : function ∈ grading degree) (hg : structureMap ∈ grading degree) :
    (Proj grading).basicOpen (ratio grading hf hg) = basicOpen grading function ⊓ basicOpen grading structureMap := by
  have equivalence : (⊤ : (Spec (.of (Away grading function))).Opens) ≤ awayι grading function hf hd ⁻¹ᵁ basicOpen grading function := by
    rw [← opensRange_awayι grading function hf hd]; exact (Scheme.Hom.preimage_opensRange _).ge
  have h₁ : awayι grading function hf hd ⁻¹ᵁ (Proj grading).basicOpen (ratio grading hf hg) =
      awayι grading function hf hd ⁻¹ᵁ basicOpen grading structureMap := by
    have := Scheme.basicOpen_appLE (awayι grading function hf hd) ⊤ (basicOpen grading function) equivalence (ratio grading hf hg)
    rw [top_inf_eq] at this
    rw [← this, awayι_preimage_basicOpen grading hf hd hg hd]
    have h2 := ConcreteCategory.congr_hom (awayToSection_awayι_appLE grading hf hd)
      (Away.mk grading hf 1 structureMap (by simpa using hg))
    rw [CommRingCat.comp_apply] at h2
    rw [ratio, h2, basicOpen_eq_of_affine]
    have hpow : (Away.mk grading hf 1 structureMap (by simpa using hg)) ^ degree =
        Away.isLocalizationElem hf hg := by
      rw [Away.mk_pow]
      simp only [mul_one]
    rw [← hpow, PrimeSpectrum.basicOpen_pow _ _ hd]
  calc (Proj grading).basicOpen (ratio grading hf hg)
      = (awayι grading function hf hd).opensRange ⊓ (Proj grading).basicOpen (ratio grading hf hg) := by
        rw [opensRange_awayι, inf_eq_right.mpr ((Proj grading).basicOpen_le _)]
    _ = (awayι grading function hf hd).opensRange ⊓ basicOpen grading structureMap := by
        rw [← Scheme.Hom.image_preimage_eq_opensRange_inf, h₁,
          Scheme.Hom.image_preimage_eq_opensRange_inf]
    _ = basicOpen grading function ⊓ basicOpen grading structureMap := by rw [opensRange_awayι]

lemma ratio_mul (hf : function ∈ grading degree) (hg : structureMap ∈ grading degree) (hh : compatibility ∈ grading degree) :
    (Proj grading).presheaf.map (homOfLE (inf_le_left :
        basicOpen grading function ⊓ basicOpen grading structureMap ≤ basicOpen grading function)).op (ratio grading hf hh) =
      (Proj grading).presheaf.map (homOfLE (inf_le_left :
        basicOpen grading function ⊓ basicOpen grading structureMap ≤ basicOpen grading function)).op (ratio grading hf hg) *
      (Proj grading).presheaf.map (homOfLE (inf_le_right :
        basicOpen grading function ⊓ basicOpen grading structureMap ≤ basicOpen grading structureMap)).op (ratio grading hg hh) := by
  have equivalence : basicOpen grading (structureMap * function) = basicOpen grading function ⊓ basicOpen grading structureMap := by
    rw [basicOpen_mul, inf_comm]
  refine Scheme.eq_of_map_eq_of_eq equivalence ?_
  rw [map_mul]
  simp only [Scheme.presheaf_map_map, ratio]
  have hF := ConcreteCategory.congr_hom
    (awayMap_awayToSection grading hg (mul_comm structureMap function)) (Away.mk grading hf 1 compatibility (by simpa using hh))
  have hF' := ConcreteCategory.congr_hom
    (awayMap_awayToSection grading hg (mul_comm structureMap function)) (Away.mk grading hf 1 structureMap (by simpa using hg))
  have hG := ConcreteCategory.congr_hom
    (awayMap_awayToSection grading hf (rfl : structureMap * function = structureMap * function)) (Away.mk grading hg 1 compatibility (by simpa using hh))
  simp only [ConcreteCategory.comp_apply] at hF hF' hG
  rw [← hF, ← hF', ← hG, ← map_mul]
  congr 1
  exact (awayMap_mk_one_eq_mul grading hg hf _).trans (mul_comm _ _)

end Proj

namespace Scheme.CoordinateCover

def ofProj {scheme : Scheme.{schemeUniverse}} {coverIndex : Type schemeUniverse} {gradingIndex baseRing : Type schemeUniverse} [CommRing baseRing] [SetLike gradingIndex baseRing]
    [AddSubgroupClass gradingIndex baseRing] (grading : ℕ → gradingIndex) [GradedRing grading] (restriction : scheme ⟶ Proj grading) {degree : ℕ} (hd : 0 < degree)
    (function : coverIndex → baseRing) (hf : ∀ index, function index ∈ grading degree) (hcov : ⨆ index, restriction ⁻¹ᵁ Proj.basicOpen grading (function index) = ⊤) :
    scheme.CoordinateCover coverIndex where
  opens index := restriction ⁻¹ᵁ Proj.basicOpen grading (function index)
  ratio index secondIndex := restriction.app _ (Proj.ratio grading (hf index) (hf secondIndex))
  ratio_self index := by simp
  basicOpen_ratio index secondIndex := by
    rw [← Scheme.preimage_basicOpen, Proj.basicOpen_ratio grading hd]
    rfl
  ratio_mul index secondIndex thirdIndex := by
    have := congrArg (restriction.app _) (Proj.ratio_mul grading (hf index) (hf secondIndex) (hf thirdIndex))
    rw [map_mul] at this
    simp only [← CommRingCat.comp_apply, restriction.naturality] at this
    exact this
  iSup_U := hcov

lemma ofProj_U {scheme : Scheme.{schemeUniverse}} {coverIndex : Type schemeUniverse} {gradingIndex baseRing : Type schemeUniverse} [CommRing baseRing] [SetLike gradingIndex baseRing]
    [AddSubgroupClass gradingIndex baseRing] (grading : ℕ → gradingIndex) [GradedRing grading] (restriction : scheme ⟶ Proj grading) {degree : ℕ} (hd : 0 < degree)
    (function : coverIndex → baseRing) (hf : ∀ index, function index ∈ grading degree) (hcov : ⨆ index, restriction ⁻¹ᵁ Proj.basicOpen grading (function index) = ⊤) (index : coverIndex) :
    (ofProj grading restriction hd function hf hcov).opens index = restriction ⁻¹ᵁ Proj.basicOpen grading (function index) := rfl

end Scheme.CoordinateCover

end AlgebraicGeometry
