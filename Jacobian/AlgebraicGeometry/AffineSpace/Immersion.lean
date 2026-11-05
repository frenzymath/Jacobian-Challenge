import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Coordinate morphisms into affine space

Coordinate morphisms commute with change of base. If the source and base
are affine and the chosen coordinates generate the section ring over the
base, the resulting morphism is a closed immersion.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry.AffineSpace

lemma toSpecMvPolyIntEquiv_comp_SpecMap {coordinates : Type u} {sourceScheme : Scheme.{u}} {coefficientRing : CommRingCat.{u}}
    (structureMap : sourceScheme ⟶ Spec coefficientRing) (ringMap : CommRingCat.of (MvPolynomial coordinates (ULift.{u} ℤ)) ⟶ coefficientRing) (coordinate : coordinates) :
    toSpecMvPolyIntEquiv coordinates (structureMap ≫ Spec.map ringMap) coordinate =
      structureMap.appTop ((Scheme.ΓSpecIso coefficientRing).inv (ringMap (MvPolynomial.X coordinate))) := by
  rw [toSpecMvPolyIntEquiv_comp]
  congr 1
  rw [toSpecMvPolyIntEquiv_apply, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply]

section Map

variable {coordinates : Type u} {baseScheme targetScheme : Scheme.{u}}

@[reassoc]
lemma homOfVector_comp_map {affineScheme : Scheme.{u}} (structureMap : affineScheme ⟶ baseScheme) (baseMap : baseScheme ⟶ targetScheme) (sections : coordinates → Γ(affineScheme, ⊤)) :
    homOfVector structureMap sections ≫ map coordinates baseMap = homOfVector (structureMap ≫ baseMap) sections := by
  refine hom_ext ?_ fun coordinate ↦ ?_
  · rw [Category.assoc, map_over, homOfVector_over_assoc, homOfVector_over]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, map_appTop_coord,
      homOfVector_appTop_coord, homOfVector_appTop_coord]

instance isOpenImmersion_map (baseMap : baseScheme ⟶ targetScheme) [IsOpenImmersion baseMap] : IsOpenImmersion (map coordinates baseMap) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_map (n := coordinates) baseMap).flip ‹_›

end Map

lemma isClosedImmersion_homOfVector {coordinates : Type u} {affineScheme targetScheme : Scheme.{u}} [IsAffine affineScheme]
    [IsAffine targetScheme] (structureMap : affineScheme ⟶ targetScheme) (sections : coordinates → Γ(affineScheme, ⊤))
    (hgen : Subring.closure (Set.range structureMap.appTop ∪ Set.range sections) = ⊤) :
    IsClosedImmersion (homOfVector structureMap sections) := by
  refine IsClosedImmersion.of_surjective_of_isAffine _ ?_
  have hle : Subring.closure (Set.range ⇑structureMap.appTop ∪ Set.range sections) ≤
      RingHom.range (homOfVector structureMap sections).appTop.hom := by
    rw [Subring.closure_le]
    rintro element (⟨coefficient, rfl⟩ | ⟨coordinateIndex, rfl⟩)
    · refine ⟨(𝔸(coordinates; targetScheme) ↘ targetScheme).appTop coefficient, ?_⟩
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, homOfVector_over]
    · exact ⟨coord targetScheme coordinateIndex, homOfVector_appTop_coord _ _ _⟩
  exact fun element ↦ hle ((Subring.eq_top_iff' _).mp hgen element)

end AlgebraicGeometry.AffineSpace
