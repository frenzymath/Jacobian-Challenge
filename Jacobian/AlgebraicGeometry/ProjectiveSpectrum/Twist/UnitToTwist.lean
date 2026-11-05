import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.Twist.FreeGenerator

/-!
# The twisting sheaves are locally free of rank one over basic opens

The morphism `𝒪 ⟶ 𝒪(d)` attached to a homogeneous element `f` of degree `d` is an isomorphism
over the basic open of `f`, which exhibits a free generator of `𝒪(d)` there.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u

open CategoryTheory Opposite TopologicalSpace TopCat HomogeneousLocalization

namespace AlgebraicGeometry

variable {gradedRing gradedPieceType : Type u} [CommRing gradedRing] [SetLike gradedPieceType gradedRing] [AddSubgroupClass gradedPieceType gradedRing]
variable (grading : ℕ → gradedPieceType) [GradedRing grading] (twistDegree : ℤ)

namespace Proj

open ProjectiveSpectrum.Twist

section Sections

variable {grading} {formDegree : ℕ} {homogeneousElement otherHomogeneousElement : gradedRing}

/-- The morphism `𝒪 ⟶ 𝒪(d)` on `Proj 𝒜` sending `1` to the homogeneous element `f` of
degree `d`. -/
def unitToTwist (hf : homogeneousElement ∈ grading formDegree) : Scheme.Modules.unit (Proj grading) ⟶ twist grading (0 + formDegree) :=
  unitToTwistZero ≫ twistMul 0 hf

/-- The morphism `𝒪 ⟶ 𝒪(d)` given by `f` is an isomorphism on `D₊(f)`. -/
instance isIso_restrict_unitToTwist (hf : homogeneousElement ∈ grading formDegree) :
    IsIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen grading homogeneousElement).ι).map (unitToTwist hf)) := by
  have : IsIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen grading homogeneousElement).ι).map
      (unitToTwistZero (𝒜 := grading))) :=
    ((Scheme.Modules.restrictFunctor (Proj.basicOpen grading homogeneousElement).ι).mapIso
      (unitIsoTwistZero (𝒜 := grading))).isIso_hom
  rw [unitToTwist, Functor.map_comp]
  infer_instance

/-- The value of the global section `f` of `𝒪(d)` at a point is the fraction `f / 1`. -/
lemma val_unitToTwist_app_top (hf : homogeneousElement ∈ grading formDegree) (point : (⊤ : (Proj grading).Opens)) :
    (((Scheme.Modules.Hom.app (unitToTwist hf) ⊤ (1 : Γ(Proj grading, ⊤))).1 point :
      Localization.AtPrime point.1.asHomogeneousIdeal.toIdeal)) = Localization.mk homogeneousElement 1 := by
  change ((degreePart.zeroEquiv (1 : HomogeneousLocalization.AtPrime grading
    point.1.asHomogeneousIdeal.toIdeal) : degreePart grading point.1.asHomogeneousIdeal.toIdeal.primeCompl 0) :
    Localization.AtPrime point.1.asHomogeneousIdeal.toIdeal) * Localization.mk homogeneousElement 1 = _
  rw [degreePart.coe_zeroEquiv_apply, HomogeneousLocalization.val_one, one_mul]

/-- **The transition rule** `f = (f / g) • g` on `D₊(g)`, for homogeneous `f` and `g` of the same
degree `d`, between the global sections `f` and `g` of `𝒪(d)`. -/
lemma map_unitToTwist_eq_smul (hf : homogeneousElement ∈ grading formDegree) (hg : otherHomogeneousElement ∈ grading formDegree) (hf' : homogeneousElement ∈ grading (1 • formDegree)) :
    (twist grading (0 + formDegree)).presheaf.map (homOfLE le_top : Proj.basicOpen grading otherHomogeneousElement ⟶ ⊤).op
        (Scheme.Modules.Hom.app (unitToTwist hf) ⊤ (1 : Γ(Proj grading, ⊤))) =
      Proj.awayToSection grading otherHomogeneousElement (Away.mk grading hg 1 homogeneousElement hf') •
        (twist grading (0 + formDegree)).presheaf.map (homOfLE le_top : Proj.basicOpen grading otherHomogeneousElement ⟶ ⊤).op
          (Scheme.Modules.Hom.app (unitToTwist hg) ⊤ (1 : Γ(Proj grading, ⊤))) := by
  refine Subtype.ext (funext fun point ↦ Subtype.ext ?_)
  have h1 := val_unitToTwist_app_top hf ⟨point.1, trivial⟩
  have h2 := val_unitToTwist_app_top hg ⟨point.1, trivial⟩
  have h3 := ProjectiveSpectrum.Proj.awayToSection_apply grading otherHomogeneousElement (Away.mk grading hg 1 homogeneousElement hf') point
  change _ = ((Proj.awayToSection grading otherHomogeneousElement (Away.mk grading hg 1 homogeneousElement hf')).1 point).val *
    (((Scheme.Modules.Hom.app (unitToTwist hg) ⊤ (1 : Γ(Proj grading, ⊤))).1 ⟨point.1, trivial⟩ :
      Localization.AtPrime point.1.asHomogeneousIdeal.toIdeal))
  rw [h2]
  refine (h1 : _).trans (Eq.trans ?_ (congrArg (· * Localization.mk otherHomogeneousElement 1) h3.symm))
  simp only [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    RingHom.id_apply]
  rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq]
  simp [mul_comm]

section UnitToTwist

/-- A point `x` of an open `U` of `Proj 𝒜` lies in the basic open of a section `s` over `U` if
and only if the value of `s` at `x` is a unit of the localization `A_x`. -/
lemma mem_basicOpen_iff_isUnit_val {openSubset : (Proj grading).Opens} (sectionValue : Γ(Proj grading, openSubset)) {point : Proj grading}
    (hx : point ∈ openSubset) : point ∈ (Proj grading).basicOpen sectionValue ↔ IsUnit (sectionValue.1 ⟨point, hx⟩).val := by
  rw [Scheme.mem_basicOpen _ _ _ hx, HomogeneousLocalization.isUnit_iff_isUnit_val,
    ← Proj.stalkIso'_germ grading openSubset point hx sectionValue]
  exact (isUnit_map_iff (stalkIso' grading point) _).symm

variable (hf : homogeneousElement ∈ grading formDegree)

/-- The value of `unitToTwist hf` on a section `s` at a point `x` is `s x * f`. -/
lemma val_unitToTwist_app_apply {openSubset : (Proj grading).Opens} (sectionValue : Γ(Proj grading, openSubset)) (point : openSubset) :
    (((unitToTwist hf).app openSubset sectionValue).1 point).1 = (sectionValue.1 point).val * Localization.mk homogeneousElement 1 :=
  rfl

/-- On an open contained in `D₊(f)`, the section `f` of `𝒪(d)` induces a bijection from the
functions to the sections of `𝒪(d)`. -/
lemma bijective_unitToTwist_app {smallerOpen : (Proj grading).Opens} (hV : smallerOpen ≤ Proj.basicOpen grading homogeneousElement) :
    Function.Bijective ((unitToTwist hf).app smallerOpen) := by
  have h₁ : Function.Bijective (Scheme.Modules.Hom.app (unitToTwistZero (𝒜 := grading)) smallerOpen) :=
    ⟨fun sectionValue otherSection compatibility ↦ Subtype.ext (funext fun point ↦ degreePart.zeroEquiv.injective
      ((val_unitToTwistZero_app_apply smallerOpen sectionValue point).symm.trans (congr($(compatibility).1 point) |>.trans
        (val_unitToTwistZero_app_apply smallerOpen otherSection point)))), fun otherSection ↦ ⟨sectionsZeroInv otherSection, Subtype.ext
        (funext fun point ↦ (val_unitToTwistZero_app_apply _ _ _).trans
          (zeroEquiv_sectionsZeroInv otherSection point))⟩⟩
  have h₂ := isIso_mulPresheafHom_app 0 hf (U := Opposite.op smallerOpen) hV
  exact (ConcreteCategory.bijective_of_isIso ((mulPresheafHom 0 hf).app (Opposite.op smallerOpen))).comp h₁

/-- The section `f` of `𝒪(d)` is a free generator of `𝒪(d)` on `D₊(f)`. -/
lemma isFreeGenerator_unitToTwist :
    Scheme.Modules.IsFreeGenerator
      ((unitToTwist hf).app (Proj.basicOpen grading homogeneousElement) (1 : Γ(Proj grading, Proj.basicOpen grading homogeneousElement))) :=
  (Scheme.Modules.isFreeGenerator_one _).app_of_bijective _ fun _ hV ↦
    bijective_unitToTwist_app hf hV

end UnitToTwist

end Sections

end Proj

end AlgebraicGeometry
