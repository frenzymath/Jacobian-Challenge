import Jacobian.AlgebraicGeometry.ProjectiveSpace.OfSections
import Jacobian.AlgebraicGeometry.ProjectiveSpectrum.FromGlobalSections

/-!
# Naturality and rescaling of projective coordinates

Pulling back generating global functions commutes with their morphism to
projective space. Multiplying every coordinate by a unit leaves this morphism
unchanged.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {source target base : Scheme.{u}} {coordinates : Type u}

/-- Pullback preserves generation of the unit ideal by global functions. -/
lemma span_range_appTop_eq_top (morphism : target ⟶ source)
    {sections : coordinates → Γ(source, ⊤)}
    (generates : Ideal.span (Set.range sections) = ⊤) :
    Ideal.span (Set.range fun coordinate ↦ morphism.appTop.hom (sections coordinate)) = ⊤ := by
  rw [Set.range_comp' morphism.appTop.hom sections, ← Ideal.map_span, generates, Ideal.map_top]

/-- The morphism given by global functions commutes with source pullback. -/
@[reassoc]
lemma comp_homOfSections (morphism : target ⟶ source) (structureMap : source ⟶ base)
    (sections : coordinates → Γ(source, ⊤))
    (generates : Ideal.span (Set.range sections) = ⊤) :
    morphism ≫ homOfSections structureMap sections generates =
      homOfSections (morphism ≫ structureMap)
        (fun coordinate ↦ morphism.appTop.hom (sections coordinate))
        (span_range_appTop_eq_top morphism generates) := by
  refine hom_ext coordinates base (by simp) ?_
  rw [Category.assoc, homOfSections_toIntegralModel, homOfSections_toIntegralModel,
    Proj.comp_fromOfGlobalSections _ morphism _ _
      (Proj.map_irrelevant_comp_appTop_eq_top _ morphism _
        (map_irrelevant_evalSections_eq_top sections generates))]
  congr 1
  exact comp_evalSections morphism sections

/-- A common unit rescaling leaves projective coordinates unchanged. -/
lemma homOfSections_eq_of_unit_mul (structureMap : source ⟶ base)
    (unitValue : Γ(source, ⊤)ˣ) {sections otherSections : coordinates → Γ(source, ⊤)}
    (generates : Ideal.span (Set.range sections) = ⊤)
    (otherGenerates : Ideal.span (Set.range otherSections) = ⊤)
    (rescaling : ∀ coordinate, otherSections coordinate = unitValue * sections coordinate) :
    homOfSections structureMap sections generates =
      homOfSections structureMap otherSections otherGenerates := by
  obtain rfl : otherSections = fun coordinate ↦ unitValue * sections coordinate := funext rescaling
  refine hom_ext coordinates base (by simp) ?_
  rw [homOfSections_toIntegralModel, homOfSections_toIntegralModel]
  exact Proj.fromOfGlobalSections_eq_of_unit_pow_mul _ unitValue _ _
    (fun _ _ homogeneous ↦ evalSections_const_mul _ _ homogeneous) _ _

end AlgebraicGeometry.ProjectiveSpace
