import Jacobian.AlgebraicGeometry.ProjectiveSpace.Relative
import Jacobian.RingTheory.MvPolynomial.HomogeneousCharts

/-!
# Morphisms to projective space from sections

A family of global functions generating the unit ideal defines a morphism
to projective space. Its inverse images of the standard opens are the
corresponding basic opens, and its affine restrictions have explicit coordinates.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {sourceScheme baseScheme : Scheme.{u}} {coordinates : Type u}

/-- Evaluation of homogeneous coordinates at a family of global functions. -/
def evalSections (sections : coordinates → Γ(sourceScheme, ⊤)) : MvPolynomial coordinates (ULift.{u} ℤ) →+* Γ(sourceScheme, ⊤) :=
  eval₂Hom ((Int.castRingHom Γ(sourceScheme, ⊤)).comp (ULift.ringEquiv (R := ℤ)).toRingHom) sections

@[simp]
lemma evalSections_X (sections : coordinates → Γ(sourceScheme, ⊤)) (coordinate : coordinates) : evalSections sections (MvPolynomial.X coordinate) = sections coordinate :=
  eval₂Hom_X' _ _ coordinate

lemma map_irrelevant_evalSections_eq_top (sections : coordinates → Γ(sourceScheme, ⊤)) (generates : Ideal.span (Set.range sections) = ⊤) :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule coordinates (ULift.{u} ℤ))).toIdeal.map
      (evalSections sections) = ⊤ := by
  rw [toIdeal_irrelevant_homogeneousSubmodule, Ideal.map_span, ← Set.range_comp]
  simpa [Function.comp_def] using generates

lemma comp_evalSections {Y : Scheme.{u}} (square : Y ⟶ sourceScheme) (sections : coordinates → Γ(sourceScheme, ⊤)) :
    square.appTop.hom.comp (evalSections sections) = evalSections fun coordinate ↦ square.appTop.hom (sections coordinate) := by
  rw [evalSections, evalSections, comp_eval₂Hom]
  congr 1
  ext point
  simp

lemma evalSections_const_mul {degree : ℕ} (scalar : Γ(sourceScheme, ⊤))
    (sections : coordinates → Γ(sourceScheme, ⊤))
    {polynomial : MvPolynomial coordinates (ULift.{u} ℤ)}
    (homogeneous : polynomial ∈ homogeneousSubmodule coordinates (ULift.{u} ℤ) degree) :
    evalSections (fun coordinate ↦ scalar * sections coordinate) polynomial =
      scalar ^ degree * evalSections sections polynomial :=
  ((mem_homogeneousSubmodule _ _).mp homogeneous).eval₂Hom_const_mul _ _ _

variable (secondMap : sourceScheme ⟶ baseScheme) (sections : coordinates → Γ(sourceScheme, ⊤)) (generates : Ideal.span (Set.range sections) = ⊤)

/-- The morphism defined by global functions generating the unit ideal. -/
def homOfSections : sourceScheme ⟶ ℙ(coordinates; baseScheme) :=
  pullback.lift secondMap
    (Proj.fromOfGlobalSections _ (evalSections sections) (map_irrelevant_evalSections_eq_top sections generates))
    (terminal.hom_ext _ _)

@[reassoc (attr := simp)]
lemma homOfSections_over : homOfSections secondMap sections generates ≫ ℙ(coordinates; baseScheme) ↘ baseScheme = secondMap :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma homOfSections_toIntegralModel :
    homOfSections secondMap sections generates ≫ toIntegralModel coordinates baseScheme =
      Proj.fromOfGlobalSections _ (evalSections sections) (map_irrelevant_evalSections_eq_top sections generates) :=
  pullback.lift_snd _ _ _

/-- The standard open where a homogeneous coordinate does not vanish. -/
def standardOpen (coordinates : Type u) (baseScheme : Scheme.{u}) (coordinate : coordinates) : ℙ(coordinates; baseScheme).Opens :=
  toIntegralModel coordinates baseScheme ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ)) (MvPolynomial.X coordinate)

@[simp]
lemma iSup_standardOpen (coordinates : Type u) (baseScheme : Scheme.{u}) : ⨆ coordinate, standardOpen coordinates baseScheme coordinate = ⊤ :=
  Scheme.Hom.iSup_preimage_eq_top _ <| Proj.iSup_basicOpen_eq_top _ _
    (toIdeal_irrelevant_homogeneousSubmodule coordinates (ULift.{u} ℤ)).le

@[ext 1100]
lemma standardOpen_hom_ext {targetScheme : Scheme.{u}} {coordinate : coordinates} {firstMap secondMap : targetScheme ⟶ (standardOpen coordinates baseScheme coordinate).toScheme}
    (structureMapEq : firstMap ≫ (standardOpen coordinates baseScheme coordinate).ι ≫ ℙ(coordinates; baseScheme) ↘ baseScheme =
      secondMap ≫ (standardOpen coordinates baseScheme coordinate).ι ≫ ℙ(coordinates; baseScheme) ↘ baseScheme)
    (integralModelMapEq : firstMap ≫ (toIntegralModel coordinates baseScheme).resLE _ (standardOpen coordinates baseScheme coordinate) le_rfl =
      secondMap ≫ (toIntegralModel coordinates baseScheme).resLE _ (standardOpen coordinates baseScheme coordinate) le_rfl) : firstMap = secondMap := by
  rw [← cancel_mono (standardOpen coordinates baseScheme coordinate).ι]
  refine hom_ext coordinates baseScheme ?_ ?_
  · simpa using structureMapEq
  · simpa using congrArg (· ≫ (Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ))
      (MvPolynomial.X coordinate)).ι) integralModelMapEq

lemma homOfSections_preimage_standardOpen (coordinate : coordinates) :
    homOfSections secondMap sections generates ⁻¹ᵁ standardOpen coordinates baseScheme coordinate = sourceScheme.basicOpen (sections coordinate) := by
  rw [standardOpen, ← Scheme.Hom.comp_preimage, homOfSections_toIntegralModel,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.one_pos
      ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ coordinate)), evalSections_X]

lemma homOfSections_resLE_comp_toIntegralModel_resLE (coordinate : coordinates) :
    (homOfSections secondMap sections generates).resLE (standardOpen coordinates baseScheme coordinate) (sourceScheme.basicOpen (sections coordinate))
        (homOfSections_preimage_standardOpen secondMap sections generates coordinate).ge ≫
      (toIntegralModel coordinates baseScheme).resLE _ (standardOpen coordinates baseScheme coordinate) le_rfl =
      Proj.toBasicOpenOfGlobalSections _ (evalSections sections) (evalSections_X sections coordinate) Nat.one_pos
        ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ coordinate)) := by
  have homogeneous : MvPolynomial.X coordinate ∈ homogeneousSubmodule coordinates (ULift.{u} ℤ) 1 :=
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ coordinate)
  suffices square : ∀ (point : Γ(sourceScheme, ⊤)) (imageEq : evalSections sections (MvPolynomial.X coordinate) = point)
      (embedding : sourceScheme.basicOpen point ≤ homOfSections secondMap sections generates ⁻¹ᵁ standardOpen coordinates baseScheme coordinate),
      (homOfSections secondMap sections generates).resLE (standardOpen coordinates baseScheme coordinate) (sourceScheme.basicOpen point) embedding ≫
        (toIntegralModel coordinates baseScheme).resLE _ (standardOpen coordinates baseScheme coordinate) le_rfl =
        Proj.toBasicOpenOfGlobalSections _ (evalSections sections) imageEq Nat.one_pos homogeneous from
    square _ (evalSections_X sections coordinate) _
  rintro point rfl embedding
  rw [← cancel_mono (Proj.basicOpen (homogeneousSubmodule coordinates (ULift.{u} ℤ))
    (MvPolynomial.X coordinate)).ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.Hom.resLE_comp_ι_assoc, homOfSections_toIntegralModel,
    ← Proj.fromOfGlobalSections_resLE _ _ _ Nat.one_pos homogeneous, Scheme.Hom.resLE_comp_ι]

@[reassoc]
lemma homOfSections_resLE_ι_over (coordinate : coordinates) :
    (homOfSections secondMap sections generates).resLE (standardOpen coordinates baseScheme coordinate) (sourceScheme.basicOpen (sections coordinate))
        (homOfSections_preimage_standardOpen secondMap sections generates coordinate).ge ≫
      (standardOpen coordinates baseScheme coordinate).ι ≫ ℙ(coordinates; baseScheme) ↘ baseScheme = (sourceScheme.basicOpen (sections coordinate)).ι ≫ secondMap := by
  rw [Scheme.Hom.resLE_comp_ι_assoc, homOfSections_over]

end AlgebraicGeometry.ProjectiveSpace
