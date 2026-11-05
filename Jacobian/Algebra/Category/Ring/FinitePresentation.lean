import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Descent of finitely presented algebras along filtered colimits

A finitely presented algebra over a filtered colimit of commutative rings is a
pushout of a finitely presented algebra over one ring in the diagram. The proof
lifts the finitely many polynomial relations to a common stage and constructs
the pushout from the corresponding quotient polynomial ring.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe categoryHom categoryObj ringUniverse

open CategoryTheory Limits

namespace CommRingCat

/-- Relations defined over the source ring give a pushout presentation of the
quotient after extending coefficients. -/
lemma exists_isPushout_quotient_span
    {baseRing extensionRing targetRing : CommRingCat.{ringUniverse}}
    (coefficientMap : baseRing ⟶ extensionRing) {generatorCount : ℕ}
    {relationIndex : Type*} (relations : relationIndex → MvPolynomial (Fin generatorCount) baseRing)
    (presentationMap : of (MvPolynomial (Fin generatorCount) extensionRing) ⟶ targetRing)
    (surjective : Function.Surjective presentationMap)
    (kernel_eq : RingHom.ker presentationMap.hom = Ideal.span
      (Set.range fun index ↦ MvPolynomial.map coefficientMap.hom (relations index))) :
    ∃ comparison : of (MvPolynomial (Fin generatorCount) baseRing ⧸
        Ideal.span (Set.range relations)) ⟶ targetRing,
      IsPushout coefficientMap
        (ofHom MvPolynomial.C ≫ ofHom (Ideal.Quotient.mk (Ideal.span (Set.range relations))))
        (ofHom MvPolynomial.C ≫ presentationMap) comparison := by
  set relationIdeal : Ideal (MvPolynomial (Fin generatorCount) baseRing) :=
    Ideal.span (Set.range relations) with relationIdeal_eq
  set quotientMap : of (MvPolynomial (Fin generatorCount) baseRing) ⟶
      of (MvPolynomial (Fin generatorCount) baseRing ⧸ relationIdeal) :=
    ofHom (Ideal.Quotient.mk relationIdeal) with quotientMap_eq
  set polynomialMap : of (MvPolynomial (Fin generatorCount) baseRing) ⟶
      of (MvPolynomial (Fin generatorCount) extensionRing) :=
    ofHom (MvPolynomial.map coefficientMap.hom) with polynomialMap_eq
  have relations_mem_kernel : relationIdeal ≤ RingHom.ker (polynomialMap ≫ presentationMap).hom := by
    rw [relationIdeal_eq, Ideal.span_le]
    rintro _ ⟨index, rfl⟩
    change MvPolynomial.map coefficientMap.hom (relations index) ∈ RingHom.ker presentationMap.hom
    rw [kernel_eq]
    exact Ideal.subset_span ⟨index, rfl⟩
  refine ⟨ofHom (Ideal.Quotient.lift relationIdeal (polynomialMap ≫ presentationMap).hom
    fun polynomial membership ↦ RingHom.mem_ker.mp (relations_mem_kernel membership)), ?_⟩
  set comparison : of (MvPolynomial (Fin generatorCount) baseRing ⧸ relationIdeal) ⟶ targetRing :=
    ofHom (Ideal.Quotient.lift relationIdeal (polynomialMap ≫ presentationMap).hom
      fun polynomial membership ↦ RingHom.mem_ker.mp (relations_mem_kernel membership))
    with comparison_eq
  have comparison_quotient : ∀ polynomial : MvPolynomial (Fin generatorCount) baseRing,
      comparison.hom (quotientMap.hom polynomial) =
        presentationMap.hom (MvPolynomial.map coefficientMap.hom polynomial) := by
    intro polynomial
    rw [comparison_eq, quotientMap_eq]
    simp [polynomialMap_eq]
  have quotient_relation : ∀ index, quotientMap.hom (relations index) = 0 := by
    intro index
    rw [quotientMap_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (relationIdeal_eq ▸ Ideal.subset_span ⟨index, rfl⟩)
  have eval_map : ∀ (testRing : CommRingCat.{ringUniverse})
      (leftMap : extensionRing ⟶ testRing)
      (rightMap : of (MvPolynomial (Fin generatorCount) baseRing ⧸ relationIdeal) ⟶ testRing),
      coefficientMap ≫ leftMap = (ofHom MvPolynomial.C ≫ quotientMap) ≫ rightMap →
      ∀ polynomial : MvPolynomial (Fin generatorCount) baseRing,
        MvPolynomial.eval₂ leftMap.hom
          (fun index ↦ rightMap.hom (quotientMap.hom (MvPolynomial.X index)))
          (MvPolynomial.map coefficientMap.hom polynomial) =
            rightMap.hom (quotientMap.hom polynomial) := by
    intro testRing leftMap rightMap compatible polynomial
    rw [MvPolynomial.eval₂_map]
    have coefficients_eq : leftMap.hom.comp coefficientMap.hom =
        rightMap.hom.comp (quotientMap.hom.comp MvPolynomial.C) := by
      have equality := congrArg CommRingCat.Hom.hom compatible
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_assoc] using equality
    have eval_quotient : MvPolynomial.eval₂Hom (quotientMap.hom.comp MvPolynomial.C)
        (fun index ↦ quotientMap.hom (MvPolynomial.X index)) = quotientMap.hom :=
      MvPolynomial.ringHom_ext (fun coefficient ↦ by simp) (fun index ↦ by simp)
    have eval_right : MvPolynomial.eval₂Hom
        (rightMap.hom.comp (quotientMap.hom.comp MvPolynomial.C))
        (fun index ↦ rightMap.hom (quotientMap.hom (MvPolynomial.X index))) =
          rightMap.hom.comp quotientMap.hom := by
      rw [← MvPolynomial.comp_eval₂Hom, eval_quotient]
    rw [coefficients_eq]
    simpa using DFunLike.congr_fun eval_right polynomial
  have evaluation_kernel : ∀ (testRing : CommRingCat.{ringUniverse})
      (leftMap : extensionRing ⟶ testRing)
      (rightMap : of (MvPolynomial (Fin generatorCount) baseRing ⧸ relationIdeal) ⟶ testRing),
      coefficientMap ≫ leftMap = (ofHom MvPolynomial.C ≫ quotientMap) ≫ rightMap →
      RingHom.ker presentationMap.hom ≤ RingHom.ker
        (MvPolynomial.eval₂Hom leftMap.hom
          fun index ↦ rightMap.hom (quotientMap.hom (MvPolynomial.X index))) := by
    intro testRing leftMap rightMap compatible
    rw [kernel_eq, Ideal.span_le, Set.range_subset_iff]
    intro index
    change MvPolynomial.eval₂ leftMap.hom
      (fun variableIndex ↦ rightMap.hom (quotientMap.hom (MvPolynomial.X variableIndex)))
      (MvPolynomial.map coefficientMap.hom (relations index)) = 0
    rw [eval_map _ leftMap rightMap compatible, quotient_relation, map_zero]
  set coconeDesc : ∀ (testRing : CommRingCat.{ringUniverse})
      (leftMap : extensionRing ⟶ testRing)
      (rightMap : of (MvPolynomial (Fin generatorCount) baseRing ⧸ relationIdeal) ⟶ testRing),
      coefficientMap ≫ leftMap = (ofHom MvPolynomial.C ≫ quotientMap) ≫ rightMap →
      (targetRing ⟶ testRing) :=
    fun testRing leftMap rightMap compatible ↦ ofHom
      (RingHom.liftOfSurjective presentationMap.hom surjective
        ⟨_, evaluation_kernel testRing leftMap rightMap compatible⟩) with coconeDesc_eq
  have coconeDesc_presentation : ∀ (testRing : CommRingCat.{ringUniverse})
      (leftMap : extensionRing ⟶ testRing)
      (rightMap : of (MvPolynomial (Fin generatorCount) baseRing ⧸ relationIdeal) ⟶ testRing)
      (compatible : coefficientMap ≫ leftMap = (ofHom MvPolynomial.C ≫ quotientMap) ≫ rightMap)
      (polynomial : MvPolynomial (Fin generatorCount) extensionRing),
      (coconeDesc testRing leftMap rightMap compatible).hom (presentationMap.hom polynomial) =
        MvPolynomial.eval₂ leftMap.hom
          (fun index ↦ rightMap.hom (quotientMap.hom (MvPolynomial.X index))) polynomial := by
    intro testRing leftMap rightMap compatible polynomial
    rw [coconeDesc_eq]
    exact RingHom.liftOfSurjective_comp_apply presentationMap.hom surjective
      ⟨_, evaluation_kernel testRing leftMap rightMap compatible⟩ polynomial
  refine ⟨⟨?_⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun cocone ↦ coconeDesc _ cocone.inl cocone.inr cocone.condition) ?_ ?_ ?_⟩⟩
  · refine CommRingCat.hom_ext (RingHom.ext fun coefficient ↦ ?_)
    change presentationMap.hom (MvPolynomial.C (coefficientMap.hom coefficient)) =
      comparison.hom (quotientMap.hom (MvPolynomial.C coefficient))
    rw [comparison_quotient, MvPolynomial.map_C]
  · intro cocone
    refine CommRingCat.hom_ext (RingHom.ext fun coefficient ↦ ?_)
    change (coconeDesc _ cocone.inl cocone.inr cocone.condition).hom
      (presentationMap.hom (MvPolynomial.C coefficient)) = cocone.inl.hom coefficient
    rw [coconeDesc_presentation _ cocone.inl cocone.inr cocone.condition, MvPolynomial.eval₂_C]
  · intro cocone
    refine CommRingCat.hom_ext (RingHom.ext fun quotientElement ↦ ?_)
    obtain ⟨polynomial, rfl⟩ := Ideal.Quotient.mk_surjective quotientElement
    change (coconeDesc _ cocone.inl cocone.inr cocone.condition).hom
      (comparison.hom (quotientMap.hom polynomial)) = cocone.inr.hom (quotientMap.hom polynomial)
    rw [comparison_quotient, coconeDesc_presentation _ cocone.inl cocone.inr cocone.condition]
    exact eval_map _ cocone.inl cocone.inr cocone.condition polynomial
  · intro cocone candidate left_eq right_eq
    have candidate_presentation : candidate.hom.comp presentationMap.hom =
        MvPolynomial.eval₂Hom cocone.inl.hom
          (fun index ↦ cocone.inr.hom (quotientMap.hom (MvPolynomial.X index))) := by
      refine MvPolynomial.ringHom_ext (fun coefficient ↦ ?_) (fun index ↦ ?_)
      · rw [MvPolynomial.eval₂Hom_C]
        exact congrArg (fun ringMorphism ↦ CommRingCat.Hom.hom ringMorphism coefficient) left_eq
      · rw [MvPolynomial.eval₂Hom_X']
        change candidate.hom (presentationMap.hom (MvPolynomial.X index)) =
          cocone.inr.hom (quotientMap.hom (MvPolynomial.X index))
        rw [show presentationMap.hom (MvPolynomial.X index) =
            comparison.hom (quotientMap.hom (MvPolynomial.X index)) by
          rw [comparison_quotient, MvPolynomial.map_X]]
        exact congrArg (fun ringMorphism ↦
          CommRingCat.Hom.hom ringMorphism (quotientMap.hom (MvPolynomial.X index))) right_eq
    refine CommRingCat.hom_ext (RingHom.ext fun targetElement ↦ ?_)
    obtain ⟨polynomial, rfl⟩ := surjective targetElement
    change candidate.hom (presentationMap.hom polynomial) =
      (coconeDesc _ cocone.inl cocone.inr cocone.condition).hom (presentationMap.hom polynomial)
    rw [coconeDesc_presentation _ cocone.inl cocone.inr cocone.condition]
    exact DFunLike.congr_fun candidate_presentation polynomial

variable {Index : Type categoryObj} [Category.{categoryHom} Index] [IsFiltered Index]
  (diagram : Index ⥤ CommRingCat.{ringUniverse}) (cocone : Cocone diagram)
  [PreservesColimit diagram (forget CommRingCat)] {indeterminates : Type*}

omit [IsFiltered Index] [PreservesColimit diagram (forget CommRingCat)] in
private lemma range_map_ι_app_subset {sourceIndex targetIndex : Index}
    (transition : sourceIndex ⟶ targetIndex) :
    Set.range (MvPolynomial.map (σ := indeterminates) (cocone.ι.app sourceIndex).hom) ⊆
      Set.range (MvPolynomial.map (σ := indeterminates) (cocone.ι.app targetIndex).hom) := by
  have maps_comp : (cocone.ι.app targetIndex).hom.comp (diagram.map transition).hom =
      (cocone.ι.app sourceIndex).hom :=
    congrArg CommRingCat.Hom.hom (cocone.w transition)
  rintro _ ⟨polynomial, rfl⟩
  exact ⟨MvPolynomial.map (diagram.map transition).hom polynomial, by
    rw [MvPolynomial.map_map, maps_comp]
    rfl⟩

variable (colimit : IsColimit cocone)

include colimit in
/-- Every polynomial over a filtered colimit of rings lifts to one stage. -/
lemma exists_mem_range_map_ι_app (polynomial : MvPolynomial indeterminates cocone.pt) :
    ∃ stage, polynomial ∈ Set.range (MvPolynomial.map (σ := indeterminates)
      (cocone.ι.app stage).hom) := by
  induction polynomial using MvPolynomial.induction_on with
  | C coefficient =>
    obtain ⟨stage, liftedCoefficient, coefficient_eq⟩ :=
      Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget _) colimit)
        (show ((forget CommRingCat).mapCocone cocone).pt from coefficient)
    exact ⟨stage, MvPolynomial.C liftedCoefficient, by
      rw [MvPolynomial.map_C]
      exact congrArg MvPolynomial.C coefficient_eq⟩
  | add firstPolynomial secondPolynomial firstLift secondLift =>
    obtain ⟨firstIndex, firstPolynomial, rfl⟩ := firstLift
    obtain ⟨secondIndex, secondPolynomial, rfl⟩ := secondLift
    obtain ⟨firstCommon, first_eq⟩ := range_map_ι_app_subset diagram cocone
      (IsFiltered.leftToMax firstIndex secondIndex) ⟨firstPolynomial, rfl⟩
    obtain ⟨secondCommon, second_eq⟩ := range_map_ι_app_subset diagram cocone
      (IsFiltered.rightToMax firstIndex secondIndex) ⟨secondPolynomial, rfl⟩
    exact ⟨IsFiltered.max firstIndex secondIndex, firstCommon + secondCommon, by
      rw [map_add]
      exact congrArg₂ (· + ·) first_eq second_eq⟩
  | mul_X polynomial variableIndex polynomialLift =>
    obtain ⟨stage, polynomial, rfl⟩ := polynomialLift
    exact ⟨stage, polynomial * MvPolynomial.X variableIndex, by
      rw [map_mul]
      exact congrArg (MvPolynomial.map (cocone.ι.app stage).hom polynomial * ·)
        (MvPolynomial.map_X _ _)⟩

include colimit in
/-- A finite set of polynomials over a filtered colimit lifts to a common stage. -/
lemma exists_forall_mem_range_map_ι_app
    (polynomials : Finset (MvPolynomial indeterminates cocone.pt)) :
    ∃ stage, ∀ polynomial ∈ polynomials,
      polynomial ∈ Set.range (MvPolynomial.map (σ := indeterminates) (cocone.ι.app stage).hom) := by
  classical
  choose stages lift_exists using fun polynomial : polynomials ↦
    exists_mem_range_map_ι_app diagram cocone colimit
      (polynomial : MvPolynomial indeterminates cocone.pt)
  obtain ⟨commonStage, commonStage_exists⟩ := IsFiltered.sup_objs_exists (Finset.univ.image stages)
  refine ⟨commonStage, fun polynomial membership ↦ ?_⟩
  obtain ⟨transition⟩ := commonStage_exists
    (Finset.mem_image_of_mem stages (Finset.mem_univ (⟨polynomial, membership⟩ : polynomials)))
  exact range_map_ι_app_subset diagram cocone transition (lift_exists ⟨polynomial, membership⟩)

include colimit in
/-- A finitely presented algebra over a filtered colimit is the pushout of a
finitely presented algebra over one stage. -/
theorem exists_isPushout_of_finitePresentation {targetRing : CommRingCat.{ringUniverse}}
    (structureMap : cocone.pt ⟶ targetRing) (finitePresentation : structureMap.hom.FinitePresentation) :
    ∃ (stage : Index) (stageAlgebra : CommRingCat.{ringUniverse})
      (stageMap : diagram.obj stage ⟶ stageAlgebra) (_ : stageMap.hom.FinitePresentation)
      (comparison : stageAlgebra ⟶ targetRing),
      IsPushout (cocone.ι.app stage) stageMap structureMap comparison := by
  classical
  letI : Algebra cocone.pt targetRing := structureMap.hom.toAlgebra
  obtain ⟨generatorCount, presentation_exists⟩ := finitePresentation
  obtain ⟨presentationMap, rfl, surjective, relations, relations_span⟩ :
      ∃ presentationMap : of (MvPolynomial (Fin generatorCount) cocone.pt) ⟶ targetRing,
        ofHom MvPolynomial.C ≫ presentationMap = structureMap ∧
          Function.Surjective presentationMap ∧ (RingHom.ker presentationMap.hom).FG := by
    obtain ⟨presentationMap, surjective, kernel_finite⟩ := presentation_exists
    exact ⟨ofHom presentationMap, by ext1; exact presentationMap.comp_algebraMap,
      surjective, kernel_finite⟩
  obtain ⟨stage, relations_lift⟩ := exists_forall_mem_range_map_ι_app diagram cocone colimit relations
  choose liftedRelations liftedRelations_eq using fun polynomial : relations ↦
    relations_lift polynomial polynomial.2
  have relations_range : (↑relations : Set (MvPolynomial (Fin generatorCount) cocone.pt)) =
      Set.range fun index ↦ MvPolynomial.map (cocone.ι.app stage).hom (liftedRelations index) := by
    refine Set.ext fun polynomial ↦ ⟨fun membership ↦
      ⟨⟨polynomial, membership⟩, liftedRelations_eq ⟨polynomial, membership⟩⟩, ?_⟩
    rintro ⟨index, polynomial_eq⟩
    exact Set.mem_of_eq_of_mem (polynomial_eq.symm.trans (liftedRelations_eq index))
      (Finset.mem_coe.mpr index.2)
  obtain ⟨comparison, pushout⟩ := exists_isPushout_quotient_span (extensionRing := cocone.pt)
    (cocone.ι.app stage) liftedRelations presentationMap surjective
      (by rw [← relations_span, relations_range]; rfl)
  refine ⟨stage, _, _, ?_, comparison, pushout⟩
  change ((Ideal.Quotient.mk (Ideal.span (Set.range liftedRelations))).comp
    MvPolynomial.C).FinitePresentation
  refine RingHom.FinitePresentation.comp
    (RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective ?_) ?_
  · rw [Ideal.mk_ker]
    exact ⟨Finset.univ.image liftedRelations, by simp⟩
  · have polynomial_finite := RingHom.finitePresentation_algebraMap
      (A := (diagram.obj stage : Type ringUniverse))
      (B := MvPolynomial (Fin generatorCount) (diagram.obj stage))
    rw [MvPolynomial.algebraMap_eq] at polynomial_finite
    exact polynomial_finite.mpr inferInstance

end CommRingCat
