import Jacobian.AlgebraicGeometry.Curve.Cohomology
import Jacobian.AlgebraicGeometry.Curve.FiniteMap
import Jacobian.AlgebraicGeometry.IdealSheaf.Curve
import Jacobian.AlgebraicGeometry.IdealSheaf.Pullback
import Jacobian.AlgebraicGeometry.Modules.SectionDivisor
import Jacobian.AlgebraicGeometry.Picard.DegreeCartier

/-!
# Pullback of degree-zero line bundles on curves

Pullback by a morphism of smooth proper geometrically irreducible curves
preserves cohomological degree zero over any ground field. A map with
singleton image trivializes every line bundle after pullback. A nonconstant
map is finite flat of constant rank, and its pullback multiplies degree by
that rank. The finite flat formula follows from Cartier Euler increments and
nonzero sections, including for inseparable maps.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- A line bundle pulls back trivially under a map with nonempty source and
singleton topological image. -/
theorem nonempty_pullback_iso_unit_of_subsingleton_range {source target : Scheme.{u}}
    [Nonempty source] (morphism : source ⟶ target)
    (singletonImage : Set.Subsingleton (Set.range morphism))
    (lineBundle : target.Modules) [lineBundle.IsInvertible] :
    Nonempty ((Scheme.Modules.pullback morphism).obj lineBundle ≅ unit source) := by
  obtain ⟨point⟩ := ‹Nonempty source›
  obtain ⟨openSubset, membership, ⟨trivialization⟩⟩ :=
    (isInvertible_iff_forall_exists_pullback_unit lineBundle).mp inferInstance (morphism point)
  have rangeSubset : Set.range morphism ⊆ (openSubset : Set target) := by
    rintro imagePoint ⟨preimagePoint, rfl⟩
    exact (singletonImage ⟨point, rfl⟩ ⟨preimagePoint, rfl⟩) ▸ membership
  let lift : source ⟶ openSubset.toScheme := IsOpenImmersion.lift openSubset.ι morphism
    (by simpa only [Scheme.Opens.range_ι] using rangeSubset)
  have factorization : lift ≫ openSubset.ι = morphism := IsOpenImmersion.lift_fac _ _ _
  exact ⟨(pullbackCongr factorization.symm).app lineBundle ≪≫
    ((pullbackComp lift openSubset.ι).app lineBundle).symm ≪≫
    (Scheme.Modules.pullback lift).mapIso trivialization ≪≫ pullbackObjUnitIso lift⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Curve

open Scheme.Modules

variable {baseField : Type u} [Field baseField]

local instance (curve : Curve baseField) :
    curve.carrier.left.Over (Spec (.of baseField)) := ⟨curve.carrier.hom⟩

local instance (curve : Curve baseField) :
    IsProper (curve.carrier.left ↘ Spec (.of baseField)) := curve.isProper

local instance (curve : Curve baseField) :
    SmoothOfRelativeDimension 1 (curve.carrier.left ↘ Spec (.of baseField)) :=
  curve.smoothOfRelativeDimension

variable (source target : Curve baseField) (morphism : source ⟶ target)

/-- A nonconstant morphism of smooth proper curves sends the generic point to
the generic point. -/
theorem genericPoint_eq_of_not_subsingleton_range
    (nonconstant : ¬ Set.Subsingleton (Set.range morphism.left)) :
    morphism.left (genericPoint source.carrier.left) = genericPoint target.carrier.left := by
  have dimensionBound : topologicalKrullDim target.carrier.left ≤ 1 := by
    exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension target.carrier.hom 1
  apply Scheme.eq_genericPoint_of_not_isClosed dimensionBound
  intro closedImage
  have constantImage (point : source.carrier.left) :
      morphism.left point = morphism.left (genericPoint source.carrier.left) := by
    have specialization := morphism.left.base.hom.map_specializes (genericPoint_specializes point)
    have membership := specializes_iff_mem_closure.mp specialization
    rwa [closedImage.closure_eq, Set.mem_singleton_iff] at membership
  apply nonconstant
  rintro firstPoint ⟨firstPreimage, rfl⟩ secondPoint ⟨secondPreimage, rfl⟩
  exact (constantImage firstPreimage).trans (constantImage secondPreimage).symm

/-- Every nonconstant morphism of smooth proper curves is finite, surjective
and flat, without a separability assumption. -/
theorem isFinite_surjective_flat_of_not_subsingleton_range
    (nonconstant : ¬ Set.Subsingleton (Set.range morphism.left)) :
    IsFinite morphism.left ∧ Surjective morphism.left ∧ Flat morphism.left := by
  letI : morphism.left.IsOver (Spec (.of baseField)) := ⟨Over.w morphism⟩
  exact Scheme.isFinite_surjective_flat_of_genericPoint_eq (baseField := baseField) morphism.left
    (genericPoint_eq_of_not_subsingleton_range source target morphism nonconstant)

private def pullbackEulerDefect (rank : ℕ) (moduleSheaf : target.carrier.left.Modules) : ℤ :=
  ((Scheme.Modules.pullback morphism.left).obj moduleSheaf).eulerChar baseField -
    (unit source.carrier.left).eulerChar baseField -
    (rank : ℤ) * (moduleSheaf.eulerChar baseField -
      (unit target.carrier.left).eulerChar baseField)

private theorem pullbackEulerDefect_iso (rank : ℕ)
    {moduleSheaf targetSheaf : target.carrier.left.Modules}
    (comparison : moduleSheaf ≅ targetSheaf) :
    pullbackEulerDefect source target morphism rank moduleSheaf =
      pullbackEulerDefect source target morphism rank targetSheaf := by
  unfold pullbackEulerDefect
  rw [eulerChar_congr baseField ((Scheme.Modules.pullback morphism.left).mapIso comparison),
    eulerChar_congr baseField comparison]

private theorem pullbackEulerDefect_unit (rank : ℕ) :
    pullbackEulerDefect source target morphism rank (unit target.carrier.left) = 0 := by
  unfold pullbackEulerDefect
  rw [eulerChar_congr baseField (pullbackObjUnitIso morphism.left)]
  ring

private theorem eulerChar_twist (curve : Curve baseField)
    (ideal : curve.carrier.left.IdealSheafData) (invertible : ideal.IsInvertible)
    (lineBundle : curve.carrier.left.Modules) [lineBundle.IsInvertible] :
    letI := (ideal.subschemeι ≫ curve.carrier.hom).ΓAlgebra
    (ideal.twist lineBundle).eulerChar baseField = lineBundle.eulerChar baseField +
      (Module.finrank baseField Γ(ideal.subscheme, ⊤) : ℤ) := by
  letI : IsFinite (ideal.subschemeι ≫ (curve.carrier.left ↘ Spec (.of baseField))) :=
    invertible.isFinite_subschemeι_comp (curve.carrier.left ↘ Spec (.of baseField))
  letI := invertible.isInvertible_twist lineBundle
  letI (degree : ℕ) : Module.Finite baseField (lineBundle.H degree) :=
    curve.hasFiniteH lineBundle degree
  letI (degree : ℕ) : Module.Finite baseField ((ideal.twist lineBundle).H degree) :=
    curve.hasFiniteH (ideal.twist lineBundle) degree
  exact invertible.eulerChar_twist_eq_add_finrank lineBundle 1
    (fun degree bound ↦ curve.subsingleton_H lineBundle bound)
    (fun degree bound ↦ curve.subsingleton_H (ideal.twist lineBundle) bound)

private theorem pullbackEulerDefect_twist [IsFinite morphism.left] [Flat morphism.left]
    (rank : ℕ) (constantRank : ∀ point : target.carrier.left, morphism.left.finrank point = rank)
    (ideal : target.carrier.left.IdealSheafData) (invertible : ideal.IsInvertible)
    (lineBundle : target.carrier.left.Modules) [lineBundle.IsInvertible] :
    pullbackEulerDefect source target morphism rank (ideal.twist lineBundle) =
      pullbackEulerDefect source target morphism rank lineBundle := by
  letI := invertible.isFinite_subschemeι_comp target.carrier.hom
  letI := (ideal.subschemeι ≫ target.carrier.hom).ΓAlgebra
  letI := ((ideal.comap morphism.left).subschemeι ≫ source.carrier.hom).ΓAlgebra
  have sourceIncrement := eulerChar_twist source (ideal.comap morphism.left)
    (invertible.comap_of_flat morphism.left) ((Scheme.Modules.pullback morphism.left).obj lineBundle)
  have targetIncrement := eulerChar_twist target ideal invertible lineBundle
  have rankEquality := Scheme.IdealSheafData.finrank_comap_eq_mul source.carrier.hom
    target.carrier.hom morphism.left (Over.w morphism) rank constantRank ideal
  have integerRank : (Module.finrank baseField Γ((ideal.comap morphism.left).subscheme, ⊤) : ℤ) =
      (rank : ℤ) * (Module.finrank baseField Γ(ideal.subscheme, ⊤) : ℤ) := by
    exact_mod_cast rankEquality
  have comparison := eulerChar_congr baseField
    (invertible.pullbackTwistIso morphism.left lineBundle)
  have scaledIncrement := congrArg (fun value : ℤ ↦ (rank : ℤ) * value) targetIncrement
  unfold pullbackEulerDefect
  nlinarith only [sourceIncrement, scaledIncrement, integerRank, comparison]

private theorem pullbackEulerDefect_of_nonzero_section [IsFinite morphism.left]
    [Flat morphism.left] (rank : ℕ)
    (constantRank : ∀ point : target.carrier.left, morphism.left.finrank point = rank)
    (lineBundle : target.carrier.left.Modules) [lineBundle.IsInvertible]
    (sectionMap : unit target.carrier.left ⟶ lineBundle) (nonzeroSection : sectionMap ≠ 0) :
    pullbackEulerDefect source target morphism rank lineBundle = 0 := by
  obtain ⟨ideal, invertible, ⟨comparison⟩⟩ :=
    exists_effectiveCartier_of_nonzero_section lineBundle sectionMap nonzeroSection
  have twistComparison : lineBundle ≅ ideal.twist (unit target.carrier.left) :=
    comparison ≪≫ (λ_ ideal.toModulesᵛ).symm
  rw [pullbackEulerDefect_iso source target morphism rank twistComparison,
    pullbackEulerDefect_twist source target morphism rank constantRank ideal invertible,
    pullbackEulerDefect_unit]

private theorem pullbackEulerDefect_eq_zero [IsFinite morphism.left] [Flat morphism.left]
    (rank : ℕ) (constantRank : ∀ point : target.carrier.left, morphism.left.finrank point = rank)
    (lineBundle : target.carrier.left.Modules) [lineBundle.IsInvertible] :
    pullbackEulerDefect source target morphism rank lineBundle = 0 := by
  obtain ⟨ideal, invertible, nonemptySupport⟩ :=
    exists_nonempty_effectiveCartierDivisor target.carrier.hom
  letI := invertible.isFinite_subschemeι_comp target.carrier.hom
  letI := (ideal.subschemeι ≫ target.carrier.hom).ΓAlgebra
  letI : Nonempty ideal.subscheme := by
    obtain ⟨point, membership⟩ := nonemptySupport
    rw [← Scheme.IdealSheafData.range_subschemeι] at membership
    obtain ⟨preimagePoint, _⟩ := membership
    exact ⟨preimagePoint⟩
  letI : Nonempty (⊤ : ideal.subscheme.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  letI : Module.Finite baseField Γ(ideal.subscheme, ⊤) :=
    finite_globalSections_of_isFinite (ideal.subschemeι ≫ target.carrier.hom)
  have positiveLength : (0 : ℤ) < (Module.finrank baseField Γ(ideal.subscheme, ⊤) : ℤ) := by
    exact_mod_cast (Module.finrank_pos (R := baseField) (M := Γ(ideal.subscheme, ⊤)))
  have zeroOfBound (bound : ℕ) : ∀ (coefficient : target.carrier.left.Modules)
      [coefficient.IsInvertible], (1 - coefficient.eulerChar baseField).toNat = bound →
        pullbackEulerDefect source target morphism rank coefficient = 0 := by
    induction bound using Nat.strong_induction_on with
    | h bound inductionHypothesis =>
      intro coefficient coefficientInvertible measureEquality
      by_cases positive : 0 < coefficient.eulerChar baseField
      · obtain ⟨sectionMap, nonzeroSection⟩ := exists_nonzero_section_of_eulerChar_pos coefficient
          (fun degree degreeBound ↦ target.subsingleton_H coefficient degreeBound) positive
        exact pullbackEulerDefect_of_nonzero_section source target morphism rank constantRank
          coefficient sectionMap nonzeroSection
      · letI := invertible.isInvertible_twist coefficient
        have increment := eulerChar_twist target ideal invertible coefficient
        have decreased : (1 - (ideal.twist coefficient).eulerChar baseField).toNat < bound := by
          rw [← measureEquality]
          omega
        have twistedZero := inductionHypothesis _ decreased (ideal.twist coefficient) rfl
        rw [pullbackEulerDefect_twist source target morphism rank constantRank ideal invertible]
          at twistedZero
        exact twistedZero
  exact zeroOfBound _ lineBundle rfl

/-- Finite flat pullback multiplies the cohomological degree of a line bundle
by the constant rank of the morphism. -/
theorem degree_pullback_eq_mul [IsFinite morphism.left] [Flat morphism.left]
    (rank : ℕ) (constantRank : ∀ point : target.carrier.left, morphism.left.finrank point = rank)
    (lineBundle : target.carrier.left.Modules) [lineBundle.IsInvertible] :
    ((Scheme.Modules.pullback morphism.left).obj lineBundle).degree baseField =
      (rank : ℤ) * lineBundle.degree baseField := by
  exact sub_eq_zero.mp
    (pullbackEulerDefect_eq_zero source target morphism rank constantRank lineBundle)

/-- Pullback by every morphism of smooth proper geometrically irreducible
curves preserves degree zero over the ground field. -/
theorem degree_pullback_eq_zero (lineBundle : target.carrier.left.Modules)
    [lineBundle.IsInvertible] (zeroDegree : lineBundle.degree baseField = 0) :
    ((Scheme.Modules.pullback morphism.left).obj lineBundle).degree baseField = 0 := by
  by_cases singletonImage : Set.Subsingleton (Set.range morphism.left)
  · obtain ⟨comparison⟩ := nonempty_pullback_iso_unit_of_subsingleton_range
      morphism.left singletonImage lineBundle
    exact (degree_congr baseField comparison).trans (degree_unit baseField)
  · obtain ⟨finite, _, flat⟩ := isFinite_surjective_flat_of_not_subsingleton_range
      source target morphism singletonImage
    letI : IsFinite morphism.left := finite
    letI : Flat morphism.left := flat
    letI : IsLocallyNoetherian target.carrier.left :=
      LocallyOfFiniteType.isLocallyNoetherian target.carrier.hom
    letI : LocallyOfFinitePresentation morphism.left :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
    let point : target.carrier.left := Classical.choice inferInstance
    have constantRank (otherPoint : target.carrier.left) :
        morphism.left.finrank otherPoint = morphism.left.finrank point :=
      morphism.left.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace otherPoint point
    simpa only [zeroDegree, mul_zero] using
      degree_pullback_eq_mul source target morphism (morphism.left.finrank point)
        constantRank lineBundle

end AlgebraicGeometry.Curve
