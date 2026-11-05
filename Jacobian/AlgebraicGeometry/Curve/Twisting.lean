import Jacobian.AlgebraicGeometry.Curve.CanonicalDegree
import Jacobian.AlgebraicGeometry.Cohomology.Cartier
import Jacobian.AlgebraicGeometry.Cohomology.Pushforward
import Jacobian.AlgebraicGeometry.Cohomology.FieldExtension
import Jacobian.AlgebraicGeometry.IdealSheaf.CanonicalSection
import Jacobian.AlgebraicGeometry.IdealSheaf.SectionDegree
import Jacobian.AlgebraicGeometry.Modules.GlobalSection
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
# Twisting line bundles by divisors on the original curve

If a global section of a line bundle is nonzero at a rational point of a smooth proper
curve, subtracting that point decreases the dimension of global sections by one and
preserves the dimension of first cohomology. The section condition is expressed using
the actual kernel ideal of the rational point. Over a separably closed ground field,
base-changed rational points are dense after any field extension. Starting with a
large-degree twist and successively subtracting such points therefore gives a twist
defined over the ground field with one global section and vanishing first cohomology.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

private theorem unitHom_eq_zero_of_H_map_zero {source : Scheme.{u}}
    {moduleSheaf : source.Modules} (morphism : unit source ⟶ moduleSheaf)
    (vanishing : ∀ element, H.map morphism 0 element = 0) : morphism = 0 := by
  apply (unitHomAddEquiv moduleSheaf).injective
  have evaluated := congrArg (H.zeroLinearEquiv moduleSheaf)
    (vanishing ((H.zeroLinearEquiv (unit source)).symm (1 : Γ(source, ⊤))))
  rw [H.zeroLinearEquiv_map, LinearEquiv.apply_symm_apply, map_zero] at evaluated
  exact evaluated

private theorem exists_H_map_tensorCokernel_ne_zero {source : Scheme.{u}}
    {ideal : source.IdealSheafData} (invertible : ideal.IsInvertible)
    (moduleSheaf : source.Modules) [moduleSheaf.IsInvertible]
    (sectionMap : unit source ⟶ moduleSheaf) (point : source)
    (point_mem : point ∈ ideal.support) (nonvanishing : point ∉ sectionMap.zeroLocus.support) :
    ∃ element : moduleSheaf.H 0,
      H.map ((λ_ moduleSheaf).inv ≫ cokernel.π (ideal.toModulesι ▷ moduleSheaf)) 0
        element ≠ 0 := by
  letI := invertible.isInvertible_toModules
  by_contra! vanishing
  have composite_zero : sectionMap ≫ (λ_ moduleSheaf).inv ≫
      cokernel.π (ideal.toModulesι ▷ moduleSheaf) = 0 := by
    apply unitHom_eq_zero_of_H_map_zero
    intro element
    rw [H.map_comp_apply]
    exact vanishing _
  let sequence : ShortComplex source.Modules :=
    ShortComplex.mk (ideal.toModulesι ▷ moduleSheaf)
      (cokernel.π (ideal.toModulesι ▷ moduleSheaf)) (cokernel.condition _)
  have exactSequence : sequence.Exact := ShortComplex.exact_cokernel _
  letI : Mono sequence.f := by
    change Mono (ideal.toModulesι ▷ moduleSheaf)
    exact (ideal.tensorSequence_shortExact moduleSheaf).mono_f
  let lift : unit source ⟶ ideal.toModules ⊗ moduleSheaf :=
    exactSequence.lift (sectionMap ≫ (λ_ moduleSheaf).inv)
      (by simpa only [Category.assoc] using composite_zero)
  have lifted : lift ≫ ideal.toModulesι ▷ moduleSheaf =
      sectionMap ≫ (λ_ moduleSheaf).inv := exactSequence.lift_f _ _
  have ideal_le : sectionMap.zeroLocus ≤ ideal := by
    rw [Hom.zeroLocus_eq_of_arrowIso sectionMap
      (sectionMap ≫ (λ_ moduleSheaf).inv)
      (Arrow.isoMk (Iso.refl _) (λ_ moduleSheaf).symm), ← lifted]
    refine (Hom.zeroLocus_comp_le lift (ideal.toModulesι ▷ moduleSheaf)).trans ?_
    rw [Hom.zeroLocus_whiskerRight, invertible.zeroLocus_toModulesι]
  exact nonvanishing (IdealSheafData.support_antitone ideal_le point_mem)

private theorem finrank_add_one_of_exact {field : Type u} [Field field]
    {firstModule : Type*} {middleModule : Type*} {lastModule : Type*}
    [AddCommGroup firstModule] [Module field firstModule] [Module.Finite field firstModule]
    [AddCommGroup middleModule] [Module field middleModule] [Module.Finite field middleModule]
    [AddCommGroup lastModule] [Module field lastModule] [Module.Finite field lastModule]
    (firstMap : firstModule →ₗ[field] middleModule)
    (secondMap : middleModule →ₗ[field] lastModule)
    (firstInjective : Function.Injective firstMap)
    (exactness : LinearMap.ker secondMap = LinearMap.range firstMap)
    (lastRank : Module.finrank field lastModule = 1) (secondNonzero : secondMap ≠ 0) :
    Module.finrank field firstModule + 1 = Module.finrank field middleModule := by
  have secondRange : LinearMap.range secondMap = ⊤ :=
    LinearMap.range_eq_top.mpr
      (_root_.surjective_of_nonzero_of_finrank_eq_one lastRank secondNonzero)
  have firstRange : Module.finrank field (LinearMap.range firstMap) =
      Module.finrank field firstModule := by
    have dimension := LinearMap.finrank_range_add_finrank_ker firstMap
    rw [LinearMap.ker_eq_bot.mpr firstInjective, finrank_bot, add_zero] at dimension
    exact dimension
  have dimension := LinearMap.finrank_range_add_finrank_ker secondMap
  rw [secondRange, finrank_top, lastRank, exactness, firstRange] at dimension
  exact (Nat.add_comm (Module.finrank field firstModule) 1).trans dimension

private theorem finrankH_zero_add_one_of_shortExact {field : Type u} [Field field]
    {space : Scheme.{u}} [space.Over (Spec (.of field))]
    (sequence : ShortComplex space.Modules) (shortExact : sequence.ShortExact)
    [Module.Finite field (sequence.X₁.H 0)] [Module.Finite field (sequence.X₂.H 0)]
    [Module.Finite field (sequence.X₃.H 0)]
    (quotientRank : sequence.X₃.finrankH field 0 = 1)
    (nonzeroImage : ∃ element : sequence.X₂.H 0, H.map sequence.g 0 element ≠ 0) :
    sequence.X₁.finrankH field 0 + 1 = sequence.X₂.finrankH field 0 := by
  let firstMap : sequence.X₁.H 0 →ₗ[field] sequence.X₂.H 0 :=
    H.mapLinearMap field sequence.f 0
  let secondMap : sequence.X₂.H 0 →ₗ[field] sequence.X₃.H 0 :=
    H.mapLinearMap field sequence.g 0
  have firstInjective : Function.Injective firstMap :=
    H.injective_map_zero_of_shortExact shortExact
  have secondKernel : LinearMap.ker secondMap = LinearMap.range firstMap := by
    ext element
    exact SetLike.ext_iff.mp (H.ker_map_g_eq_range_map_f shortExact 0) element
  have secondNonzero : secondMap ≠ 0 := by
    obtain ⟨element, nonzeroImage⟩ := nonzeroImage
    intro vanishing
    exact nonzeroImage (LinearMap.congr_fun vanishing element)
  exact finrank_add_one_of_exact firstMap secondMap firstInjective secondKernel
    quotientRank secondNonzero

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
  [source.Over (Spec (.of baseField))]
  [SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))]
  [IsProper (source ↘ Spec (.of baseField))]
  [GeometricallyIrreducible (source ↘ Spec (.of baseField))]

private def associatedCurve : Curve baseField where
  carrier := Over.mk (source ↘ Spec (.of baseField))
  isProper := inferInstanceAs (IsProper (source ↘ Spec (.of baseField)))
  smoothOfRelativeDimension :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField)))
  geometricallyIrreducible :=
    inferInstanceAs (GeometricallyIrreducible (source ↘ Spec (.of baseField)))

private theorem finrankH_tensorCokernel_point_eq_one
    (point : Spec (.of baseField) ⟶ source)
    (section_eq : point ≫ (source ↘ Spec (.of baseField)) = 𝟙 _)
    (moduleSheaf : source.Modules) [moduleSheaf.IsInvertible] :
    (cokernel (point.ker.toModulesι ▷ moduleSheaf)).finrankH baseField 0 = 1 := by
  let projection := source ↘ Spec (.of baseField)
  let ideal := point.ker
  letI : IsIso (ideal.subschemeι ≫ projection) :=
    point.isIso_ker_subschemeι_comp_of_section projection section_eq
  letI : ideal.subscheme.Over (Spec (.of baseField)) := ⟨ideal.subschemeι ≫ projection⟩
  letI : ideal.subschemeι.IsOver (Spec (.of baseField)) := ⟨rfl⟩
  letI : IsFinite (ideal.subscheme ↘ Spec (.of baseField)) :=
    inferInstanceAs (IsFinite (ideal.subschemeι ≫ projection))
  rw [finrankH_congr baseField (ideal.tensorCokernelIsoPushforward moduleSheaf),
    finrankH_pushforward_of_isAffineHom baseField ideal.subschemeι,
    finrankH_zero_eq_finrank_globalSections_of_isFinite]
  change (ideal.subschemeι ≫ projection).finrankΓ = 1
  calc
    _ = (ideal.subschemeι ≫ projection).finrank (IsLocalRing.closedPoint baseField) :=
      (Scheme.Hom.finrank_eq_finrankΓ_of_field (ideal.subschemeι ≫ projection)
        (IsLocalRing.closedPoint baseField)).symm
    _ = 1 := by
      rw [Scheme.Hom.finrank_eq_one_of_isIso (ideal.subschemeι ≫ projection)]
      rfl

/-- Subtracting a rational point where a section is nonzero removes exactly one global
section from a line bundle on a smooth proper geometrically irreducible curve. -/
theorem finrankH_zero_tensor_ker_add_one (moduleSheaf : source.Modules)
    [moduleSheaf.IsInvertible] (sectionMap : unit source ⟶ moduleSheaf)
    (point : Spec (.of baseField) ⟶ source)
    (section_eq : point ≫ (source ↘ Spec (.of baseField)) = 𝟙 _)
    (nonvanishing : point (IsLocalRing.closedPoint baseField) ∉ sectionMap.zeroLocus.support) :
    (moduleSheaf ⊗ point.ker.toModules).finrankH baseField 0 + 1 =
      moduleSheaf.finrankH baseField 0 := by
  let ideal := point.ker
  have invertible :=
    (point.isRelativeEffectiveCartier_ker_of_section _ section_eq).1
  letI := invertible.isInvertible_toModules
  letI := point.isIso_ker_subschemeι_comp_of_section
    (source ↘ Spec (.of baseField)) section_eq
  let curve := associatedCurve (baseField := baseField) (source := source)
  letI : Module.Finite baseField ((ideal.toModules ⊗ moduleSheaf).H 0) :=
    curve.hasFiniteH _ 0
  letI : Module.Finite baseField ((unit source ⊗ moduleSheaf).H 0) :=
    curve.hasFiniteH _ 0
  letI : Module.Finite baseField ((cokernel (ideal.toModulesι ▷ moduleSheaf)).H 0) :=
    ideal.finite_H_tensorCokernel moduleSheaf 0
  let sequence : ShortComplex source.Modules :=
    ShortComplex.mk (ideal.toModulesι ▷ moduleSheaf)
      (cokernel.π (ideal.toModulesι ▷ moduleSheaf)) (cokernel.condition _)
  have shortExact : sequence.ShortExact := ideal.tensorSequence_shortExact moduleSheaf
  have quotientRank : (cokernel (ideal.toModulesι ▷ moduleSheaf)).finrankH baseField 0 = 1 :=
    finrankH_tensorCokernel_point_eq_one point section_eq moduleSheaf
  have point_mem : point (IsLocalRing.closedPoint baseField) ∈ ideal.support := by
    change point (IsLocalRing.closedPoint baseField) ∈ (point.ker.support : Set source)
    rw [Scheme.Hom.support_ker]
    exact subset_closure ⟨_, rfl⟩
  obtain ⟨element, nonzeroImage⟩ := exists_H_map_tensorCokernel_ne_zero invertible
    moduleSheaf sectionMap _ point_mem nonvanishing
  have quotientNonzero : ∃ vector : sequence.X₂.H 0, H.map sequence.g 0 vector ≠ 0 := by
    refine ⟨H.map (λ_ moduleSheaf).inv 0 element, ?_⟩
    change H.map (cokernel.π (ideal.toModulesι ▷ moduleSheaf)) 0
      (H.map (λ_ moduleSheaf).inv 0 element) ≠ 0
    intro vanishing
    exact nonzeroImage
      ((H.map_comp_apply (X := source) (λ_ moduleSheaf).inv
        (cokernel.π (ideal.toModulesι ▷ moduleSheaf)) 0 element).trans vanishing)
  have dimension := finrankH_zero_add_one_of_shortExact (field := baseField) sequence shortExact
    quotientRank quotientNonzero
  change (ideal.toModules ⊗ moduleSheaf).finrankH baseField 0 + 1 =
    (unit source ⊗ moduleSheaf).finrankH baseField 0 at dimension
  have unitRank : (unit source ⊗ moduleSheaf).finrankH baseField 0 =
      moduleSheaf.finrankH baseField 0 :=
    finrankH_congr baseField (λ_ moduleSheaf) 0
  have swapRank : (ideal.toModules ⊗ moduleSheaf).finrankH baseField 0 =
      (moduleSheaf ⊗ ideal.toModules).finrankH baseField 0 :=
    finrankH_congr baseField (β_ ideal.toModules moduleSheaf) 0
  exact (congrArg (fun rank : ℕ => rank + 1) swapRank.symm).trans
    (dimension.trans unitRank)

/-- Subtracting a rational point at which some section is nonzero preserves first
cohomology, in particular its vanishing. -/
theorem finrankH_one_tensor_ker_eq (moduleSheaf : source.Modules)
    [moduleSheaf.IsInvertible] (sectionMap : unit source ⟶ moduleSheaf)
    (point : Spec (.of baseField) ⟶ source)
    (section_eq : point ≫ (source ↘ Spec (.of baseField)) = 𝟙 _)
    (nonvanishing : point (IsLocalRing.closedPoint baseField) ∉ sectionMap.zeroLocus.support) :
    (moduleSheaf ⊗ point.ker.toModules).finrankH baseField 1 =
      moduleSheaf.finrankH baseField 1 := by
  have invertible :=
    (point.isRelativeEffectiveCartier_ker_of_section _ section_eq).1
  letI := invertible.isInvertible_toModules
  letI := point.isIso_ker_subschemeι_comp_of_section
    (source ↘ Spec (.of baseField)) section_eq
  let curve := associatedCurve (baseField := baseField) (source := source)
  letI : IsIso (point.ker.subschemeι ≫ curve.carrier.hom) := by
    change IsIso (point.ker.subschemeι ≫ (source ↘ Spec (.of baseField)))
    infer_instance
  have dualDegree : point.ker.toModulesᵛ.degree baseField = 1 :=
    invertible.degree_dual_toModules_eq_one curve
  have unitDegree : (point.ker.toModules ⊗ point.ker.toModulesᵛ).degree baseField = 0 :=
    (degree_congr baseField (tensorObjDualIsoUnit point.ker.toModules)).trans
      (degree_unit baseField)
  have idealTensorDegree := degree_tensorObj (k := baseField)
    point.ker.toModules point.ker.toModulesᵛ
  have tensorDegree := degree_tensorObj (k := baseField) moduleSheaf point.ker.toModules
  have sectionDimension := finrankH_zero_tensor_ker_add_one moduleSheaf sectionMap
    point section_eq nonvanishing
  have originalEuler := finrankH_zero_sub_finrankH_one (baseField := baseField) moduleSheaf
  have twistedEuler := finrankH_zero_sub_finrankH_one (baseField := baseField)
    (moduleSheaf ⊗ point.ker.toModules)
  omega

private def residueAlgebraMap {field : Type u} [Field field] {space : Scheme.{u}}
    (projection : space ⟶ Spec (.of field)) (point : space) : field →+* space.residueField point :=
  (CommRingCat.ofHom (algebraMap (CommRingCat.of field) (projection point).asIdeal.ResidueField) ≫
    (Spec.residueFieldIso (.of field) (projection point)).inv ≫ projection.residueFieldMap point).hom

private theorem specMap_residueAlgebraMap {field : Type u} [Field field] {space : Scheme.{u}}
    (projection : space ⟶ Spec (.of field)) (point : space) :
    Spec.map (CommRingCat.ofHom (residueAlgebraMap projection point)) =
      space.fromSpecResidueField point ≫ projection := by
  rw [← projection.SpecMap_residueFieldMap_fromSpecResidueField point,
    ← Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp, ← Spec.map_comp,
    Spec.map_inj]
  ext scalar
  rfl

private theorem residueAlgebraMap_comp {field : Type u} [Field field]
    {space otherSpace : Scheme.{u}} (morphism : space ⟶ otherSpace)
    (projection : otherSpace ⟶ Spec (.of field)) (point : space) :
    residueAlgebraMap (morphism ≫ projection) point =
      (morphism.residueFieldMap point).hom.comp (residueAlgebraMap projection (morphism point)) := by
  simp only [residueAlgebraMap, Scheme.residueFieldMap_comp, CommRingCat.hom_comp]
  rfl

private theorem residue_section_comp_iff {field : Type u} [Field field] {space : Scheme.{u}}
    (projection : space ⟶ Spec (.of field)) (point : space)
    (residueMap : space.residueField point ⟶ CommRingCat.of field) :
    (Spec.map residueMap ≫ space.fromSpecResidueField point) ≫ projection = 𝟙 _ ↔
      residueMap.hom.comp (residueAlgebraMap projection point) = RingHom.id field := by
  have comparison :
      (Spec.map residueMap ≫ space.fromSpecResidueField point) ≫ projection =
          Spec.map (CommRingCat.ofHom (RingHom.id field)) ↔
        residueMap.hom.comp (residueAlgebraMap projection point) = RingHom.id field := by
    rw [Category.assoc, ← specMap_residueAlgebraMap, ← Spec.map_comp, Spec.map_inj]
    exact ⟨fun equality ↦ congrArg CommRingCat.Hom.hom equality,
      fun equality ↦ CommRingCat.hom_ext equality⟩
  simpa only [CommRingCat.ofHom_id, Spec.map_id] using comparison

private theorem exists_section_iff_residue_embedding {field : Type u} [Field field]
    {space : Scheme.{u}} (projection : space ⟶ Spec (.of field)) (point : space) :
    (∃ sectionMap : Spec (.of field) ⟶ space,
      sectionMap ≫ projection = 𝟙 _ ∧ sectionMap (IsLocalRing.closedPoint field) = point) ↔
    ∃ residueMap : space.residueField point ⟶ CommRingCat.of field,
      residueMap.hom.comp (residueAlgebraMap projection point) = RingHom.id field := by
  constructor
  · rintro ⟨sectionMap, section_eq, rfl⟩
    obtain ⟨⟨point, residueMap⟩, representation⟩ :=
      (SpecToEquivOfField field space).symm.surjective sectionMap
    simp only [SpecToEquivOfField_symm_apply] at representation
    have point_eq : sectionMap (IsLocalRing.closedPoint field) = point := by
      rw [← representation]
      simp
    rw [← representation, residue_section_comp_iff] at section_eq
    rw [point_eq]
    exact ⟨residueMap, section_eq⟩
  · rintro ⟨residueMap, compatible⟩
    exact ⟨Spec.map residueMap ≫ space.fromSpecResidueField point,
      (residue_section_comp_iff projection point residueMap).mpr compatible, by simp⟩

private abbrev residueSeparable {field : Type u} [Field field] {space : Scheme.{u}}
    (projection : space ⟶ Spec (.of field)) (point : space) : Prop :=
  letI := (residueAlgebraMap projection point).toAlgebra
  Algebra.IsSeparable field (space.residueField point)

private theorem residueSeparable_comp {field : Type u} [Field field]
    {space otherSpace : Scheme.{u}} (morphism : space ⟶ otherSpace)
    (projection : otherSpace ⟶ Spec (.of field)) (point : space)
    (baseSeparable : residueSeparable projection (morphism point))
    (relativeSeparable : letI := (morphism.residueFieldMap point).hom.toAlgebra
      Algebra.IsSeparable (otherSpace.residueField (morphism point)) (space.residueField point)) :
    residueSeparable (morphism ≫ projection) point := by
  letI := (residueAlgebraMap projection (morphism point)).toAlgebra
  letI := (morphism.residueFieldMap point).hom.toAlgebra
  letI := (residueAlgebraMap (morphism ≫ projection) point).toAlgebra
  letI : IsScalarTower field (otherSpace.residueField (morphism point)) (space.residueField point) :=
    .of_algebraMap_eq' (residueAlgebraMap_comp morphism projection point)
  exact Algebra.IsSeparable.trans field (otherSpace.residueField (morphism point))
    (space.residueField point)

private theorem residueSeparable_of_comp {field : Type u} [Field field]
    {space otherSpace : Scheme.{u}} (morphism : space ⟶ otherSpace)
    (projection : otherSpace ⟶ Spec (.of field)) (point : space)
    (separable : residueSeparable (morphism ≫ projection) point) :
    residueSeparable projection (morphism point) := by
  letI := (residueAlgebraMap projection (morphism point)).toAlgebra
  letI := (residueAlgebraMap (morphism ≫ projection) point).toAlgebra
  let residueHom : otherSpace.residueField (morphism point) →ₐ[field] space.residueField point :=
    { toRingHom := (morphism.residueFieldMap point).hom
      commutes' := fun scalar ↦
        (RingHom.congr_fun (residueAlgebraMap_comp morphism projection point) scalar).symm }
  exact Algebra.IsSeparable.of_algHom field _ residueHom

private theorem infinite_of_isSepClosed (field : Type u) [Field field] [IsSepClosed field] :
    Infinite field := by
  refine Infinite.of_not_fintype fun _ ↦ ?_
  obtain ⟨root, root_eq⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C
    (1 : field) (-1) (-1) (FiniteField.cast_card_eq_zero field)
    (Fintype.one_lt_card (α := field)) (by simp)
  simp [FiniteField.pow_card] at root_eq

private theorem exists_residueSeparable_polynomial {field : Type u} [Field field]
    [IsSepClosed field] (dimension : ℕ)
    (openSet : Set (Spec (.of (MvPolynomial (Fin dimension) field))))
    (openSet_open : IsOpen openSet) (nonempty : openSet.Nonempty) :
    ∃ point ∈ openSet,
      residueSeparable (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin dimension))))
        point := by
  letI := infinite_of_isSepClosed field
  obtain ⟨point, point_mem⟩ := nonempty
  obtain ⟨_, ⟨polynomial, rfl⟩, point_basic, basic_subset⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open point_mem openSet_open
  have polynomial_ne_zero : polynomial ≠ 0 := by
    rintro rfl
    exact point_basic (zero_mem _)
  obtain ⟨coordinates, evaluation_ne_zero⟩ :
      ∃ coordinates : Fin dimension → field, MvPolynomial.aeval (R := field) coordinates polynomial ≠ 0 := by
    by_contra! vanishing
    exact polynomial_ne_zero (MvPolynomial.funext fun coordinates ↦ by
      simpa [MvPolynomial.aeval_def] using vanishing coordinates)
  let pointMap : Spec (.of field) ⟶ Spec (.of (MvPolynomial (Fin dimension) field)) :=
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := field) coordinates).toRingHom)
  have point_over : pointMap ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = 𝟙 _ := by
    have coefficient_eq : CommRingCat.ofHom MvPolynomial.C ≫
        CommRingCat.ofHom (MvPolynomial.aeval (R := field) coordinates).toRingHom = 𝟙 _ :=
      CommRingCat.hom_ext (MvPolynomial.aeval (R := field) coordinates).comp_algebraMap
    rw [← Spec.map_comp, coefficient_eq, Spec.map_id]
  refine ⟨pointMap (IsLocalRing.closedPoint field), basic_subset ?_, ?_⟩
  · simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    intro membership
    have kernel_mem : polynomial ∈ Ideal.comap
        (MvPolynomial.aeval (R := field) coordinates).toRingHom ⊥ := by
      convert membership using 2
      exact congrArg (Ideal.comap _) (Ideal.eq_bot_of_prime (K := field) _).symm
    exact evaluation_ne_zero (by simpa using kernel_mem)
  · obtain ⟨residueMap, compatible⟩ :=
      (exists_section_iff_residue_embedding
        (Spec.map (CommRingCat.ofHom MvPolynomial.C)) _).mp ⟨pointMap, point_over, rfl⟩
    letI := (residueAlgebraMap (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin dimension))))
      (pointMap (IsLocalRing.closedPoint field))).toAlgebra
    exact Algebra.IsSeparable.of_algHom field _
      { toRingHom := residueMap.hom
        commutes' := fun scalar ↦ RingHom.congr_fun compatible scalar }

private theorem exists_etale_polynomial_chart {field : Type u} [Field field]
    {space : Scheme.{u}} (projection : space ⟶ Spec (.of field)) [Smooth projection]
    (point : space) :
    ∃ (chart : space.Opens) (_ : IsAffineOpen chart) (_ : point ∈ chart) (dimension : ℕ)
      (chartMap : chart.toScheme ⟶ Spec (.of (MvPolynomial (Fin dimension) field))),
      Etale chartMap ∧ chartMap ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
        chart.ι ≫ projection := by
  obtain ⟨baseOpen, -, chart, affineChart, point_mem, mapsInto, standardSmooth⟩ :=
    Smooth.exists_isStandardSmooth projection point
  obtain rfl : baseOpen = ⊤ := eq_top_iff.mpr fun otherPoint _ ↦
    Subsingleton.elim (projection point) otherPoint ▸ mapsInto point_mem
  have standardSmooth' :
      ((Scheme.ΓSpecIso (.of field)).inv ≫ projection.appLE ⊤ chart mapsInto).hom.IsStandardSmooth := by
    rw [CommRingCat.hom_comp]
    exact (RingHom.isStandardSmooth_respectsIso.cancel_left_isIso _ _).mpr standardSmooth
  obtain ⟨dimension, chartRingMap, coefficients_eq, etale⟩ :=
    standardSmooth'.exists_etale_mvPolynomial
  letI : Etale (Spec.map (CommRingCat.ofHom chartRingMap)) :=
    HasRingHomProperty.Spec_iff.mpr etale
  refine ⟨chart, affineChart, point_mem, dimension,
    affineChart.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom chartRingMap), inferInstance, ?_⟩
  have coefficients_eq' : CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom chartRingMap =
      (Scheme.ΓSpecIso (.of field)).inv ≫ projection.appLE ⊤ chart mapsInto :=
    CommRingCat.hom_ext coefficients_eq
  rw [Category.assoc, ← Spec.map_comp, coefficients_eq', Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
    ← IsAffineOpen.fromSpec_top, IsAffineOpen.SpecMap_appLE_fromSpec projection _ affineChart,
    ← IsAffineOpen.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc]

private theorem dense_residueSeparable {field : Type u} [Field field] [IsSepClosed field]
    {space : Scheme.{u}} (projection : space ⟶ Spec (.of field)) [Smooth projection] :
    Dense {point : space | residueSeparable projection point} := by
  refine dense_iff_inter_open.mpr fun openSet openSet_open ⟨point, point_mem⟩ ↦ ?_
  obtain ⟨chart, affineChart, chart_mem, dimension, chartMap, etale, chart_over⟩ :=
    exists_etale_polynomial_chart projection point
  let restrictedOpen : Set chart.toScheme := chart.ι ⁻¹' openSet
  have restrictedOpen_open : IsOpen restrictedOpen :=
    openSet_open.preimage chart.ι.continuous
  obtain ⟨imagePoint, ⟨chartPoint, chartPoint_mem, rfl⟩, separable⟩ :=
    exists_residueSeparable_polynomial dimension (chartMap '' restrictedOpen)
      (chartMap.isOpenMap _ restrictedOpen_open) ⟨_, ⟨⟨point, chart_mem⟩, point_mem, rfl⟩⟩
  have chartSeparable := residueSeparable_comp chartMap
    (Spec.map (CommRingCat.ofHom MvPolynomial.C)) chartPoint separable inferInstance
  rw [chart_over] at chartSeparable
  exact ⟨chart.ι chartPoint, chartPoint_mem,
    residueSeparable_of_comp chart.ι projection chartPoint chartSeparable⟩

private theorem denseRange_rationalSections {field : Type u} [Field field] [IsSepClosed field]
    {space : Scheme.{u}} (projection : space ⟶ Spec (.of field)) [Smooth projection] :
    DenseRange fun point : {point : Spec (.of field) ⟶ space // point ≫ projection = 𝟙 _} ↦
      point.val (IsLocalRing.closedPoint field) := by
  refine (dense_residueSeparable projection).mono fun point separable ↦ ?_
  letI := (residueAlgebraMap projection point).toAlgebra
  letI : Algebra.IsSeparable field (space.residueField point) := separable
  let equivalence := RingEquiv.ofBijective _
    (IsSepClosed.algebraMap_bijective field (space.residueField point))
  obtain ⟨pointMap, point_over, point_eq⟩ :=
    (exists_section_iff_residue_embedding projection point).mpr
      ⟨CommRingCat.ofHom equivalence.symm.toRingHom, by
        ext scalar
        exact equivalence.symm_apply_apply scalar⟩
  exact ⟨⟨pointMap, point_over⟩, point_eq⟩

/-- A nonempty smooth scheme over a separably closed field has a rational section. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.exists_section_of_isSepClosed
    {field : Type u} [Field field] [IsSepClosed field] {space : Scheme.{u}}
    [Nonempty space] (projection : space ⟶ Spec (.of field)) [Smooth projection] :
    ∃ sectionMap : Spec (.of field) ⟶ space, sectionMap ≫ projection = 𝟙 _ := by
  obtain ⟨⟨sectionMap, section_eq⟩⟩ := (denseRange_rationalSections projection).nonempty
  exact ⟨sectionMap, section_eq⟩

private def baseChangeSection {field : Type u} [Field field] {space : Scheme.{u}}
    (projection : space ⟶ Spec (.of field)) (extensionField : Type u) [Field extensionField]
    [Algebra field extensionField] (point : Spec (.of field) ⟶ space)
    (point_over : point ≫ projection = 𝟙 _) :
    Spec (.of extensionField) ⟶
      Limits.pullback projection (Spec.map (CommRingCat.ofHom (algebraMap field extensionField))) :=
  Limits.pullback.lift
    (Spec.map (CommRingCat.ofHom (algebraMap field extensionField)) ≫ point) (𝟙 _)
    (by rw [Category.assoc, point_over, Category.comp_id, Category.id_comp])

private theorem baseChangeSection_eq_of_fst_eq {field : Type u} [Field field]
    {space : Scheme.{u}} (projection : space ⟶ Spec (.of field))
    (extensionField : Type u) [Field extensionField] [Algebra field extensionField]
    (point : Spec (.of field) ⟶ space) (point_over : point ≫ projection = 𝟙 _)
    {targetPoint : (Limits.pullback projection
      (Spec.map (CommRingCat.ofHom (algebraMap field extensionField))) : Scheme.{u})}
    (projection_eq : (Limits.pullback.fst _ _ : _ ⟶ space) targetPoint =
      point (IsLocalRing.closedPoint field)) :
    baseChangeSection projection extensionField point point_over
      (IsLocalRing.closedPoint extensionField) = targetPoint := by
  let fieldMap := Spec.map (CommRingCat.ofHom (algebraMap field extensionField))
  letI : IsIso (point ≫ projection) := by rw [point_over]; infer_instance
  letI : Subsingleton (Limits.pullback point (Limits.pullback.fst projection fieldMap) : Scheme.{u}) :=
    ((pullbackRightPullbackFstIso _ _ point).hom ≫ Limits.pullback.snd _ _).homeomorph.subsingleton
  have image_mem (otherPoint : (Limits.pullback projection fieldMap : Scheme.{u}))
      (image : (Limits.pullback.fst projection fieldMap : _ ⟶ space) otherPoint ∈ Set.range point) :
      otherPoint ∈ Set.range (Limits.pullback.snd point
        (Limits.pullback.fst projection fieldMap) : _ ⟶ _) := by
    rw [Scheme.Pullback.range_snd]
    exact image
  obtain ⟨firstLift, firstLift_eq⟩ := image_mem targetPoint
    ⟨IsLocalRing.closedPoint field, projection_eq.symm⟩
  obtain ⟨secondLift, secondLift_eq⟩ :=
    image_mem (baseChangeSection projection extensionField point point_over
      (IsLocalRing.closedPoint extensionField))
      ⟨fieldMap (IsLocalRing.closedPoint extensionField), by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, baseChangeSection,
          Limits.pullback.lift_fst]⟩
  rw [← firstLift_eq, ← secondLift_eq, Subsingleton.elim firstLift secondLift]

private theorem denseRange_baseChangeSections {field : Type u} [Field field]
    [IsSepClosed field] {space : Scheme.{u}} (projection : space ⟶ Spec (.of field))
    [Smooth projection] (extensionField : Type u) [Field extensionField]
    [Algebra field extensionField] :
    DenseRange fun point : {point : Spec (.of field) ⟶ space // point ≫ projection = 𝟙 _} ↦
      baseChangeSection projection extensionField point.val point.property
        (IsLocalRing.closedPoint extensionField) := by
  let fieldMap := Spec.map (CommRingCat.ofHom (algebraMap field extensionField))
  letI : Flat fieldMap := Flat.SpecMap_iff.mpr
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  refine dense_iff_inter_open.mpr fun openSet openSet_open nonempty ↦ ?_
  obtain ⟨point, targetPoint, targetPoint_mem, projection_eq⟩ :=
    DenseRange.exists_mem_open (denseRange_rationalSections projection)
      ((Limits.pullback.fst projection fieldMap).isOpenMap _ openSet_open) (nonempty.image _)
  refine ⟨_, ?_, point, rfl⟩
  have point_eq : baseChangeSection projection extensionField point.val point.property
      (IsLocalRing.closedPoint extensionField) = targetPoint :=
    baseChangeSection_eq_of_fst_eq projection extensionField point.val point.property projection_eq
  exact Eq.mpr (congrArg
    (fun actualPoint : (Limits.pullback projection fieldMap : Scheme.{u}) ↦ actualPoint ∈ openSet)
    point_eq) targetPoint_mem

private theorem ker_baseChangeSection {field : Type u} [Field field] {space : Scheme.{u}}
    (projection : space ⟶ Spec (.of field)) [IsSeparated projection]
    (extensionField : Type u) [Field extensionField] [Algebra field extensionField]
    (point : Spec (.of field) ⟶ space) (point_over : point ≫ projection = 𝟙 _) :
    point.ker.comap (Limits.pullback.fst projection
        (Spec.map (CommRingCat.ofHom (algebraMap field extensionField)))) =
      (baseChangeSection projection extensionField point point_over).ker := by
  let fieldMap := Spec.map (CommRingCat.ofHom (algebraMap field extensionField))
  let liftedPoint := baseChangeSection projection extensionField point point_over
  letI : IsClosedImmersion point := isClosedImmersion_of_comp_eq_id projection point point_over
  have square : IsPullback liftedPoint fieldMap (Limits.pullback.fst projection fieldMap) point := by
    apply IsPullback.flip
    refine IsPullback.of_bot (h₃₁ := fieldMap) ?_ ?_
      (IsPullback.of_hasPullback projection fieldMap)
    · change IsPullback fieldMap (liftedPoint ≫ Limits.pullback.snd projection fieldMap)
        (point ≫ projection) fieldMap
      dsimp only [liftedPoint, baseChangeSection]
      rw [Limits.pullback.lift_snd, point_over]
      exact IsPullback.of_id_snd
    · dsimp only [liftedPoint, baseChangeSection]
      rw [Limits.pullback.lift_fst]
  rw [← IdealSheafData.ker_fst_of_isClosedImmersion point (Limits.pullback.fst projection fieldMap),
    ← Scheme.Hom.ker_comp_of_isIso square.isoPullback.hom, square.isoPullback_hom_fst]

private theorem exists_twist_of_finrankH_zero [IsSepClosed baseField]
    (extensionField : Type u) [Field extensionField] [Algebra baseField extensionField]
    (lineBundle : (Limits.pullback (source ↘ Spec (.of baseField))
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))).Modules)
    [lineBundle.IsInvertible] (count : ℕ) :
    ∀ twist : source.Modules, twist.IsInvertible →
      (lineBundle ⊗ (pullback (Limits.pullback.fst (source ↘ Spec (.of baseField))
        (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))).obj twist).finrankH
          extensionField 0 = count + 1 →
      (lineBundle ⊗ (pullback (Limits.pullback.fst (source ↘ Spec (.of baseField))
        (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))).obj twist).finrankH
          extensionField 1 = 0 →
    ∃ twist : source.Modules, twist.IsInvertible ∧
      (lineBundle ⊗ (pullback (Limits.pullback.fst (source ↘ Spec (.of baseField))
        (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))).obj twist).finrankH
          extensionField 0 = 1 ∧
      (lineBundle ⊗ (pullback (Limits.pullback.fst (source ↘ Spec (.of baseField))
        (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))).obj twist).finrankH
          extensionField 1 = 0 := by
  let projection := source ↘ Spec (.of baseField)
  let fieldMap := Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))
  let target := Limits.pullback projection fieldMap
  let coefficientMap : target ⟶ source := Limits.pullback.fst projection fieldMap
  letI : Smooth projection := SmoothOfRelativeDimension.smooth 1 _
  letI : target.Over (Spec (.of extensionField)) := ⟨Limits.pullback.snd projection fieldMap⟩
  letI : SmoothOfRelativeDimension 1 (target ↘ Spec (.of extensionField)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback projection fieldMap)
      (inferInstanceAs (SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))))
  letI : IsProper (target ↘ Spec (.of extensionField)) :=
    inferInstanceAs (IsProper (Limits.pullback.snd projection fieldMap))
  letI : GeometricallyIrreducible (target ↘ Spec (.of extensionField)) :=
    inferInstanceAs (GeometricallyIrreducible (Limits.pullback.snd projection fieldMap))
  letI : Smooth (target ↘ Spec (.of extensionField)) := SmoothOfRelativeDimension.smooth 1 _
  letI : IsReduced target := Smooth.isReduced_of_field (target ↘ Spec (.of extensionField))
  letI : Flat fieldMap := Flat.SpecMap_iff.mpr
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let curve := associatedCurve (baseField := extensionField) (source := target)
  induction count with
  | zero => exact fun twist invertible zeroDimension firstDimension ↦
      ⟨twist, invertible, zeroDimension, firstDimension⟩
  | succ count inductionHypothesis =>
    intro twist invertible zeroDimension firstDimension
    letI : twist.IsInvertible := invertible
    let twistedLine := lineBundle ⊗ (pullback coefficientMap).obj twist
    change twistedLine.finrankH extensionField 0 = count + 1 + 1 at zeroDimension
    change twistedLine.finrankH extensionField 1 = 0 at firstDimension
    have positiveEuler : 0 < twistedLine.eulerChar extensionField := by
      rw [eulerChar_eq_finrankH_zero_sub_finrankH_one (k := extensionField) twistedLine
        (fun degree bound ↦ curve.subsingleton_H twistedLine bound)]
      omega
    obtain ⟨sectionMap, nonzeroSection⟩ := exists_nonzero_section_of_eulerChar_pos
      (k := extensionField) twistedLine (fun degree bound ↦ curve.subsingleton_H twistedLine bound)
      positiveEuler
    have outside : ∃ point, point ∉ sectionMap.zeroLocus.support := by
      by_contra! vanishing
      apply nonzeroSection
      apply (Hom.zeroLocus_eq_bot_iff sectionMap).mp
      rw [← IdealSheafData.support_eq_top_iff]
      exact eq_top_iff.mpr fun point _ ↦ vanishing point
    obtain ⟨point, point_nonvanishing⟩ := DenseRange.exists_mem_open
      (denseRange_baseChangeSections projection extensionField)
      sectionMap.zeroLocus.support.isClosed.isOpen_compl outside
    let liftedPoint := baseChangeSection projection extensionField point.val point.property
    have lifted_over : liftedPoint ≫ (target ↘ Spec (.of extensionField)) = 𝟙 _ := by
      change liftedPoint ≫ Limits.pullback.snd projection fieldMap = 𝟙 _
      dsimp only [liftedPoint, baseChangeSection]
      rw [Limits.pullback.lift_snd]
    have pointInvertible :=
      (point.val.isRelativeEffectiveCartier_ker_of_section projection point.property).1
    letI := pointInvertible.isInvertible_toModules
    have pulledInvertible := pointInvertible.comap_of_flat coefficientMap
    obtain ⟨idealComparison⟩ :=
      pointInvertible.nonempty_pullback_toModules_iso coefficientMap pulledInvertible
    have kernel_eq := ker_baseChangeSection projection extensionField point.val point.property
    let pointComparison : (pullback coefficientMap).obj point.val.ker.toModules ≅
        liftedPoint.ker.toModules := idealComparison ≪≫
      eqToIso (congrArg (fun ideal : target.IdealSheafData ↦ ideal.toModules) kernel_eq)
    let comparison : lineBundle ⊗ (pullback coefficientMap).obj (twist ⊗ point.val.ker.toModules) ≅
        twistedLine ⊗ liftedPoint.ker.toModules :=
      whiskerLeftIso lineBundle (pullbackTensorObjIso coefficientMap twist point.val.ker.toModules) ≪≫
        (α_ lineBundle ((pullback coefficientMap).obj twist)
          ((pullback coefficientMap).obj point.val.ker.toModules)).symm ≪≫
        whiskerLeftIso twistedLine pointComparison
    have zeroDrop := finrankH_zero_tensor_ker_add_one twistedLine sectionMap liftedPoint
      lifted_over point_nonvanishing
    have firstSame := finrankH_one_tensor_ker_eq twistedLine sectionMap liftedPoint
      lifted_over point_nonvanishing
    refine inductionHypothesis (twist ⊗ point.val.ker.toModules) inferInstance ?_ ?_
    · change (lineBundle ⊗ (pullback coefficientMap).obj
        (twist ⊗ point.val.ker.toModules)).finrankH extensionField 0 = count + 1
      rw [finrankH_congr extensionField comparison 0]
      omega
    · change (lineBundle ⊗ (pullback coefficientMap).obj
        (twist ⊗ point.val.ker.toModules)).finrankH extensionField 1 = 0
      exact (finrankH_congr extensionField comparison 1).trans (firstSame.trans firstDimension)

/-- Over a separably closed ground field, any line bundle after a field extension can be
twisted by a line bundle from the original curve to have one global section and no first
cohomology. The twisting bundle is defined over the ground field. -/
theorem exists_isInvertible_twist [IsSepClosed baseField]
    (extensionField : Type u) [Field extensionField] [Algebra baseField extensionField]
    (lineBundle : (Limits.pullback (source ↘ Spec (.of baseField))
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))).Modules)
    [lineBundle.IsInvertible] :
    ∃ twist : source.Modules, twist.IsInvertible ∧
      (lineBundle ⊗ (pullback (Limits.pullback.fst (source ↘ Spec (.of baseField))
        (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))).obj twist).finrankH
          extensionField 0 = 1 ∧
      (lineBundle ⊗ (pullback (Limits.pullback.fst (source ↘ Spec (.of baseField))
        (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))).obj twist).finrankH
          extensionField 1 = 0 := by
  let projection := source ↘ Spec (.of baseField)
  let fieldMap := Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))
  let target := Limits.pullback projection fieldMap
  let coefficientMap : target ⟶ source := Limits.pullback.fst projection fieldMap
  letI : Smooth projection := SmoothOfRelativeDimension.smooth 1 _
  letI : IsIntegral source := GeometricallyIntegral.isIntegral_of_subsingleton projection
  letI : target.Over (Spec (.of extensionField)) := ⟨Limits.pullback.snd projection fieldMap⟩
  letI : SmoothOfRelativeDimension 1 (target ↘ Spec (.of extensionField)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback projection fieldMap)
      (inferInstanceAs (SmoothOfRelativeDimension 1 (source ↘ Spec (.of baseField))))
  letI : IsProper (target ↘ Spec (.of extensionField)) :=
    inferInstanceAs (IsProper (Limits.pullback.snd projection fieldMap))
  letI : GeometricallyIrreducible (target ↘ Spec (.of extensionField)) :=
    inferInstanceAs (GeometricallyIrreducible (Limits.pullback.snd projection fieldMap))
  obtain ⟨⟨point, point_over⟩⟩ := (denseRange_rationalSections projection).nonempty
  have pointInvertible :=
    (point.isRelativeEffectiveCartier_ker_of_section projection point_over).1
  letI := pointInvertible.isInvertible_toModules
  letI := point.isIso_ker_subschemeι_comp_of_section projection point_over
  let curve := associatedCurve (baseField := baseField) (source := source)
  letI : IsIso (point.ker.subschemeι ≫ curve.carrier.hom) := by
    change IsIso (point.ker.subschemeι ≫ projection)
    infer_instance
  have pointDegree : point.ker.toModulesᵛ.degree baseField = 1 :=
    pointInvertible.degree_dual_toModules_eq_one curve
  have exists_degree (count : ℕ) : ∃ twist : source.Modules,
      twist.IsInvertible ∧ twist.degree baseField = (count : ℤ) := by
    induction count with
    | zero => exact ⟨unit source, inferInstance, degree_unit baseField⟩
    | succ count inductionHypothesis =>
      obtain ⟨twist, invertible, degree_eq⟩ := inductionHypothesis
      letI : twist.IsInvertible := invertible
      refine ⟨point.ker.toModulesᵛ ⊗ twist, inferInstance, ?_⟩
      rw [degree_tensorObj, pointDegree, degree_eq]
      push_cast
      omega
  let genus := arithmeticGenus extensionField target
  obtain ⟨twist, invertible, degree_eq⟩ :=
    exists_degree (2 * (genus : ℤ) - lineBundle.degree extensionField).toNat
  letI : twist.IsInvertible := invertible
  let twistedLine := lineBundle ⊗ (pullback coefficientMap).obj twist
  have tensorDegree := degree_tensorObj (k := extensionField) lineBundle
    ((pullback coefficientMap).obj twist)
  rw [degree_pullback extensionField twist, degree_eq] at tensorDegree
  have largeDegree : 2 * (genus : ℤ) ≤ twistedLine.degree extensionField := by
    change 2 * (genus : ℤ) ≤
      (lineBundle ⊗ (pullback coefficientMap).obj twist).degree extensionField
    omega
  have canonicalBound : 2 * (arithmeticGenus extensionField target : ℤ) - 2 <
      twistedLine.degree extensionField := by omega
  have firstZero := finrankH_one_eq_zero_of_degree_gt_canonical twistedLine canonicalBound
  have zeroDimension := finrankH_zero_eq_degree_add_one_sub_genus twistedLine canonicalBound
  change (twistedLine.finrankH extensionField 0 : ℤ) =
    twistedLine.degree extensionField + 1 - (genus : ℤ) at zeroDimension
  have positiveZero : 0 < twistedLine.finrankH extensionField 0 := by omega
  refine exists_twist_of_finrankH_zero extensionField lineBundle
    (twistedLine.finrankH extensionField 0 - 1) twist invertible ?_ firstZero
  change twistedLine.finrankH extensionField 0 =
    twistedLine.finrankH extensionField 0 - 1 + 1
  omega

end AlgebraicGeometry.Scheme.Modules
