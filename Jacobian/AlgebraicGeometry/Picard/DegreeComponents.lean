import Jacobian.AlgebraicGeometry.Picard.RelativeDegree
import Jacobian.AlgebraicGeometry.Picard.DegreeMembership
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Open and closed degree components of the Picard scheme

If the Picard sheaf of a proper flat family over a field is represented, the
locally constant degree of its universal section cuts the representing scheme
into disjoint open and closed subschemes. Each subscheme represents the
corresponding degree part, compatibly with its inclusion into the Picard sheaf.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
  (family : source ⟶ Spec (.of baseField)) [IsProper family]
  [LocallyOfFinitePresentation family] [Flat family]

/-- The degree parts of a represented relative Picard sheaf are represented by
pairwise disjoint open and closed subschemes covering its representing scheme.
Their representations commute with the inclusions on line-bundle classes. -/
theorem exists_decomposition_picardFunctor_representableBy (representing : Over (Spec (.of baseField)))
    (representation : (picardFunctor family).obj.RepresentableBy representing) :
    ∃ (components : ℤ → Over (Spec (.of baseField))) (inclusion : ∀ degree, components degree ⟶ representing)
      (componentRepresentation : ∀ degree, (picardFunctorDegree family degree).obj.RepresentableBy (components degree)),
      (∀ degree, IsOpenImmersion (inclusion degree).left) ∧
      (∀ degree, Set.range (inclusion degree).left.base =
        picardDegree family (representation.homEquiv (𝟙 representing)) ⁻¹' {degree}) ∧
      (∀ degree, IsClopen (Set.range (inclusion degree).left.base)) ∧
      (∀ degree otherDegree, degree ≠ otherDegree → Disjoint (Set.range (inclusion degree).left.base) (Set.range (inclusion otherDegree).left.base)) ∧
      (⋃ degree, Set.range (inclusion degree).left.base) = Set.univ ∧
      ∀ degree {parameter : Over (Spec (.of baseField))} (lineClass : (picardPresheaf family).obj (.op parameter))
        (membership : lineClass ∈ (picardSubfunctorDegree family degree).obj (.op parameter)),
        (componentRepresentation degree).homEquiv.symm ((toSheafify (fppfTopology.over (Spec (.of baseField)))
            (picardSubfunctorDegree family degree).toFunctor).app (.op parameter) ⟨lineClass, membership⟩) ≫
          inclusion degree = representation.homEquiv.symm ((toPicardFunctor family).app (.op parameter) lineClass) := by
  let topology := Scheme.fppfTopology.over (Spec (.of baseField))
  let degreeFunction := picardDegree family (representation.homEquiv (𝟙 representing))
  have locallyConstant : IsLocallyConstant degreeFunction := isLocallyConstant_picardDegree family _
  have degree_naturality {parameter : Over (Spec (.of baseField))} (morphism : parameter ⟶ representing) (point : parameter.left) :
      picardDegree family (representation.homEquiv morphism) point = degreeFunction (morphism.left point) := by
    rw [show representation.homEquiv morphism = (picardFunctor family).obj.map morphism.op (representation.homEquiv (𝟙 representing)) by
      simpa using representation.homEquiv_comp morphism (𝟙 representing), picardDegree_map]
  let degreeOpen (degree : ℤ) : representing.left.Opens := ⟨degreeFunction ⁻¹' {degree}, locallyConstant.isOpen_fiber degree⟩
  let components (degree : ℤ) : Over (Spec (.of baseField)) := Over.mk ((degreeOpen degree).ι ≫ representing.hom)
  let inclusion (degree : ℤ) : components degree ⟶ representing := Over.homMk (degreeOpen degree).ι
  have inclusion_range (degree : ℤ) : Set.range (inclusion degree).left.base = degreeFunction ⁻¹' {degree} := (degreeOpen degree).range_ι
  have hjmono (degree : ℤ) {parameter : Over (Spec (.of baseField))} (firstMap secondMap : parameter ⟶ components degree) (equality : firstMap ≫ inclusion degree = secondMap ≫ inclusion degree) :
      firstMap = secondMap := by
    ext1
    exact (cancel_mono (degreeOpen degree).ι).1 congr($(equality).left)
  have hlift (degree : ℤ) {parameter : Over (Spec (.of baseField))} (morphism : parameter ⟶ representing) (constantDegree : ∀ point, degreeFunction (morphism.left point) = degree) :
      ∃ localMap : parameter ⟶ components degree, localMap ≫ inclusion degree = morphism := by
    have rangeCondition : Set.range morphism.left.base ⊆ Set.range (degreeOpen degree).ι.base := by
      rw [(degreeOpen degree).range_ι]
      rintro _ ⟨point, rfl⟩
      exact constantDegree point
    refine ⟨Over.homMk (IsOpenImmersion.lift (degreeOpen degree).ι morphism.left rangeCondition) ?_, ?_⟩
    · simp [components, IsOpenImmersion.lift_fac_assoc]
    · ext1
      exact IsOpenImmersion.lift_fac _ _ _
  suffices representableComponents : ∀ degree : ℤ, ∃ componentRepresentation : (picardFunctorDegree family degree).obj.RepresentableBy (components degree),
      ∀ (parameter : Over (Spec (.of baseField))) (lineClass : (picardPresheaf family).obj (.op parameter))
        (membership : lineClass ∈ (picardSubfunctorDegree family degree).obj (.op parameter)),
        componentRepresentation.homEquiv.symm ((toSheafify topology (picardSubfunctorDegree family degree).toFunctor).app (.op parameter)
          ⟨lineClass, membership⟩) ≫ inclusion degree = representation.homEquiv.symm ((toPicardFunctor family).app (.op parameter) lineClass) by
    choose componentRepresentation component_compatibility using representableComponents
    refine ⟨components, inclusion, componentRepresentation, fun degree ↦ inferInstanceAs (IsOpenImmersion (degreeOpen degree).ι), inclusion_range, fun degree ↦ ?_, ?_,
      ?_, fun degree parameter lineClass membership ↦ component_compatibility degree parameter lineClass membership⟩
    · rw [inclusion_range]
      exact locallyConstant.isClopen_fiber degree
    · intro degree otherDegree differentDegrees
      rw [inclusion_range, inclusion_range]
      exact Disjoint.preimage _ (Set.disjoint_singleton.2 differentDegrees)
    · simp only [inclusion_range]
      ext point
      simp
  intro degree
  let degreePart := picardSubfunctorDegree family degree
  have representative_degree {parameter : Over (Spec (.of baseField))} (lineClass : (picardPresheaf family).obj (.op parameter))
      (membership : lineClass ∈ degreePart.obj (.op parameter)) (point : parameter.left) :
      degreeFunction ((representation.homEquiv.symm ((toPicardFunctor family).app (.op parameter) lineClass)).left point) = degree := by
    rw [← degree_naturality, Equiv.apply_symm_apply, picardDegree_toPicardFunctor]
    exact (mem_picardSubfunctorDegree_iff family lineClass degree).1 membership point
  let classifyingLift {parameter : Over (Spec (.of baseField))} (lineClass : degreePart.toFunctor.obj (.op parameter)) : parameter ⟶ components degree :=
    (hlift degree _ (representative_degree lineClass.1 lineClass.2)).choose
  have classifyingLift_comp {parameter : Over (Spec (.of baseField))} (lineClass : degreePart.toFunctor.obj (.op parameter)) :
      classifyingLift lineClass ≫ inclusion degree = representation.homEquiv.symm ((toPicardFunctor family).app (.op parameter) lineClass.1) :=
    (hlift degree _ (representative_degree lineClass.1 lineClass.2)).choose_spec
  let classifyingMap : degreePart.toFunctor ⟶ uliftYoneda.{u + 1}.obj (components degree) :=
    { app parameter := TypeCat.ofHom fun lineClass ↦ ULift.up (classifyingLift lineClass)
      naturality parameter changedParameter restriction := by
        ext lineClass
        refine ULift.ext _ _ (hjmono degree _ _ ?_)
        change classifyingLift (degreePart.toFunctor.map restriction lineClass) ≫ inclusion degree = (restriction.unop ≫ classifyingLift lineClass) ≫ inclusion degree
        rw [classifyingLift_comp, Category.assoc, classifyingLift_comp, representation.comp_homEquiv_symm]
        exact congrArg representation.homEquiv.symm (NatTrans.naturality_apply (toPicardFunctor family) restriction lineClass.1) }
  have locallyInjective : Presheaf.IsLocallyInjective topology classifyingMap := by
    refine ⟨fun {parameter} lineClass otherClass morphism ↦ ?_⟩
    have classEquality : (toPicardFunctor family).app parameter lineClass.1 = (toPicardFunctor family).app parameter otherClass.1 := by
      apply representation.homEquiv.symm.injective
      rw [← classifyingLift_comp, ← classifyingLift_comp]
      exact congrArg (· ≫ inclusion degree) (congrArg ULift.down morphism)
    exact topology.superset_covering (fun localParameter restriction localEquality ↦ Subtype.ext localEquality)
      (Presheaf.equalizerSieve_mem topology (toPicardFunctor family) lineClass.1 otherClass.1 classEquality)
  have locallySurjective : Presheaf.IsLocallySurjective topology classifyingMap := by
    refine ⟨fun {parameter} localMap ↦ ?_⟩
    refine topology.superset_covering ?_
      (Presheaf.imageSieve_mem topology (toPicardFunctor family) (representation.homEquiv (localMap.down ≫ inclusion degree)))
    rintro localParameter restriction ⟨lineClass, membership⟩
    have degreeMembership : lineClass ∈ degreePart.obj (.op localParameter) := by
      refine (mem_picardSubfunctorDegree_iff family lineClass degree).2 fun localPoint ↦ ?_
      rw [← picardDegree_toPicardFunctor, membership, picardDegree_map, degree_naturality, ← Set.mem_singleton_iff,
        ← Set.mem_preimage, ← inclusion_range degree]
      exact ⟨localMap.down.left (restriction.left localPoint), rfl⟩
    refine ⟨⟨lineClass, degreeMembership⟩, ULift.ext _ _ (hjmono degree _ _ ?_)⟩
    change classifyingLift ⟨lineClass, degreeMembership⟩ ≫ inclusion degree = (restriction ≫ localMap.down) ≫ inclusion degree
    rw [classifyingLift_comp, Category.assoc, ← Equiv.symm_apply_apply representation.homEquiv (localMap.down ≫ inclusion degree),
      representation.comp_homEquiv_symm]
    exact congrArg representation.homEquiv.symm membership
  have : topology.Subcanonical := inferInstanceAs (fppfTopology.over (Spec (.of baseField))).Subcanonical
  let representedSheaf := topology.uliftYoneda.{u + 1}.obj (components degree)
  let sheafClassifyingMap : (presheafToSheaf topology (Type (u + 1))).obj degreePart.toFunctor ⟶ representedSheaf :=
    ⟨sheafifyLift topology classifyingMap representedSheaf.property⟩
  have sheafificationCompatibility : toSheafify topology degreePart.toFunctor ≫ sheafClassifyingMap.hom = classifyingMap := toSheafify_sheafifyLift topology classifyingMap representedSheaf.property
  have : Presheaf.IsLocallyInjective topology sheafClassifyingMap.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac topology classifyingMap sheafificationCompatibility
  have : Presheaf.IsLocallySurjective topology sheafClassifyingMap.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac topology sheafificationCompatibility
  have : IsIso sheafClassifyingMap := (Sheaf.isLocallyBijective_iff_isIso sheafClassifyingMap).1 ⟨inferInstance, inferInstance⟩
  refine ⟨(Functor.RepresentableBy.equivUliftYonedaIso _ (components degree)).symm
    ((sheafToPresheaf topology _).mapIso (asIso sheafClassifyingMap)).symm, fun parameter lineClass membership ↦ ?_⟩
  have morphism : (sheafClassifyingMap.hom.app (.op parameter) ((toSheafify topology degreePart.toFunctor).app (.op parameter) ⟨lineClass, membership⟩)).down =
      classifyingLift ⟨lineClass, membership⟩ :=
    congr_arg (fun transformation ↦ (transformation.app (.op parameter) ⟨lineClass, membership⟩).down) sheafificationCompatibility
  exact (congr_arg (· ≫ inclusion degree) morphism).trans (classifyingLift_comp ⟨lineClass, membership⟩)

end AlgebraicGeometry
