import Jacobian.AlgebraicGeometry.Picard.DegreeBaseChange
import Jacobian.AlgebraicGeometry.Sites.Fppf
import Jacobian.CategoryTheory.Sites.Subfunctor

/-!
# Detecting the degree part of the Picard sheaf

Fibrewise degree descends along fppf covering sieves because every residue-field
point lifts along such a sieve, and cohomology dimensions are unchanged by
extension of its residue field. Consequently a Picard class belongs to the
degree part precisely when its image in the Picard sheaf does.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {baseField : Type u} [Field baseField] {source : Scheme.{u}}
  (family : source ⟶ Spec (.of baseField)) [QuasiCompact family] [QuasiSeparated family]

/-- Constant fibre degree can be checked on any fppf covering sieve of the
parameter scheme. No properness or Noetherian hypothesis is required. -/
theorem mem_picardSubfunctorDegree_of_mem_fppfTopology
    {parameter : Over (Spec (.of baseField))}
    (picardClass : (picardPresheaf family).obj (op parameter)) (degree : ℤ)
    (sieve : Sieve parameter)
    (covering : sieve ∈ Scheme.fppfTopology.over (Spec (.of baseField)) parameter)
    (localMembership : ∀ {localParameter : Over (Spec (.of baseField))}
      (restriction : localParameter ⟶ parameter), sieve restriction →
        (picardPresheaf family).map restriction.op picardClass ∈
          (picardSubfunctorDegree family degree).obj (op localParameter)) :
    picardClass ∈ (picardSubfunctorDegree family degree).obj (op parameter) := by
  rw [mem_picardSubfunctorDegree_iff]
  intro point
  obtain ⟨localParameter, restriction, member, _, _, localPoint, imageEquality⟩ :=
    Scheme.exists_flat_mem_of_mem_fppfTopology_over covering point
  have localDegree := (mem_picardSubfunctorDegree_iff family _ degree).mp
    (localMembership restriction member) localPoint
  rw [picardPresheafDegree_map family restriction picardClass localPoint] at localDegree
  simpa only [imageEquality] using localDegree

/-- Sheafification does not add globally represented Picard classes to a degree
part: membership is already determined by the degrees of the original fibres. -/
theorem exists_picardFunctorDegree_lift_iff
    {parameter : Over (Spec (.of baseField))}
    (picardClass : (picardPresheaf family).obj (op parameter)) (degree : ℤ) :
    (∃ lift : (picardFunctorDegree family degree).obj.obj (op parameter),
      (picardFunctorDegreeι family degree).hom.app (op parameter) lift =
        (toPicardFunctor family).app (op parameter) picardClass) ↔
      picardClass ∈ (picardSubfunctorDegree family degree).obj (op parameter) := by
  let topology := Scheme.fppfTopology.over (Spec (.of baseField))
  let degreePart := picardSubfunctorDegree family degree
  have inclusionEquality : sheafifyMap topology degreePart.ι =
      (picardFunctorDegreeι family degree).hom := by
    change sheafifyMap topology degreePart.ι =
      sheafifyLift topology (degreePart.ι ≫ toPicardFunctor family)
        (picardFunctor family).property
    apply sheafifyLift_unique
    exact (toSheafify_naturality topology degreePart.ι).symm
  constructor
  · rintro ⟨lift, equality⟩
    have liftEquality : (sheafifyMap topology degreePart.ι).app (op parameter) lift =
        (toSheafify topology (picardPresheaf family)).app (op parameter) picardClass := by
      rw [inclusionEquality]
      exact equality
    have localMembership := (Subfunctor.exists_sheafifyMap_eq_iff topology degreePart
      picardClass).mp ⟨lift, liftEquality⟩
    exact mem_picardSubfunctorDegree_of_mem_fppfTopology family picardClass degree
      (degreePart.sieveOfSection picardClass) localMembership (fun _ membership ↦ membership)
  · intro membership
    refine ⟨(toSheafify topology degreePart.toFunctor).app (op parameter)
      ⟨picardClass, membership⟩, ?_⟩
    exact picardFunctorDegreeι_app_toSheafify family degree ⟨picardClass, membership⟩

end AlgebraicGeometry
