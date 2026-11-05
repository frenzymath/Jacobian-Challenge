import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Local membership under sheafification

A section maps into the sheafification of a subpresheaf precisely when it belongs
to that subpresheaf locally. This remains true when the ambient presheaf is not
separated: local equality in its sheafification supplies the necessary refinement.
-/

noncomputable section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory.Subfunctor

variable {siteCategory : Type u} [Category.{v} siteCategory]
  (topology : GrothendieckTopology siteCategory)
  {presheaf : siteCategoryᵒᵖ ⥤ Type (max u v)} (subpresheaf : Subfunctor presheaf)

private theorem sheafifiedPresheaf_isSheaf (presheaf : siteCategoryᵒᵖ ⥤ Type (max u v)) :
    Presieve.IsSheaf topology (CategoryTheory.sheafify topology presheaf) :=
  (isSheaf_iff_isSheaf_of_type topology _).mp
    ((presheafToSheaf topology (Type (max u v))).obj presheaf).property

private def localMembershipLift :
    (subpresheaf.sheafify topology).toFunctor ⟶ CategoryTheory.sheafify topology subpresheaf.toFunctor :=
  subpresheaf.sheafifyLift (CategoryTheory.toSheafify topology subpresheaf.toFunctor)
    (sheafifiedPresheaf_isSheaf topology _)

private theorem localMembershipLift_fac :
    localMembershipLift topology subpresheaf ≫ CategoryTheory.sheafifyMap topology subpresheaf.ι =
      (subpresheaf.sheafify topology).ι ≫ CategoryTheory.toSheafify topology presheaf := by
  apply subpresheaf.to_sheafify_lift_unique (sheafifiedPresheaf_isSheaf topology presheaf)
  change Subfunctor.homOfLe (subpresheaf.le_sheafify topology) ≫
      subpresheaf.sheafifyLift (CategoryTheory.toSheafify topology subpresheaf.toFunctor)
        (sheafifiedPresheaf_isSheaf topology _) ≫ CategoryTheory.sheafifyMap topology subpresheaf.ι =
    Subfunctor.homOfLe (subpresheaf.le_sheafify topology) ≫
      (subpresheaf.sheafify topology).ι ≫ CategoryTheory.toSheafify topology presheaf
  rw [← Category.assoc, Subfunctor.to_sheafifyLift]
  rw [← toSheafify_naturality, ← Category.assoc, Subfunctor.homOfLe_ι]

/-- A section lies in the sheafified image exactly when its original membership
holds on a covering sieve. No separation assumption on the presheaf is needed. -/
theorem exists_sheafifyMap_eq_iff {object : siteCategory}
    (sectionValue : presheaf.obj (op object)) :
    (∃ lift : (CategoryTheory.sheafify topology subpresheaf.toFunctor).obj (op object),
      (CategoryTheory.sheafifyMap topology subpresheaf.ι).app (op object) lift =
        (CategoryTheory.toSheafify topology presheaf).app (op object) sectionValue) ↔
      subpresheaf.sieveOfSection sectionValue ∈ topology object := by
  constructor
  · rintro ⟨lift, liftEquality⟩
    have localRepresentatives :=
      Presheaf.imageSieve_mem topology (CategoryTheory.toSheafify topology subpresheaf.toFunctor) lift
    apply topology.transitive localRepresentatives (subpresheaf.sieveOfSection sectionValue)
    intro localObject restriction localRepresentative
    obtain ⟨representative, representativeEquality⟩ := localRepresentative
    have localEquality :
        (CategoryTheory.toSheafify topology presheaf).app (op localObject) representative.val =
          (CategoryTheory.toSheafify topology presheaf).app (op localObject)
            (presheaf.map restriction.op sectionValue) := by
      calc
        _ = (CategoryTheory.sheafifyMap topology subpresheaf.ι).app (op localObject)
            ((CategoryTheory.toSheafify topology subpresheaf.toFunctor).app (op localObject) representative) :=
          ConcreteCategory.congr_hom
            (congr_app (toSheafify_naturality topology subpresheaf.ι) (op localObject))
            representative
        _ = (CategoryTheory.sheafifyMap topology subpresheaf.ι).app (op localObject)
            ((CategoryTheory.sheafify topology subpresheaf.toFunctor).map restriction.op lift) :=
          congrArg ((CategoryTheory.sheafifyMap topology subpresheaf.ι).app (op localObject))
            representativeEquality
        _ = (CategoryTheory.sheafify topology presheaf).map restriction.op
            ((CategoryTheory.sheafifyMap topology subpresheaf.ι).app (op object) lift) :=
          ConcreteCategory.congr_hom
            ((CategoryTheory.sheafifyMap topology subpresheaf.ι).naturality restriction.op) lift
        _ = (CategoryTheory.sheafify topology presheaf).map restriction.op
            ((CategoryTheory.toSheafify topology presheaf).app (op object) sectionValue) :=
          congrArg ((CategoryTheory.sheafify topology presheaf).map restriction.op) liftEquality
        _ = _ := (ConcreteCategory.congr_hom
          ((CategoryTheory.toSheafify topology presheaf).naturality restriction.op) sectionValue).symm
    have localEqualizer := Presheaf.equalizerSieve_mem topology (CategoryTheory.toSheafify topology presheaf)
      representative.val (presheaf.map restriction.op sectionValue) localEquality
    apply topology.superset_covering _ localEqualizer
    intro refinementObject refinement equality
    change presheaf.map (refinement ≫ restriction).op sectionValue ∈
      subpresheaf.obj (op refinementObject)
    change presheaf.map refinement.op representative.val =
      presheaf.map refinement.op (presheaf.map restriction.op sectionValue) at equality
    rw [op_comp, presheaf.map_comp, types_comp_apply, ← equality]
    exact subpresheaf.map refinement.op representative.property
  · intro localMembership
    refine ⟨(localMembershipLift topology subpresheaf).app (op object)
      ⟨sectionValue, localMembership⟩, ?_⟩
    exact ConcreteCategory.congr_hom
      (congr_app (localMembershipLift_fac topology subpresheaf) (op object))
      ⟨sectionValue, localMembership⟩

end CategoryTheory.Subfunctor
