import Jacobian.CategoryTheory.Sites.SheafifyGrp

/-!
# Functoriality of group-valued sheafification

Sheafification of a homomorphism of group-valued presheaves respects the induced
group laws. The resulting maps agree with the underlying sheafification maps
and preserve identities and composition.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe objectUniverse morphismUniverse

open Opposite

namespace CategoryTheory

variable {site : Type objectUniverse} [Category.{morphismUniverse} site]
  (topology : GrothendieckTopology site)
  {sourceFunctor targetFunctor thirdFunctor :
    siteᵒᵖ ⥤ GrpCat.{max objectUniverse morphismUniverse}}

private theorem sheafifyMap_app_toSheafify
    (transformation : sourceFunctor ⟶ targetFunctor) (object : siteᵒᵖ)
    (element : sourceFunctor.obj object) :
    (sheafifyMap topology (CategoryTheory.Functor.whiskerRight transformation (forget GrpCat))).app object
        ((toSheafify topology (sourceFunctor ⋙ forget GrpCat)).app object element) =
      (toSheafify topology (targetFunctor ⋙ forget GrpCat)).app object
        ((transformation.app object).hom element) := by
  exact (ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality topology
      (CategoryTheory.Functor.whiskerRight transformation (forget GrpCat))) object) element).symm

/-- Sheafification of a group-valued presheaf morphism, with the induced group laws. -/
def sheafifyGrpMap (transformation : sourceFunctor ⟶ targetFunctor) :
    sheafifyGrp topology sourceFunctor ⟶ sheafifyGrp topology targetFunctor where
  app object :=
    letI := sheafifyGroup topology sourceFunctor object.unop
    letI := sheafifyGroup topology targetFunctor object.unop
    GrpCat.ofHom
      { toFun := (sheafifyMap topology
          (CategoryTheory.Functor.whiskerRight transformation (forget GrpCat))).app object
        map_one' := by
          change (sheafifyMap topology (CategoryTheory.Functor.whiskerRight transformation (forget GrpCat))).app object
              ((toSheafify topology (sourceFunctor ⋙ forget GrpCat)).app object 1) =
            (toSheafify topology (targetFunctor ⋙ forget GrpCat)).app object 1
          rw [sheafifyMap_app_toSheafify, map_one]
        map_mul' firstSection secondSection := by
          let underlyingMap := sheafifyMap topology
            (CategoryTheory.Functor.whiskerRight transformation (forget GrpCat))
          let covering := Presheaf.imageSieve
              (toSheafify topology (sourceFunctor ⋙ forget GrpCat)) firstSection ⊓
            Presheaf.imageSieve
              (toSheafify topology (sourceFunctor ⋙ forget GrpCat)) secondSection
          apply SheafifyGrp.ext (presheaf := targetFunctor ⋙ forget GrpCat) covering
            (topology.intersection_covering (SheafifyGrp.imageSieve_mem firstSection)
              (SheafifyGrp.imageSieve_mem secondSection))
          intro otherObject restriction membership
          obtain ⟨⟨firstElement, firstEquality⟩, ⟨secondElement, secondEquality⟩⟩ := membership
          letI := sheafifyGroup topology sourceFunctor otherObject
          letI := sheafifyGroup topology targetFunctor otherObject
          calc
            (sheafify topology (targetFunctor ⋙ forget GrpCat)).map restriction.op
                (underlyingMap.app object (firstSection * secondSection)) =
                underlyingMap.app (.op otherObject)
                  ((sheafify topology (sourceFunctor ⋙ forget GrpCat)).map restriction.op
                    (firstSection * secondSection)) :=
              (underlyingMap.naturality_apply restriction.op _).symm
            _ = underlyingMap.app (.op otherObject)
                ((toSheafify topology (sourceFunctor ⋙ forget GrpCat)).app _
                  (firstElement * secondElement)) := by
              rw [map_sheafify_mul topology sourceFunctor firstSection secondSection
                restriction firstElement secondElement firstEquality secondEquality]
            _ = (toSheafify topology (targetFunctor ⋙ forget GrpCat)).app _
                ((transformation.app (.op otherObject)).hom firstElement *
                  (transformation.app (.op otherObject)).hom secondElement) := by
              rw [sheafifyMap_app_toSheafify, map_mul]
            _ = (sheafify topology (targetFunctor ⋙ forget GrpCat)).map restriction.op
                (underlyingMap.app object firstSection) *
                (sheafify topology (targetFunctor ⋙ forget GrpCat)).map restriction.op
                  (underlyingMap.app object secondSection) := by
              rw [toSheafify_mul]
              congr 1
              · rw [← underlyingMap.naturality_apply, ← firstEquality,
                  sheafifyMap_app_toSheafify]
              · rw [← underlyingMap.naturality_apply, ← secondEquality,
                  sheafifyMap_app_toSheafify]
            _ = (sheafify topology (targetFunctor ⋙ forget GrpCat)).map restriction.op
                (underlyingMap.app object firstSection * underlyingMap.app object secondSection) :=
              (sheafify_map_mul topology targetFunctor restriction _ _).symm }
  naturality _ _ restriction := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    exact (sheafifyMap topology
      (CategoryTheory.Functor.whiskerRight transformation (forget GrpCat))).naturality_apply restriction

/-- On original sections, the sheafified group map is the original homomorphism. -/
@[simp]
theorem sheafifyGrpMap_toSheafify (transformation : sourceFunctor ⟶ targetFunctor)
    (object : siteᵒᵖ) (element : sourceFunctor.obj object) :
    (sheafifyGrpMap topology transformation).app object
        ((toSheafify topology (sourceFunctor ⋙ forget GrpCat)).app object element) =
      (toSheafify topology (targetFunctor ⋙ forget GrpCat)).app object
        ((transformation.app object).hom element) :=
  sheafifyMap_app_toSheafify topology transformation object element

/-- The underlying natural transformation is the usual sheafification map. -/
theorem sheafifyGrpMap_whiskerRight (transformation : sourceFunctor ⟶ targetFunctor) :
    CategoryTheory.Functor.whiskerRight (sheafifyGrpMap topology transformation) (forget GrpCat) =
      sheafifyMap topology (CategoryTheory.Functor.whiskerRight transformation (forget GrpCat)) :=
  rfl

@[simp]
theorem sheafifyGrpMap_id :
    sheafifyGrpMap topology (𝟙 sourceFunctor) = 𝟙 (sheafifyGrp topology sourceFunctor) := by
  ext object element
  change (sheafifyMap topology (CategoryTheory.Functor.whiskerRight (𝟙 sourceFunctor) (forget GrpCat))).app
    object element = element
  simp

/-- Sheafifying a composite gives the composite of the sheafified group maps. -/
theorem sheafifyGrpMap_comp (firstMap : sourceFunctor ⟶ targetFunctor)
    (secondMap : targetFunctor ⟶ thirdFunctor) :
    sheafifyGrpMap topology (firstMap ≫ secondMap) =
      sheafifyGrpMap topology firstMap ≫ sheafifyGrpMap topology secondMap := by
  ext object element
  change (sheafifyMap topology
      (CategoryTheory.Functor.whiskerRight (firstMap ≫ secondMap) (forget GrpCat))).app object element =
    ((sheafifyMap topology (CategoryTheory.Functor.whiskerRight secondMap (forget GrpCat))).app object)
      ((sheafifyMap topology (CategoryTheory.Functor.whiskerRight firstMap (forget GrpCat))).app object element)
  simp only [CategoryTheory.Functor.whiskerRight_comp, sheafifyMap_comp, NatTrans.comp_app, types_comp_apply]

end CategoryTheory
