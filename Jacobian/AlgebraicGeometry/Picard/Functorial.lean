import Jacobian.AlgebraicGeometry.Picard.RepresentableGroup
import Jacobian.CategoryTheory.Sites.SheafifyGrpMap

/-!
# Pullback morphisms of relative Picard sheaves

A morphism of schemes over a base induces contravariant pullback on the
relative Picard presheaves and their fppf sheafifications. These maps preserve
the tensor group laws and satisfy identity and composition on the nose.
No properness, smoothness or representability hypothesis is needed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {base : Scheme.{u}} {source target thirdScheme : Over base}

/-- The map on families over a parameter scheme induced by a morphism over the base. -/
def picardFamilyMap (morphism : source ⟶ target) (parameter : Over base) :
    pullback source.hom parameter.hom ⟶ pullback target.hom parameter.hom :=
  pullback.lift (pullback.fst source.hom parameter.hom ≫ morphism.left)
    (pullback.snd source.hom parameter.hom) (by
      rw [Category.assoc, Over.w, pullback.condition])

@[simp]
theorem picardFamilyMap_id (parameter : Over base) :
    picardFamilyMap (𝟙 source) parameter = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [picardFamilyMap]

/-- Maps of families respect composition of morphisms over the base. -/
theorem picardFamilyMap_comp (firstMap : source ⟶ target)
    (secondMap : target ⟶ thirdScheme) (parameter : Over base) :
    picardFamilyMap (firstMap ≫ secondMap) parameter =
      picardFamilyMap firstMap parameter ≫ picardFamilyMap secondMap parameter := by
  apply pullback.hom_ext <;> simp [picardFamilyMap, Category.assoc]

/-- Pullback in the family variable commutes with restriction in the parameter variable. -/
theorem picardFamilyMap_naturality (morphism : source ⟶ target)
    {parameter otherParameter : Over base} (restriction : otherParameter ⟶ parameter) :
    baseChangeMap source.hom restriction ≫ picardFamilyMap morphism parameter =
      picardFamilyMap morphism otherParameter ≫ baseChangeMap target.hom restriction := by
  apply pullback.hom_ext <;> simp [picardFamilyMap, baseChangeMap, Category.assoc]

/-- Pullback on Picard classes as a natural transformation of group-valued presheaves. -/
def picardPresheafPullbackGrp (morphism : source ⟶ target) :
    picardPresheafGrp target.hom ⟶ picardPresheafGrp source.hom where
  app parameter := GrpCat.ofHom (Pic.mapHom (picardFamilyMap morphism parameter.unop))
  naturality _ _ restriction := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro picardClass
    change Pic.map (picardFamilyMap morphism _)
        (Pic.map (baseChangeMap target.hom restriction.unop) picardClass) =
      Pic.map (baseChangeMap source.hom restriction.unop)
        (Pic.map (picardFamilyMap morphism _) picardClass)
    rw [← Pic.map_comp, ← Pic.map_comp, picardFamilyMap_naturality]

/-- Pullback of line-bundle classes, forgetting the tensor group law. -/
def picardPresheafPullback (morphism : source ⟶ target) :
    picardPresheaf target.hom ⟶ picardPresheaf source.hom :=
  CategoryTheory.Functor.whiskerRight (picardPresheafPullbackGrp morphism) (forget GrpCat)

@[simp]
theorem picardPresheafPullbackGrp_id :
    picardPresheafPullbackGrp (𝟙 source) = 𝟙 (picardPresheafGrp source.hom) := by
  ext parameter picardClass
  change Pic.map (picardFamilyMap (𝟙 source) parameter.unop) picardClass = picardClass
  rw [picardFamilyMap_id, Pic.map_id]

/-- Picard pullback is contravariant in the morphism of schemes. -/
theorem picardPresheafPullbackGrp_comp (firstMap : source ⟶ target)
    (secondMap : target ⟶ thirdScheme) :
    picardPresheafPullbackGrp (firstMap ≫ secondMap) =
      picardPresheafPullbackGrp secondMap ≫ picardPresheafPullbackGrp firstMap := by
  ext parameter picardClass
  change Pic.map (picardFamilyMap (firstMap ≫ secondMap) parameter.unop) picardClass =
    Pic.map (picardFamilyMap firstMap parameter.unop)
      (Pic.map (picardFamilyMap secondMap parameter.unop) picardClass)
  rw [picardFamilyMap_comp, Pic.map_comp]

/-- The morphism of relative Picard sheaves induced by actual line-bundle pullback. -/
def picardFunctorPullback (morphism : source ⟶ target) :
    picardFunctor target.hom ⟶ picardFunctor source.hom :=
  (presheafToSheaf (fppfTopology.over base) (Type (u + 1))).map
    (picardPresheafPullback morphism)

/-- Pullback on relative Picard sheaves preserves their tensor group structures. -/
def picardFunctorPullbackGrp (morphism : source ⟶ target) :
    picardFunctorGrp target.hom ⟶ picardFunctorGrp source.hom :=
  sheafifyGrpMap (fppfTopology.over base) (picardPresheafPullbackGrp morphism)

/-- Forgetting the group structure recovers the actual sheaf morphism. -/
theorem picardFunctorPullbackGrp_whiskerRight (morphism : source ⟶ target) :
    CategoryTheory.Functor.whiskerRight (picardFunctorPullbackGrp morphism) (forget GrpCat) =
      (picardFunctorPullback morphism).hom :=
  rfl

/-- The Picard sheaf map classifies the pullback of every original bundle class. -/
@[simp]
theorem picardFunctorPullback_toPicardFunctor (morphism : source ⟶ target)
    (parameter : Over base) (picardClass : (pullback target.hom parameter.hom).Pic) :
    (picardFunctorPullback morphism).hom.app (.op parameter)
        ((toPicardFunctor target.hom).app (.op parameter) picardClass) =
      (toPicardFunctor source.hom).app (.op parameter)
        (Pic.map (picardFamilyMap morphism parameter) picardClass) :=
  sheafifyGrpMap_toSheafify (fppfTopology.over base)
    (picardPresheafPullbackGrp morphism) (.op parameter) picardClass

@[simp]
theorem picardFunctorPullbackGrp_id :
    picardFunctorPullbackGrp (𝟙 source) = 𝟙 (picardFunctorGrp source.hom) := by
  simp only [picardFunctorPullbackGrp, picardPresheafPullbackGrp_id,
    sheafifyGrpMap_id, picardFunctorGrp]

/-- Sheafified group pullback respects contravariant composition. -/
theorem picardFunctorPullbackGrp_comp (firstMap : source ⟶ target)
    (secondMap : target ⟶ thirdScheme) :
    picardFunctorPullbackGrp (firstMap ≫ secondMap) =
      picardFunctorPullbackGrp secondMap ≫ picardFunctorPullbackGrp firstMap := by
  simp only [picardFunctorPullbackGrp, picardPresheafPullbackGrp_comp, sheafifyGrpMap_comp]

@[simp]
theorem picardFunctorPullback_id :
    picardFunctorPullback (𝟙 source) = 𝟙 (picardFunctor source.hom) := by
  apply Sheaf.hom_ext
  have identity := congrArg
    (fun transformation : picardFunctorGrp source.hom ⟶ picardFunctorGrp source.hom ↦
      CategoryTheory.Functor.whiskerRight transformation (forget GrpCat))
    (picardFunctorPullbackGrp_id (source := source))
  simpa only [picardFunctorPullbackGrp_whiskerRight,
    CategoryTheory.Functor.whiskerRight_id', picardFunctorGrp_comp_forget,
    ObjectProperty.FullSubcategory.id_hom] using identity

/-- Pullback on the relative Picard sheaves is contravariantly functorial. -/
theorem picardFunctorPullback_comp (firstMap : source ⟶ target)
    (secondMap : target ⟶ thirdScheme) :
    picardFunctorPullback (firstMap ≫ secondMap) =
      picardFunctorPullback secondMap ≫ picardFunctorPullback firstMap := by
  simp only [picardFunctorPullback, picardPresheafPullback,
    picardPresheafPullbackGrp_comp, CategoryTheory.Functor.whiskerRight_comp,
    CategoryTheory.Functor.map_comp]

/-- The Picard sheaf pullback is determined by its action on original bundle classes. -/
theorem picardFunctorPullback_unique (morphism : source ⟶ target)
    (candidate : picardFunctor target.hom ⟶ picardFunctor source.hom)
    (compatibility : toPicardFunctor target.hom ≫ candidate.hom =
      picardPresheafPullback morphism ≫ toPicardFunctor source.hom) :
    candidate = picardFunctorPullback morphism := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (fppfTopology.over base) candidate.hom
    (picardFunctorPullback morphism).hom (picardFunctor source.hom).property
  exact compatibility.trans
    (toSheafify_naturality (fppfTopology.over base) (picardPresheafPullback morphism))

end AlgebraicGeometry
