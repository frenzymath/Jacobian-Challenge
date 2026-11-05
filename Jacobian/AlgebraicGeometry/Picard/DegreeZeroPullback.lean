import Jacobian.AlgebraicGeometry.Curve.PullbackDegreeFamily
import Jacobian.AlgebraicGeometry.Picard.DegreeZero

/-!
# Pullback on degree-zero Picard sheaves

Every morphism of smooth proper geometrically irreducible curves induces
contravariant pullback on their degree-zero Picard sheaves and tensor group
structures. The restriction is uniquely determined by the full Picard sheaf
map. Given representing schemes, these transformations induce group morphisms
with the same identity and composition laws. Representability is supplied,
not asserted here.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {baseField : Type u} [Field baseField]
  {source target thirdCurve : Curve baseField}

/-- Actual curve pullback restricts to the degree-zero Picard group presheaves. -/
def picardDegreeZeroPresheafPullbackGrp (morphism : source ⟶ target) :
    picardDegreeZeroPresheafGrp target.carrier.hom ⟶
      picardDegreeZeroPresheafGrp source.carrier.hom where
  app parameter := GrpCat.ofHom
    { toFun := fun picardClass ↦
        ⟨Pic.map (picardFamilyMap morphism parameter.unop) picardClass.val,
          Curve.mem_picardSubfunctorDegree_zero_pullback source target morphism
            parameter.unop picardClass.val picardClass.property⟩
      map_one' := Subtype.ext (map_one (Pic.mapHom (picardFamilyMap morphism parameter.unop)))
      map_mul' firstClass secondClass := Subtype.ext
        (map_mul (Pic.mapHom (picardFamilyMap morphism parameter.unop))
          firstClass.val secondClass.val) }
  naturality _ _ restriction := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro picardClass
    apply Subtype.ext
    change Pic.map (picardFamilyMap morphism _)
        (Pic.map (baseChangeMap target.carrier.hom restriction.unop) picardClass.val) =
      Pic.map (baseChangeMap source.carrier.hom restriction.unop)
        (Pic.map (picardFamilyMap morphism _) picardClass.val)
    rw [← Pic.map_comp, ← Pic.map_comp, picardFamilyMap_naturality]

/-- The underlying transformation of the degree-zero Picard subpresheaves. -/
def picardDegreeZeroPresheafPullback (morphism : source ⟶ target) :
    (picardSubfunctorDegree target.carrier.hom 0).toFunctor ⟶
      (picardSubfunctorDegree source.carrier.hom 0).toFunctor :=
  CategoryTheory.Functor.whiskerRight (picardDegreeZeroPresheafPullbackGrp morphism)
    (forget GrpCat)

@[simp]
theorem picardDegreeZeroPresheafPullbackGrp_id :
    picardDegreeZeroPresheafPullbackGrp (𝟙 source) =
      𝟙 (picardDegreeZeroPresheafGrp source.carrier.hom) := by
  apply NatTrans.ext
  funext parameter
  apply GrpCat.hom_ext
  refine MonoidHom.ext fun
    (picardClass : picardDegreeZeroSubgroup source.carrier.hom parameter.unop) ↦ ?_
  apply Subtype.ext
  change Pic.map (picardFamilyMap (𝟙 source.carrier) parameter.unop) picardClass.val =
    picardClass.val
  rw [picardFamilyMap_id, Pic.map_id]

/-- Degree-zero presheaf pullback respects contravariant composition. -/
theorem picardDegreeZeroPresheafPullbackGrp_comp (firstMap : source ⟶ target)
    (secondMap : target ⟶ thirdCurve) :
    picardDegreeZeroPresheafPullbackGrp (firstMap ≫ secondMap) =
      picardDegreeZeroPresheafPullbackGrp secondMap ≫
        picardDegreeZeroPresheafPullbackGrp firstMap := by
  ext parameter picardClass
  apply Subtype.ext
  change Pic.map (picardFamilyMap (firstMap ≫ secondMap) parameter.unop) picardClass.val =
    Pic.map (picardFamilyMap firstMap parameter.unop)
      (Pic.map (picardFamilyMap secondMap parameter.unop) picardClass.val)
  rw [picardFamilyMap_comp, Pic.map_comp]

/-- Pullback between the degree-zero Picard sheaves. -/
def picardDegreeZeroFunctorPullback (morphism : source ⟶ target) :
    picardFunctorDegree target.carrier.hom 0 ⟶ picardFunctorDegree source.carrier.hom 0 :=
  (presheafToSheaf (fppfTopology.over (Spec (.of baseField))) (Type (u + 1))).map
    (picardDegreeZeroPresheafPullback morphism)

/-- The degree-zero sheaf pullback as a natural transformation of group-valued functors. -/
def picardDegreeZeroFunctorPullbackGrp (morphism : source ⟶ target) :
    picardDegreeZeroFunctorGrp target.carrier.hom ⟶
      picardDegreeZeroFunctorGrp source.carrier.hom :=
  sheafifyGrpMap (fppfTopology.over (Spec (.of baseField)))
    (picardDegreeZeroPresheafPullbackGrp morphism)

/-- Forgetting the tensor law gives the same degree-zero Picard sheaf map. -/
theorem picardDegreeZeroFunctorPullbackGrp_whiskerRight (morphism : source ⟶ target) :
    CategoryTheory.Functor.whiskerRight (picardDegreeZeroFunctorPullbackGrp morphism)
        (forget GrpCat) = (picardDegreeZeroFunctorPullback morphism).hom :=
  rfl

/-- The sheafified map acts by actual pullback on original degree-zero classes. -/
@[simp]
theorem picardDegreeZeroFunctorPullback_toSheafify (morphism : source ⟶ target)
    (parameter : Over (Spec (.of baseField)))
    (picardClass : picardDegreeZeroSubgroup target.carrier.hom parameter) :
    (picardDegreeZeroFunctorPullback morphism).hom.app (.op parameter)
        ((toSheafify (fppfTopology.over (Spec (.of baseField)))
          (picardSubfunctorDegree target.carrier.hom 0).toFunctor).app (.op parameter)
            picardClass) =
      (toSheafify (fppfTopology.over (Spec (.of baseField)))
        (picardSubfunctorDegree source.carrier.hom 0).toFunctor).app (.op parameter)
          ((picardDegreeZeroPresheafPullbackGrp morphism).app (.op parameter) picardClass) :=
  sheafifyGrpMap_toSheafify (fppfTopology.over (Spec (.of baseField)))
    (picardDegreeZeroPresheafPullbackGrp morphism) (.op parameter) picardClass

@[simp]
theorem picardDegreeZeroFunctorPullbackGrp_id :
    picardDegreeZeroFunctorPullbackGrp (𝟙 source) =
      𝟙 (picardDegreeZeroFunctorGrp source.carrier.hom) := by
  simp only [picardDegreeZeroFunctorPullbackGrp,
    picardDegreeZeroPresheafPullbackGrp_id, sheafifyGrpMap_id, picardDegreeZeroFunctorGrp]

/-- Degree-zero sheaf pullback respects contravariant composition. -/
theorem picardDegreeZeroFunctorPullbackGrp_comp (firstMap : source ⟶ target)
    (secondMap : target ⟶ thirdCurve) :
    picardDegreeZeroFunctorPullbackGrp (firstMap ≫ secondMap) =
      picardDegreeZeroFunctorPullbackGrp secondMap ≫ picardDegreeZeroFunctorPullbackGrp firstMap := by
  simp only [picardDegreeZeroFunctorPullbackGrp,
    picardDegreeZeroPresheafPullbackGrp_comp, sheafifyGrpMap_comp]

/-- The degree-zero pullback is a restriction of the full Picard sheaf pullback. -/
theorem picardDegreeZeroFunctorPullback_inclusion (morphism : source ⟶ target) :
    picardDegreeZeroFunctorPullback morphism ≫ picardFunctorDegreeι source.carrier.hom 0 =
      picardFunctorDegreeι target.carrier.hom 0 ≫ picardFunctorPullback morphism := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (fppfTopology.over (Spec (.of baseField))) _ _
    (picardFunctor source.carrier.hom).property
  ext parameter picardClass
  change (picardFunctorDegreeι source.carrier.hom 0).hom.app parameter
      ((picardDegreeZeroFunctorPullback morphism).hom.app parameter
        ((toSheafify (fppfTopology.over (Spec (.of baseField)))
          (picardSubfunctorDegree target.carrier.hom 0).toFunctor).app parameter picardClass)) =
    (picardFunctorPullback morphism).hom.app parameter
      ((picardFunctorDegreeι target.carrier.hom 0).hom.app parameter
        ((toSheafify (fppfTopology.over (Spec (.of baseField)))
          (picardSubfunctorDegree target.carrier.hom 0).toFunctor).app parameter picardClass))
  rw [picardDegreeZeroFunctorPullback_toSheafify,
    picardFunctorDegreeι_app_toSheafify, picardFunctorDegreeι_app_toSheafify,
    picardFunctorPullback_toPicardFunctor]
  rfl

/-- There is only one degree-zero restriction of the full Picard pullback map. -/
theorem picardDegreeZeroFunctorPullback_unique (morphism : source ⟶ target)
    (candidate : picardFunctorDegree target.carrier.hom 0 ⟶
      picardFunctorDegree source.carrier.hom 0)
    (compatibility : candidate ≫ picardFunctorDegreeι source.carrier.hom 0 =
      picardFunctorDegreeι target.carrier.hom 0 ≫ picardFunctorPullback morphism) :
    candidate = picardDegreeZeroFunctorPullback morphism := by
  have equality : candidate ≫ picardFunctorDegreeι source.carrier.hom 0 =
      picardDegreeZeroFunctorPullback morphism ≫ picardFunctorDegreeι source.carrier.hom 0 :=
    compatibility.trans (picardDegreeZeroFunctorPullback_inclusion morphism).symm
  apply Sheaf.hom_ext
  ext parameter sectionValue
  apply injective_picardFunctorDegreeι_app source.carrier.hom 0 parameter.unop
  exact ConcreteCategory.congr_hom (congr_app
    (congrArg (fun map : picardFunctorDegree target.carrier.hom 0 ⟶
      picardFunctor source.carrier.hom ↦ map.hom) equality) parameter) sectionValue

/-- A represented degree-zero Picard pullback is a group morphism. -/
def picardDegreeZeroRepresentedPullback (morphism : source ⟶ target)
    {sourceRepresentative targetRepresentative : Over (Spec (.of baseField))}
    (sourceRepresentation :
      (picardFunctorDegree source.carrier.hom 0).obj.RepresentableBy sourceRepresentative)
    (targetRepresentation :
      (picardFunctorDegree target.carrier.hom 0).obj.RepresentableBy targetRepresentative) :
    letI := picardDegreeZeroCommGrpObj source.carrier.hom sourceRepresentation
    letI := picardDegreeZeroCommGrpObj target.carrier.hom targetRepresentation
    CommGrp.mk targetRepresentative ⟶ CommGrp.mk sourceRepresentative := by
  letI := picardDegreeZeroCommGrpObj source.carrier.hom sourceRepresentation
  letI := picardDegreeZeroCommGrpObj target.carrier.hom targetRepresentation
  exact ⟨GrpObj.mapOfRepresentableBy
    (sourceFunctor := picardDegreeZeroFunctorGrp target.carrier.hom)
    (targetFunctor := picardDegreeZeroFunctorGrp source.carrier.hom)
    targetRepresentation sourceRepresentation (picardDegreeZeroFunctorPullbackGrp morphism)⟩

/-- The represented group morphism realizes the degree-zero sheaf transformation. -/
theorem picardDegreeZeroRepresentedPullback_app (morphism : source ⟶ target)
    {sourceRepresentative targetRepresentative : Over (Spec (.of baseField))}
    (sourceRepresentation :
      (picardFunctorDegree source.carrier.hom 0).obj.RepresentableBy sourceRepresentative)
    (targetRepresentation :
      (picardFunctorDegree target.carrier.hom 0).obj.RepresentableBy targetRepresentative)
    (parameter : Over (Spec (.of baseField))) (point : parameter ⟶ targetRepresentative) :
    letI := picardDegreeZeroCommGrpObj source.carrier.hom sourceRepresentation
    letI := picardDegreeZeroCommGrpObj target.carrier.hom targetRepresentation
    sourceRepresentation.homEquiv (point ≫
        (picardDegreeZeroRepresentedPullback morphism sourceRepresentation
          targetRepresentation).hom.hom.hom) =
      (picardDegreeZeroFunctorPullbackGrp morphism).app (.op parameter)
        (targetRepresentation.homEquiv point) := by
  letI := picardDegreeZeroCommGrpObj source.carrier.hom sourceRepresentation
  letI := picardDegreeZeroCommGrpObj target.carrier.hom targetRepresentation
  exact GrpObj.homEquiv_mapOfRepresentableBy
    (sourceFunctor := picardDegreeZeroFunctorGrp target.carrier.hom)
    (targetFunctor := picardDegreeZeroFunctorGrp source.carrier.hom)
    targetRepresentation sourceRepresentation (picardDegreeZeroFunctorPullbackGrp morphism) point

@[simp]
theorem picardDegreeZeroRepresentedPullback_id
    {representative : Over (Spec (.of baseField))}
    (representation :
      (picardFunctorDegree source.carrier.hom 0).obj.RepresentableBy representative) :
    letI := picardDegreeZeroCommGrpObj source.carrier.hom representation
    picardDegreeZeroRepresentedPullback (𝟙 source) representation representation =
      𝟙 (CommGrp.mk representative) := by
  letI := picardDegreeZeroCommGrpObj source.carrier.hom representation
  apply CommGrp.hom_ext
  change (GrpObj.mapOfRepresentableBy
      (sourceFunctor := picardDegreeZeroFunctorGrp source.carrier.hom)
      (targetFunctor := picardDegreeZeroFunctorGrp source.carrier.hom)
      representation representation (picardDegreeZeroFunctorPullbackGrp (𝟙 source))).hom.hom = _
  rw [picardDegreeZeroFunctorPullbackGrp_id, GrpObj.mapOfRepresentableBy_id]
  simp only [CommGrp.id_hom, Grp.id_hom_hom]

/-- Represented degree-zero Picard pullbacks satisfy contravariant composition. -/
theorem picardDegreeZeroRepresentedPullback_comp (firstMap : source ⟶ target)
    (secondMap : target ⟶ thirdCurve)
    {sourceRepresentative targetRepresentative thirdRepresentative : Over (Spec (.of baseField))}
    (sourceRepresentation :
      (picardFunctorDegree source.carrier.hom 0).obj.RepresentableBy sourceRepresentative)
    (targetRepresentation :
      (picardFunctorDegree target.carrier.hom 0).obj.RepresentableBy targetRepresentative)
    (thirdRepresentation :
      (picardFunctorDegree thirdCurve.carrier.hom 0).obj.RepresentableBy thirdRepresentative) :
    letI := picardDegreeZeroCommGrpObj source.carrier.hom sourceRepresentation
    letI := picardDegreeZeroCommGrpObj target.carrier.hom targetRepresentation
    letI := picardDegreeZeroCommGrpObj thirdCurve.carrier.hom thirdRepresentation
    picardDegreeZeroRepresentedPullback (firstMap ≫ secondMap)
        sourceRepresentation thirdRepresentation =
      picardDegreeZeroRepresentedPullback secondMap targetRepresentation thirdRepresentation ≫
        picardDegreeZeroRepresentedPullback firstMap sourceRepresentation targetRepresentation := by
  letI := picardDegreeZeroCommGrpObj source.carrier.hom sourceRepresentation
  letI := picardDegreeZeroCommGrpObj target.carrier.hom targetRepresentation
  letI := picardDegreeZeroCommGrpObj thirdCurve.carrier.hom thirdRepresentation
  apply CommGrp.hom_ext
  change (GrpObj.mapOfRepresentableBy
      (sourceFunctor := picardDegreeZeroFunctorGrp thirdCurve.carrier.hom)
      (targetFunctor := picardDegreeZeroFunctorGrp source.carrier.hom)
      thirdRepresentation sourceRepresentation
      (picardDegreeZeroFunctorPullbackGrp (firstMap ≫ secondMap))).hom.hom =
    (GrpObj.mapOfRepresentableBy
        (sourceFunctor := picardDegreeZeroFunctorGrp thirdCurve.carrier.hom)
        (targetFunctor := picardDegreeZeroFunctorGrp target.carrier.hom)
        thirdRepresentation targetRepresentation (picardDegreeZeroFunctorPullbackGrp secondMap) ≫
      GrpObj.mapOfRepresentableBy
        (sourceFunctor := picardDegreeZeroFunctorGrp target.carrier.hom)
        (targetFunctor := picardDegreeZeroFunctorGrp source.carrier.hom)
        targetRepresentation sourceRepresentation
        (picardDegreeZeroFunctorPullbackGrp firstMap)).hom.hom
  rw [picardDegreeZeroFunctorPullbackGrp_comp, GrpObj.mapOfRepresentableBy_comp]

end AlgebraicGeometry
