import Jacobian.AlgebraicGeometry.Picard.BaseChange
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Jacobian.AlgebraicGeometry.Picard.DegreeBaseChange

/-!
# Degree parts of the Picard sheaf under field extension

A Cartesian change of the ground field identifies the degree parts of the
Picard presheaves and their fppf sheafifications, on all parameter schemes.
The comparison is actual pullback of invertible modules on the canonically
isomorphic products. The family need only be quasi-compact and quasi-separated.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {baseField extensionField : Type u} [Field baseField] [Field extensionField]
  {scheme extendedScheme : Scheme.{u}}
  {structureMap : scheme ⟶ Spec (.of baseField)}
  {extendedMap : extendedScheme ⟶ Spec (.of extensionField)}
  {baseMap : Spec (.of extensionField) ⟶ Spec (.of baseField)}
  {comparison : extendedScheme ⟶ scheme}
  [QuasiCompact structureMap] [QuasiSeparated structureMap]

/-- The canonical product comparison preserves every residue-fibre degree. -/
theorem picardPresheafDegree_pullbackIsoOfIsPullback
    (square : IsPullback comparison extendedMap structureMap baseMap)
    (parameter : Over (Spec (.of extensionField)))
    (picardClass : (picardPresheaf structureMap).obj (.op ((Over.map baseMap).obj parameter)))
    (point : parameter.left) :
    picardPresheafDegree extendedMap
        (Pic.map (pullbackIsoOfIsPullback square parameter).hom picardClass) point =
      picardPresheafDegree structureMap picardClass point := by
  have productSquare : IsPullback (pullbackIsoOfIsPullback square parameter).hom
      (pullback.snd extendedMap parameter.hom)
      (pullback.snd structureMap (parameter.hom ≫ baseMap)) (𝟙 parameter.left) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id, pullbackIsoOfIsPullback_hom_snd]⟩
  simpa using picardPresheafDegree_pic_map_of_isPullback structureMap extendedMap
    (𝟙 parameter.left) (pullbackIsoOfIsPullback square parameter).hom productSquare
    picardClass point

/-- A Picard class belongs to degree `degree` before extension exactly when its
canonical pullback belongs to that degree after extension. -/
theorem mem_picardSubfunctorDegree_pullbackIsoOfIsPullback_iff
    (square : IsPullback comparison extendedMap structureMap baseMap)
    (parameter : Over (Spec (.of extensionField)))
    (picardClass : (picardPresheaf structureMap).obj (.op ((Over.map baseMap).obj parameter)))
    (degree : ℤ) :
    Pic.map (pullbackIsoOfIsPullback square parameter).hom picardClass ∈
        (picardSubfunctorDegree extendedMap degree).obj (.op parameter) ↔
      picardClass ∈ (picardSubfunctorDegree structureMap degree).obj
        (.op ((Over.map baseMap).obj parameter)) := by
  have : QuasiCompact extendedMap := MorphismProperty.of_isPullback square inferInstance
  have : QuasiSeparated extendedMap := MorphismProperty.of_isPullback square inferInstance
  rw [mem_picardSubfunctorDegree_iff, mem_picardSubfunctorDegree_iff]
  simp_rw [picardPresheafDegree_pullbackIsoOfIsPullback square]
  rfl

/-- Restriction of test schemes identifies the degree parts of Cartesian families. -/
def picardPresheafDegreeIsoOfIsPullback
    (square : IsPullback comparison extendedMap structureMap baseMap) (degree : ℤ) :
    (Over.map baseMap).op ⋙ (picardSubfunctorDegree structureMap degree).toFunctor ≅
      (picardSubfunctorDegree extendedMap degree).toFunctor :=
  NatIso.ofComponents
    (fun parameter ↦ Equiv.toIso
      (((picardPresheafIsoOfIsPullback square).app parameter).toEquiv.subtypeEquiv
        (fun picardClass ↦
          (mem_picardSubfunctorDegree_pullbackIsoOfIsPullback_iff square parameter.unop
            picardClass degree).symm)))
    (by
      intro parameter otherParameter restriction
      ext picardClass
      apply Subtype.ext
      exact NatTrans.naturality_apply (picardPresheafIsoOfIsPullback square).hom
        restriction picardClass.val)

/-- Degree parts of the relative Picard sheaf commute with Cartesian field extension. -/
def picardFunctorDegreeIsoOfIsPullback
    (square : IsPullback comparison extendedMap structureMap baseMap) (degree : ℤ) :
    (Over.map baseMap).op ⋙ (picardFunctorDegree structureMap degree).obj ≅
      (picardFunctorDegree extendedMap degree).obj :=
  overMapOpCompSheafifyIso baseMap (picardSubfunctorDegree structureMap degree).toFunctor ≪≫
    (sheafToPresheaf _ _).mapIso
      ((presheafToSheaf _ _).mapIso (picardPresheafDegreeIsoOfIsPullback square degree))

/-- On generating classes the sheaf comparison is exactly the presheaf comparison. -/
@[reassoc]
theorem whiskerLeft_toSheafify_picardFunctorDegreeIsoOfIsPullback_hom
    (square : IsPullback comparison extendedMap structureMap baseMap) (degree : ℤ) :
    CategoryTheory.Functor.whiskerLeft (Over.map baseMap).op
        (toSheafify (fppfTopology.over (Spec (.of baseField)))
          (picardSubfunctorDegree structureMap degree).toFunctor) ≫
        (picardFunctorDegreeIsoOfIsPullback square degree).hom =
      (picardPresheafDegreeIsoOfIsPullback square degree).hom ≫
        toSheafify (fppfTopology.over (Spec (.of extensionField)))
          (picardSubfunctorDegree extendedMap degree).toFunctor := by
  rw [picardFunctorDegreeIsoOfIsPullback, Iso.trans_hom,
    whiskerLeft_toSheafify_overMapOpCompSheafifyIso_hom_assoc, toSheafify_naturality,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_hom]
  rfl

/-- The field-extension comparison sends an actual Picard class to its canonical pullback. -/
theorem picardFunctorDegreeIsoOfIsPullback_hom_app_toSheafify
    (square : IsPullback comparison extendedMap structureMap baseMap) (degree : ℤ)
    (parameter : Over (Spec (.of extensionField)))
    (picardClass : (picardSubfunctorDegree structureMap degree).toFunctor.obj
      (.op ((Over.map baseMap).obj parameter))) :
    (picardFunctorDegreeIsoOfIsPullback square degree).hom.app (.op parameter)
        ((toSheafify (fppfTopology.over (Spec (.of baseField)))
          (picardSubfunctorDegree structureMap degree).toFunctor).app _ picardClass) =
      (toSheafify (fppfTopology.over (Spec (.of extensionField)))
        (picardSubfunctorDegree extendedMap degree).toFunctor).app _
        ((picardPresheafDegreeIsoOfIsPullback square degree).hom.app
          (.op parameter) picardClass) := by
  have component := NatTrans.congr_app
    (whiskerLeft_toSheafify_picardFunctorDegreeIsoOfIsPullback_hom square degree)
    (.op parameter)
  simp only [NatTrans.comp_app, CategoryTheory.Functor.whiskerLeft_app] at component
  rw [← ConcreteCategory.comp_apply, ← component, ConcreteCategory.comp_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The degree-part comparison is the restriction of the full Picard comparison. -/
theorem picardFunctorDegreeIsoOfIsPullback_inclusion
    (square : IsPullback comparison extendedMap structureMap baseMap) (degree : ℤ) :
    (picardFunctorDegreeIsoOfIsPullback square degree).hom ≫
        (picardFunctorDegreeι extendedMap degree).hom =
      CategoryTheory.Functor.whiskerLeft (Over.map baseMap).op
          (picardFunctorDegreeι structureMap degree).hom ≫
        (picardFunctorIsoOfIsPullback square).hom := by
  let topology := fppfTopology.over (Spec (.of extensionField))
  let presentation := CategoryTheory.Functor.whiskerLeft (Over.map baseMap).op
    (toSheafify (fppfTopology.over (Spec (.of baseField)))
      (picardSubfunctorDegree structureMap degree).toFunctor)
  haveI : Presheaf.IsLocallySurjective topology presentation :=
    Presheaf.isLocallySurjective_whisker topology
      (fppfTopology.over (Spec (.of baseField))) (Over.map baseMap)
      (toSheafify (fppfTopology.over (Spec (.of baseField)))
        (picardSubfunctorDegree structureMap degree).toFunctor)
  let firstMap := (picardFunctorDegreeIsoOfIsPullback square degree).hom ≫
    (picardFunctorDegreeι extendedMap degree).hom
  let secondMap := CategoryTheory.Functor.whiskerLeft (Over.map baseMap).op
    (picardFunctorDegreeι structureMap degree).hom ≫
      (picardFunctorIsoOfIsPullback square).hom
  have onClasses (parameter : Over (Spec (.of extensionField)))
      (picardClass : (picardSubfunctorDegree structureMap degree).toFunctor.obj
        (.op ((Over.map baseMap).obj parameter))) :
      firstMap.app (.op parameter) (presentation.app (.op parameter) picardClass) =
        secondMap.app (.op parameter) (presentation.app (.op parameter) picardClass) := by
    change (picardFunctorDegreeι extendedMap degree).hom.app _
        ((picardFunctorDegreeIsoOfIsPullback square degree).hom.app _
          ((toSheafify (fppfTopology.over (Spec (.of baseField)))
            (picardSubfunctorDegree structureMap degree).toFunctor).app _ picardClass)) =
      (picardFunctorIsoOfIsPullback square).hom.app _
        ((picardFunctorDegreeι structureMap degree).hom.app _
          ((toSheafify (fppfTopology.over (Spec (.of baseField)))
            (picardSubfunctorDegree structureMap degree).toFunctor).app _ picardClass))
    rw [picardFunctorDegreeIsoOfIsPullback_hom_app_toSheafify,
      picardFunctorDegreeι_app_toSheafify, picardFunctorDegreeι_app_toSheafify,
      picardFunctorIsoOfIsPullback_hom_app_toPicardFunctor]
    rfl
  ext parameter sectionValue
  let coveringSieve := Presheaf.imageSieve presentation sectionValue
  have covering : coveringSieve ∈ topology parameter.unop :=
    Presheaf.imageSieve_mem topology presentation sectionValue
  apply (((isSheaf_iff_isSheaf_of_type topology _).1
    (picardFunctor extendedMap).property).isSeparated coveringSieve covering).ext
  rintro cover restriction ⟨picardClass, classEquality⟩
  change (picardFunctor extendedMap).obj.map restriction.op (firstMap.app parameter sectionValue) =
    (picardFunctor extendedMap).obj.map restriction.op (secondMap.app parameter sectionValue)
  have localEquality : presentation.app (.op cover) picardClass =
      (((Over.map baseMap).op ⋙ (picardFunctorDegree structureMap degree).obj).map
        restriction.op) sectionValue := classEquality
  rw [← firstMap.naturality_apply, ← secondMap.naturality_apply, ← localEquality]
  exact onClasses cover picardClass

end AlgebraicGeometry
