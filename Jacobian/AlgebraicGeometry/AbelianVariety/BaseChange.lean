import Jacobian.AlgebraicGeometry.AbelianVariety.Basic
import Jacobian.AlgebraicGeometry.BaseChange.Field

/-!
# Extension of scalars for abelian varieties

Pullback preserves the commutative group scheme and its geometric properties.
Identity and tower comparisons retain the prescribed commutative-group maps.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory MonObj

namespace AlgebraicGeometry.AbelianVariety

set_option backward.isDefEq.respectTransparency.types false in
private theorem smooth_baseChange {baseField extensionField : Type u}
    [Field baseField] [Field extensionField] [Algebra baseField extensionField]
    (scheme : Over (Spec (.of baseField))) [Smooth scheme.hom] :
    Smooth ((AlgebraicGeometry.baseChange baseField extensionField).obj scheme).hom :=
  MorphismProperty.pullback_snd scheme.hom
    (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) inferInstance

/-- Extend the commutative group scheme and all its geometric structure. -/
def baseChange (baseField extensionField : Type u)
    [Field baseField] [Field extensionField] [Algebra baseField extensionField] :
    AbelianVariety baseField ⥤ AbelianVariety extensionField where
  obj variety :=
    { group := (AlgebraicGeometry.baseChange baseField extensionField).mapCommGrp.obj variety.group
      smooth := smooth_baseChange variety.group.X
      proper := inferInstanceAs (IsProper
        ((AlgebraicGeometry.baseChange baseField extensionField).obj variety.group.X).hom)
      geometricallyIrreducible := inferInstanceAs (GeometricallyIrreducible
        ((AlgebraicGeometry.baseChange baseField extensionField).obj variety.group.X).hom) }
  map morphism := InducedCategory.homMk
    ((AlgebraicGeometry.baseChange baseField extensionField).mapCommGrp.map morphism.hom)
  map_id variety := InducedCategory.hom_ext
    ((AlgebraicGeometry.baseChange baseField extensionField).mapCommGrp.map_id variety.group)
  map_comp first second := InducedCategory.hom_ext
    ((AlgebraicGeometry.baseChange baseField extensionField).mapCommGrp.map_comp first.hom second.hom)

private def natIsoOfForget {baseField extensionField : Type u}
    [Field baseField] [Field extensionField]
    (sourceFunctor targetFunctor : AbelianVariety baseField ⥤ AbelianVariety extensionField)
    (comparison : sourceFunctor ⋙ forget extensionField ≅
      targetFunctor ⋙ forget extensionField) : sourceFunctor ≅ targetFunctor :=
  NatIso.ofComponents (F := sourceFunctor) (G := targetFunctor)
    (fun variety ↦ InducedCategory.isoMk (F := AbelianVariety.group)
      (X := sourceFunctor.obj variety) (Y := targetFunctor.obj variety) (comparison.app variety))
    (fun morphism ↦ InducedCategory.hom_ext (comparison.hom.naturality morphism))

private theorem natIsoOfForget_app {baseField extensionField : Type u}
    [Field baseField] [Field extensionField]
    (sourceFunctor targetFunctor : AbelianVariety baseField ⥤ AbelianVariety extensionField)
    (comparison : sourceFunctor ⋙ forget extensionField ≅
      targetFunctor ⋙ forget extensionField) (variety : AbelianVariety baseField) :
    (forget extensionField).mapIso
        ((natIsoOfForget sourceFunctor targetFunctor comparison).app variety) =
      comparison.app variety := by
  apply Iso.ext
  rfl

private def idIsoOf (baseField : Type u) [Field baseField]
    (comparison : AlgebraicGeometry.baseChange baseField baseField ≅
      𝟭 (Over (Spec (.of baseField)))) :
    baseChange baseField baseField ≅ 𝟭 (AbelianVariety baseField) :=
  natIsoOfForget (baseChange baseField baseField) (𝟭 (AbelianVariety baseField))
    (Functor.isoWhiskerLeft (forget baseField)
      (Functor.mapCommGrpNatIso comparison ≪≫
        Functor.mapCommGrpIdIso (C := Over (Spec (.of baseField)))))

private theorem idIsoOf_app (baseField : Type u) [Field baseField]
    (comparison : AlgebraicGeometry.baseChange baseField baseField ≅
      𝟭 (Over (Spec (.of baseField)))) (variety : AbelianVariety baseField) :
    (forget baseField).mapIso ((idIsoOf baseField comparison).app variety) =
      (Functor.mapCommGrpNatIso comparison).app variety.group ≪≫
        (Functor.mapCommGrpIdIso (C := Over (Spec (.of baseField)))).app variety.group :=
  natIsoOfForget_app _ _ _ variety

/-- Identity field extension is canonically isomorphic to the identity on abelian varieties. -/
def baseChange.idIso (baseField : Type u) [Field baseField] :
    baseChange baseField baseField ≅ 𝟭 (AbelianVariety baseField) :=
  idIsoOf baseField (AlgebraicGeometry.baseChange.idIso baseField)

/-- The identity comparison has the prescribed commutative-group component. -/
@[simp]
theorem forget_mapIso_baseChange_idIso_app (baseField : Type u) [Field baseField]
    (variety : AbelianVariety baseField) :
    (forget baseField).mapIso ((baseChange.idIso baseField).app variety) =
      (Functor.mapCommGrpNatIso (AlgebraicGeometry.baseChange.idIso baseField)).app variety.group ≪≫
        (Functor.mapCommGrpIdIso (C := Over (Spec (.of baseField)))).app variety.group :=
  idIsoOf_app baseField _ variety

private def compIsoOf (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField]
    (comparison : AlgebraicGeometry.baseChange baseField extensionField ≅
      AlgebraicGeometry.baseChange baseField middleField ⋙
        AlgebraicGeometry.baseChange middleField extensionField) :
    baseChange baseField extensionField ≅
      baseChange baseField middleField ⋙ baseChange middleField extensionField :=
  natIsoOfForget (baseChange baseField extensionField)
    (baseChange baseField middleField ⋙ baseChange middleField extensionField)
    (Functor.isoWhiskerLeft (forget baseField)
      (Functor.mapCommGrpNatIso comparison ≪≫ Functor.mapCommGrpCompIso
        (F := AlgebraicGeometry.baseChange baseField middleField)
        (G := AlgebraicGeometry.baseChange middleField extensionField)))

private theorem compIsoOf_app (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField]
    (comparison : AlgebraicGeometry.baseChange baseField extensionField ≅
      AlgebraicGeometry.baseChange baseField middleField ⋙
        AlgebraicGeometry.baseChange middleField extensionField)
    (variety : AbelianVariety baseField) :
    (forget extensionField).mapIso
        ((compIsoOf baseField middleField extensionField comparison).app variety) =
      (Functor.mapCommGrpNatIso comparison).app variety.group ≪≫
        (Functor.mapCommGrpCompIso (F := AlgebraicGeometry.baseChange baseField middleField)
          (G := AlgebraicGeometry.baseChange middleField extensionField)).app variety.group :=
  natIsoOfForget_app _ _ _ variety

/-- Direct and iterated field extension are canonically isomorphic on abelian varieties. -/
def baseChange.compIso (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField] [IsScalarTower baseField middleField extensionField] :
    baseChange baseField extensionField ≅
      baseChange baseField middleField ⋙ baseChange middleField extensionField :=
  compIsoOf baseField middleField extensionField
    (AlgebraicGeometry.baseChange.compIso baseField middleField extensionField)

/-- The tower comparison has the prescribed commutative-group component. -/
@[simp]
theorem forget_mapIso_baseChange_compIso_app (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField] [IsScalarTower baseField middleField extensionField]
    (variety : AbelianVariety baseField) :
    (forget extensionField).mapIso
        ((baseChange.compIso baseField middleField extensionField).app variety) =
      (Functor.mapCommGrpNatIso
        (AlgebraicGeometry.baseChange.compIso baseField middleField extensionField)).app
          variety.group ≪≫
        (Functor.mapCommGrpCompIso (F := AlgebraicGeometry.baseChange baseField middleField)
          (G := AlgebraicGeometry.baseChange middleField extensionField)).app variety.group :=
  compIsoOf_app baseField middleField extensionField _ variety

end AlgebraicGeometry.AbelianVariety
