import Jacobian.AlgebraicGeometry.PointedCurve.Basic
import Jacobian.AlgebraicGeometry.Curve.BaseChange

/-!
# Extension of scalars for pointed curves

The point is transported using the canonical map from the terminal scheme.
Monoidal naturality makes the canonical identity and tower comparisons pointed.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.PointedCurve

/-- Extend scalars, transporting the specified rational point. -/
def baseChange (baseField extensionField : Type u)
    [Field baseField] [Field extensionField] [Algebra baseField extensionField] :
    PointedCurve baseField ⥤ PointedCurve extensionField where
  obj curve :=
    { curve := (Curve.baseChange baseField extensionField).obj curve.curve
      point := Functor.LaxMonoidal.ε (AlgebraicGeometry.baseChange baseField extensionField) ≫
        (AlgebraicGeometry.baseChange baseField extensionField).map curve.point }
  map {source target} morphism :=
    { map := (Curve.baseChange baseField extensionField).map morphism.map
      point_map := by
        change (Functor.LaxMonoidal.ε (AlgebraicGeometry.baseChange baseField extensionField) ≫
          (AlgebraicGeometry.baseChange baseField extensionField).map source.point) ≫
          (AlgebraicGeometry.baseChange baseField extensionField).map morphism.map = _
        rw [Category.assoc, ← Functor.map_comp, morphism.point_map]
        rfl }
  map_id curve := Hom.ext _ _ ((Curve.baseChange baseField extensionField).map_id curve.curve)
  map_comp first second := Hom.ext _ _
    ((Curve.baseChange baseField extensionField).map_comp first.map second.map)

private theorem mapPoint_naturality {baseField extensionField : Type u}
    [Field baseField] [Field extensionField]
    {sourceFunctor targetFunctor : Over (Spec (.of baseField)) ⥤ Over (Spec (.of extensionField))}
    [sourceFunctor.Monoidal] [targetFunctor.Monoidal]
    (comparison : sourceFunctor ⟶ targetFunctor) {scheme : Over (Spec (.of baseField))}
    (point : 𝟙_ (Over (Spec (.of baseField))) ⟶ scheme) :
    (Functor.LaxMonoidal.ε sourceFunctor ≫ sourceFunctor.map point) ≫ comparison.app scheme =
      Functor.LaxMonoidal.ε targetFunctor ≫ targetFunctor.map point := by
  rw [Category.assoc, comparison.naturality, ← Category.assoc, NatTrans.IsMonoidal.unit]

private def idIsoOf (baseField : Type u) [Field baseField]
    (comparison : AlgebraicGeometry.baseChange baseField baseField ≅
      𝟭 (Over (Spec (.of baseField)))) :
    baseChange baseField baseField ≅ 𝟭 (PointedCurve baseField) :=
  NatIso.ofComponents (F := baseChange baseField baseField) (G := 𝟭 (PointedCurve baseField))
    (fun curve ↦ isoMk (source := (baseChange baseField baseField).obj curve) (target := curve)
      (Curve.isoMk (C := ((baseChange baseField baseField).obj curve).curve)
        (D := curve.curve) (comparison.app curve.curve.carrier)) (by
        change (Functor.LaxMonoidal.ε (AlgebraicGeometry.baseChange baseField baseField) ≫
          (AlgebraicGeometry.baseChange baseField baseField).map curve.point) ≫
          comparison.hom.app curve.curve.carrier = _
        simpa only [Functor.LaxMonoidal.id_ε, Functor.id_map, Category.id_comp] using
          mapPoint_naturality comparison.hom curve.point))
    (fun morphism ↦ Hom.ext _ _ (comparison.hom.naturality morphism.map))

private theorem idIsoOf_app (baseField : Type u) [Field baseField]
    (comparison : AlgebraicGeometry.baseChange baseField baseField ≅
      𝟭 (Over (Spec (.of baseField)))) (curve : PointedCurve baseField) :
    (Curve.forget baseField).mapIso (forget.mapIso ((idIsoOf baseField comparison).app curve)) =
      comparison.app curve.curve.carrier := by
  apply Iso.ext
  rfl

/-- Identity extension preserves pointed curves with the canonical scheme comparison. -/
def baseChange.idIso (baseField : Type u) [Field baseField] :
    baseChange baseField baseField ≅ 𝟭 (PointedCurve baseField) :=
  idIsoOf baseField (AlgebraicGeometry.baseChange.idIso baseField)

/-- The identity comparison forgets to the canonical scheme pullback comparison. -/
@[simp]
theorem forget_mapIso_baseChange_idIso_app (baseField : Type u) [Field baseField]
    (curve : PointedCurve baseField) :
    (Curve.forget baseField).mapIso (forget.mapIso ((baseChange.idIso baseField).app curve)) =
      (AlgebraicGeometry.baseChange.idIso baseField).app curve.curve.carrier :=
  idIsoOf_app baseField _ curve

private def compIsoOf (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField]
    (comparison : AlgebraicGeometry.baseChange baseField extensionField ≅
      AlgebraicGeometry.baseChange baseField middleField ⋙
        AlgebraicGeometry.baseChange middleField extensionField) :
    baseChange baseField extensionField ≅
      baseChange baseField middleField ⋙ baseChange middleField extensionField :=
  NatIso.ofComponents (F := baseChange baseField extensionField)
    (G := baseChange baseField middleField ⋙ baseChange middleField extensionField)
    (fun curve ↦ isoMk (source := (baseChange baseField extensionField).obj curve)
      (target := (baseChange baseField middleField ⋙ baseChange middleField extensionField).obj
        curve)
      (Curve.isoMk (C := ((baseChange baseField extensionField).obj curve).curve)
        (D := ((baseChange baseField middleField ⋙ baseChange middleField extensionField).obj
          curve).curve) (comparison.app curve.curve.carrier)) (by
          change (Functor.LaxMonoidal.ε (AlgebraicGeometry.baseChange baseField extensionField) ≫
            (AlgebraicGeometry.baseChange baseField extensionField).map curve.point) ≫
            comparison.hom.app curve.curve.carrier =
              Functor.LaxMonoidal.ε (AlgebraicGeometry.baseChange middleField extensionField) ≫
                (AlgebraicGeometry.baseChange middleField extensionField).map
                  (Functor.LaxMonoidal.ε (AlgebraicGeometry.baseChange baseField middleField) ≫
                    (AlgebraicGeometry.baseChange baseField middleField).map curve.point)
          simpa only [Functor.LaxMonoidal.comp_ε, Functor.map_comp, Functor.comp_map,
            Category.assoc] using mapPoint_naturality comparison.hom curve.point))
    (fun morphism ↦ Hom.ext _ _ (comparison.hom.naturality morphism.map))

private theorem compIsoOf_app (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField]
    (comparison : AlgebraicGeometry.baseChange baseField extensionField ≅
      AlgebraicGeometry.baseChange baseField middleField ⋙
        AlgebraicGeometry.baseChange middleField extensionField)
    (curve : PointedCurve baseField) :
    (Curve.forget extensionField).mapIso
        (forget.mapIso ((compIsoOf baseField middleField extensionField comparison).app curve)) =
      comparison.app curve.curve.carrier := by
  apply Iso.ext
  rfl

/-- Direct and iterated extension are canonically isomorphic as pointed curves. -/
def baseChange.compIso (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField] [IsScalarTower baseField middleField extensionField] :
    baseChange baseField extensionField ≅
      baseChange baseField middleField ⋙ baseChange middleField extensionField :=
  compIsoOf baseField middleField extensionField
    (AlgebraicGeometry.baseChange.compIso baseField middleField extensionField)

/-- The tower comparison forgets to the canonical scheme pullback comparison. -/
@[simp]
theorem forget_mapIso_baseChange_compIso_app (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField] [IsScalarTower baseField middleField extensionField]
    (curve : PointedCurve baseField) :
    (Curve.forget extensionField).mapIso
        (forget.mapIso ((baseChange.compIso baseField middleField extensionField).app curve)) =
      (AlgebraicGeometry.baseChange.compIso baseField middleField extensionField).app
        curve.curve.carrier :=
  compIsoOf_app baseField middleField extensionField _ curve

end AlgebraicGeometry.PointedCurve
