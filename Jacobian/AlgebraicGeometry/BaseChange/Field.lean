import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Jacobian.CategoryTheory.Comma.Over.Pullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Extension of the ground field

Base change along a field extension is pullback over the corresponding map of
spectra. It preserves properness, geometric irreducibility, and smoothness of
any fixed relative dimension. The identity and tower comparisons are the
canonical comparisons for pullback functors.
-/

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Base change of `k`-schemes along a field homomorphism `k → L`, i.e. `X ↦ X ×_{Spec k} Spec L`. -/
noncomputable abbrev baseChange (k L : Type u) [Field k] [Field L] [Algebra k L] :
    Over (Spec (.of k)) ⥤ Over (Spec (.of L)) :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))

set_option backward.isDefEq.respectTransparency.types false in
instance {k L : Type u} [Field k] [Field L] [Algebra k L] (C : Over (Spec (.of k)))
    [IsProper C.hom] : IsProper ((baseChange k L).obj C).hom :=
  MorphismProperty.pullback_snd C.hom
    (Spec.map (CommRingCat.ofHom (algebraMap k L))) inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance {k L : Type u} [Field k] [Field L] [Algebra k L] (C : Over (Spec (.of k)))
    [GeometricallyIrreducible C.hom] : GeometricallyIrreducible ((baseChange k L).obj C).hom :=
  MorphismProperty.pullback_snd C.hom
    (Spec.map (CommRingCat.ofHom (algebraMap k L))) inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance {n : ℕ} {k L : Type u} [Field k] [Field L] [Algebra k L] (C : Over (Spec (.of k)))
    [SmoothOfRelativeDimension n C.hom] :
    SmoothOfRelativeDimension n ((baseChange k L).obj C).hom :=
  have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  MorphismProperty.pullback_snd C.hom
    (Spec.map (CommRingCat.ofHom (algebraMap k L))) inferInstance

-- These instances expose geometric properties through identity and composite functors.
instance {k : Type u} [Field k] (C : Over (Spec (.of k))) [IsProper C.hom] :
    IsProper ((𝟭 (Over (Spec (.of k)))).obj C).hom := ‹_›
instance {k : Type u} [Field k] (C : Over (Spec (.of k))) [GeometricallyIrreducible C.hom] :
    GeometricallyIrreducible ((𝟭 (Over (Spec (.of k)))).obj C).hom := ‹_›
instance {n : ℕ} {k : Type u} [Field k] (C : Over (Spec (.of k))) [SmoothOfRelativeDimension n C.hom] :
    SmoothOfRelativeDimension n ((𝟭 (Over (Spec (.of k)))).obj C).hom := ‹_›

instance {k L M : Type u} [Field k] [Field L] [Field M] [Algebra k L] [Algebra L M]
    (C : Over (Spec (.of k))) [IsProper C.hom] :
    IsProper ((baseChange k L ⋙ baseChange L M).obj C).hom :=
  inferInstanceAs (IsProper ((baseChange L M).obj ((baseChange k L).obj C)).hom)
instance {k L M : Type u} [Field k] [Field L] [Field M] [Algebra k L] [Algebra L M]
    (C : Over (Spec (.of k))) [GeometricallyIrreducible C.hom] :
    GeometricallyIrreducible ((baseChange k L ⋙ baseChange L M).obj C).hom :=
  inferInstanceAs (GeometricallyIrreducible ((baseChange L M).obj ((baseChange k L).obj C)).hom)
instance {n : ℕ} {k L M : Type u} [Field k] [Field L] [Field M] [Algebra k L] [Algebra L M]
    (C : Over (Spec (.of k))) [SmoothOfRelativeDimension n C.hom] :
    SmoothOfRelativeDimension n ((baseChange k L ⋙ baseChange L M).obj C).hom :=
  inferInstanceAs (SmoothOfRelativeDimension n ((baseChange L M).obj ((baseChange k L).obj C)).hom)

/-- Base change along `k → k` is the identity functor. -/
noncomputable def baseChange.idIso (k : Type u) [Field k] :
    baseChange k k ≅ 𝟭 (Over (Spec (.of k))) :=
  eqToIso (by
    show Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k k))) = Over.pullback (𝟙 _)
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]) ≪≫ Over.pullbackId

/-- Base change along a tower `k → L → M` is the composite of the two base changes. -/
noncomputable def baseChange.compIso (k L M : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra L M] [Algebra k M] [IsScalarTower k L M] :
    baseChange k M ≅ baseChange k L ⋙ baseChange L M :=
  eqToIso (by
    show Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k M))) =
      Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap L M)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k L)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]) ≪≫
    Over.pullbackComp _ _

private theorem pullbackIdentityProjection {base : Scheme.{u}} (baseMap : base ⟶ base)
    (identity : baseMap = 𝟙 base) (object : Over base) :
    (((eqToIso (congrArg (fun morphism ↦ Over.pullback morphism) identity) ≪≫
      Over.pullbackId).app object).hom).left = pullback.fst object.hom baseMap := by
  subst baseMap
  simpa using Over.pullbackId_hom_app_left base object

private theorem pullbackTowerProjection {base middle extension : Scheme.{u}}
    (firstMap : extension ⟶ middle) (secondMap : middle ⟶ base)
    (compositeMap : extension ⟶ base) (composition : compositeMap = firstMap ≫ secondMap)
    (object : Over base) :
    (((eqToIso (congrArg (fun morphism ↦ Over.pullback morphism) composition) ≪≫
      Over.pullbackComp firstMap secondMap).app object).hom).left ≫
      pullback.fst (pullback.snd object.hom secondMap) firstMap ≫
        pullback.fst object.hom secondMap = pullback.fst object.hom compositeMap := by
  subst compositeMap
  simpa using Over.pullbackComp_hom_app_left_fst_fst firstMap secondMap object

/-- The canonical identity field comparison is the first projection. -/
theorem baseChange.idIso_hom_app_left (baseField : Type u) [Field baseField]
    (object : Over (Spec (.of baseField))) :
    (((baseChange.idIso baseField).app object).hom).left =
      pullback.fst object.hom
        (Spec.map (CommRingCat.ofHom (algebraMap baseField baseField))) := by
  exact pullbackIdentityProjection _
    (by simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]) object

/-- The canonical tower comparison preserves the original projection. -/
theorem baseChange.compIso_hom_app_left_fst_fst
    (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField] [IsScalarTower baseField middleField extensionField]
    (object : Over (Spec (.of baseField))) :
    (((baseChange.compIso baseField middleField extensionField).app object).hom).left ≫
      pullback.fst (pullback.snd object.hom
        (Spec.map (CommRingCat.ofHom (algebraMap baseField middleField))))
        (Spec.map (CommRingCat.ofHom (algebraMap middleField extensionField))) ≫
      pullback.fst object.hom
        (Spec.map (CommRingCat.ofHom (algebraMap baseField middleField))) =
      pullback.fst object.hom
        (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) := by
  exact pullbackTowerProjection _ _ _ (by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]) object

/-- Restriction along the identity field algebra is identity on the underlying scheme. -/
noncomputable def baseChange.restrictionId (baseField : Type u) [Field baseField]
    (parameter : Over (Spec (.of baseField))) :
    parameter ⟶ (Over.map (Spec.map (CommRingCat.ofHom
      (algebraMap baseField baseField)))).obj parameter :=
  Over.homMk (𝟙 parameter.left) (by
    change 𝟙 parameter.left ≫ (parameter.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap baseField baseField))) = parameter.hom
    simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id,
      Category.id_comp, Category.comp_id])

/-- Iterated and direct restriction have the same underlying parameter scheme. -/
noncomputable def baseChange.restrictionComp (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField] [IsScalarTower baseField middleField extensionField]
    (parameter : Over (Spec (.of extensionField))) :
    (Over.map (Spec.map (CommRingCat.ofHom (algebraMap baseField middleField)))).obj
      ((Over.map (Spec.map (CommRingCat.ofHom
        (algebraMap middleField extensionField)))).obj parameter) ⟶
      (Over.map (Spec.map (CommRingCat.ofHom
        (algebraMap baseField extensionField)))).obj parameter :=
  Over.homMk (𝟙 parameter.left) (by
    change 𝟙 parameter.left ≫ (parameter.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))) =
      (parameter.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap middleField extensionField))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap baseField middleField))
    simp only [Category.id_comp, Category.assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

end AlgebraicGeometry
