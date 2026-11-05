import Jacobian.AlgebraicGeometry.Cohomology.Pullback
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The field-extension comparison on cohomology

For a scheme over a field and a field extension, pullback on cohomology extends
to a linear map from the scalar extension of the original cohomology. The
construction uses the cohomology and field actions of `Cohomology.Basic`.
It does not require quasi-coherence, quasi-compactness or separatedness.
-/

noncomputable section

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {baseField : Type schemeUniverse} [Field baseField]
  (extensionField : Type schemeUniverse) [Field extensionField] [Algebra baseField extensionField]
  {scheme : Scheme.{schemeUniverse}} [scheme.Over (Spec (.of baseField))]

set_option backward.isDefEq.respectTransparency false in
/-- The two scalar homomorphisms on a base-changed scheme agree. -/
lemma globalSectionsRingHom_pullback (scalar : baseField) :
    (pullback.fst (scheme ↘ Spec (.of baseField))
        (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))).appTop
        (globalSectionsRingHom baseField (X := scheme) scalar) =
      globalSectionsRingHom extensionField
        (X := pullback (scheme ↘ Spec (.of baseField))
          (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))
        (algebraMap baseField extensionField scalar) := by
  let structureMap := scheme ↘ Spec (.of baseField)
  let scalarMap := Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))
  have square := congrArg Scheme.Hom.appTop (pullback.condition (f := structureMap) (g := scalarMap))
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at square
  change structureMap.appTop ≫ (pullback.fst structureMap scalarMap).appTop =
    scalarMap.appTop ≫ (pullback.snd structureMap scalarMap).appTop at square
  have naturality := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap baseField extensionField))
  change CommRingCat.ofHom (algebraMap baseField extensionField) ≫
      (Scheme.ΓSpecIso (.of extensionField)).inv =
    (Scheme.ΓSpecIso (.of baseField)).inv ≫ scalarMap.appTop at naturality
  have scalarSquare : (Scheme.ΓSpecIso (.of baseField)).inv ≫ structureMap.appTop ≫
        (pullback.fst structureMap scalarMap).appTop =
      CommRingCat.ofHom (algebraMap baseField extensionField) ≫
        (Scheme.ΓSpecIso (.of extensionField)).inv ≫ (pullback.snd structureMap scalarMap).appTop := by
    rw [square, ← Category.assoc, ← naturality, Category.assoc]
  exact ConcreteCategory.congr_hom scalarSquare scalar

namespace Modules

set_option backward.isDefEq.respectTransparency false in
/-- The canonical field-extension comparison on the existing sheaf cohomology.
It sends `scalar ⊗ cohomologyClass` to `scalar` times the pulled-back class. -/
def H.baseChange (moduleSheaf : scheme.Modules) (degree : ℕ) :
    TensorProduct baseField extensionField (moduleSheaf.H degree) →ₗ[extensionField]
      ((Modules.pullback (Limits.pullback.fst (scheme ↘ Spec (.of baseField))
        (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))).obj moduleSheaf).H
        degree := by
  let projection := Limits.pullback.fst (scheme ↘ Spec (.of baseField))
    (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))
  let pulledSheaf := (Modules.pullback projection).obj moduleSheaf
  letI : Module baseField (pulledSheaf.H degree) :=
    Module.compHom (pulledSheaf.H degree) (algebraMap baseField extensionField)
  letI : IsScalarTower baseField extensionField (pulledSheaf.H degree) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let comparison : moduleSheaf.H degree →ₗ[baseField] pulledSheaf.H degree :=
    { toFun := H.pullback projection moduleSheaf degree
      map_add' := map_add _
      map_smul' := fun scalar cohomologyClass ↦ by
        change H.pullback projection moduleSheaf degree
            (globalSectionsRingHom baseField (X := scheme) scalar • cohomologyClass) =
          globalSectionsRingHom extensionField
              (X := Limits.pullback (scheme ↘ Spec (.of baseField))
                (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))
              (algebraMap baseField extensionField scalar) •
            H.pullback projection moduleSheaf degree cohomologyClass
        calc
          _ = projection.appTop (globalSectionsRingHom baseField (X := scheme) scalar) •
              H.pullback projection moduleSheaf degree cohomologyClass :=
            (H.pullback projection moduleSheaf degree).map_smul'
              (globalSectionsRingHom baseField (X := scheme) scalar) cohomologyClass
          _ = _ := by rw [globalSectionsRingHom_pullback extensionField scalar] }
  exact TensorProduct.AlgebraTensorModule.lift
    { toFun := fun scalar ↦ scalar • comparison
      map_add' := fun _ _ ↦ add_smul _ _ _
      map_smul' := fun _ _ ↦ mul_smul _ _ _ }

@[simp]
lemma H.baseChange_tmul (moduleSheaf : scheme.Modules) (degree : ℕ)
    (scalar : extensionField) (cohomologyClass : moduleSheaf.H degree) :
    H.baseChange (baseField := baseField) extensionField moduleSheaf degree
        (scalar ⊗ₜ[baseField] cohomologyClass) =
      scalar • H.pullback (Limits.pullback.fst (scheme ↘ Spec (.of baseField))
        (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))
        moduleSheaf degree cohomologyClass :=
  rfl

/-- Bijectivity of the canonical comparison gives invariance of the cohomology
dimension under the field extension. -/
theorem finrankH_pullback_of_bijective (moduleSheaf : scheme.Modules) (degree : ℕ)
    (bijective : Function.Bijective
      (H.baseChange (baseField := baseField) extensionField moduleSheaf degree)) :
    ((Modules.pullback (Limits.pullback.fst (scheme ↘ Spec (.of baseField))
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))).obj
        moduleSheaf).finrankH extensionField degree =
      moduleSheaf.finrankH baseField degree := by
  exact (LinearEquiv.ofBijective
    (H.baseChange (baseField := baseField) extensionField moduleSheaf degree)
      bijective).finrank_eq.symm.trans
      Module.finrank_baseChange

/-- Bijectivity of the canonical comparisons in every degree gives invariance
of the Euler characteristic under the field extension. -/
theorem eulerChar_pullback_of_bijective (moduleSheaf : scheme.Modules)
    (bijective : ∀ degree, Function.Bijective
      (H.baseChange (baseField := baseField) extensionField moduleSheaf degree)) :
    ((Modules.pullback (Limits.pullback.fst (scheme ↘ Spec (.of baseField))
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField))))).obj
        moduleSheaf).eulerChar extensionField =
      moduleSheaf.eulerChar baseField := by
  unfold eulerChar
  apply finsum_congr
  intro degree
  rw [finrankH_pullback_of_bijective (baseField := baseField)
    extensionField moduleSheaf degree (bijective degree)]

end Modules

end AlgebraicGeometry.Scheme
