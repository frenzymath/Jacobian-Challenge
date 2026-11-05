import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Finitely presented modules over directed ring colimits

Finite generators and their finitely many relations descend to one stage.
Scalar extension identifies the resulting presentation cokernel with the
original module, including presentations with no generators or relations.
-/

set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

universe ringUniverse moduleUniverse sourceUniverse targetUniverse

noncomputable section

open CategoryTheory Limits

open scoped ChangeOfRings

namespace ModuleCat

private theorem exists_stage_finite_relation_matrix
    {Index : Type ringUniverse} [Preorder Index] [Nonempty Index] [IsDirected Index (· ≤ ·)]
    (diagram : Index ⥤ CommRingCat) (targetRank sourceRank : ℕ)
    (relationMap : (Fin sourceRank → (colimit diagram : CommRingCat)) →ₗ[(colimit diagram : CommRingCat)]
      (Fin targetRank → (colimit diagram : CommRingCat))) :
    ∃ (representativeIndex : Index) (stageRelationMap : (Fin sourceRank → diagram.obj representativeIndex) →ₗ[diagram.obj representativeIndex] (Fin targetRank → diagram.obj representativeIndex)),
      ∀ (targetIndex : Fin targetRank) (sourceIndex : Fin sourceRank),
        (colimit.ι diagram representativeIndex).hom (stageRelationMap (Pi.single sourceIndex 1) targetIndex) = relationMap (Pi.single sourceIndex 1) targetIndex := by
  classical
  have reps (entryIndex : Fin targetRank × Fin sourceRank) :=
    Concrete.colimit_exists_rep diagram (relationMap (Pi.single entryIndex.2 1) entryIndex.1)
  choose representativeIndex representative ha using reps
  obtain ⟨targetIndex, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image representativeIndex)
  let comparisonMap (entryIndex : Fin targetRank × Fin sourceRank) : representativeIndex entryIndex ⟶ targetIndex :=
    (hj (Finset.mem_image_of_mem representativeIndex (Finset.mem_univ entryIndex))).some
  let entry (entryIndex : Fin targetRank × Fin sourceRank) : diagram.obj targetIndex := diagram.map (comparisonMap entryIndex) (representative entryIndex)
  have hb (entryIndex : Fin targetRank × Fin sourceRank) :
      (colimit.ι diagram targetIndex).hom (entry entryIndex) = relationMap (Pi.single entryIndex.2 1) entryIndex.1 := by
    exact (ConcreteCategory.congr_hom (colimit.w diagram (comparisonMap entryIndex)) (representative entryIndex)).trans (ha entryIndex)
  refine ⟨targetIndex, Matrix.toLin' (fun rowIndex columnIndex ↦ entry (rowIndex, columnIndex)), ?_⟩
  intro rowIndex columnIndex
  simpa only [Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply] using
    hb (rowIndex, columnIndex)

private theorem finite_relation_quotient_comparison
    {Index : Type ringUniverse} [Preorder Index] [Nonempty Index] [IsDirected Index (· ≤ ·)]
    (diagram : Index ⥤ CommRingCat) (targetRank sourceRank : ℕ)
    (relationMap : (Fin sourceRank → (colimit diagram : CommRingCat)) →ₗ[(colimit diagram : CommRingCat)]
      (Fin targetRank → (colimit diagram : CommRingCat)))
    (baseIndex : Index) (stageRelationMap : (Fin sourceRank → diagram.obj baseIndex) →ₗ[diagram.obj baseIndex] (Fin targetRank → diagram.obj baseIndex))
    (hcoeff : ∀ (targetIndex : Fin targetRank) (sourceIndex : Fin sourceRank),
      (colimit.ι diagram baseIndex).hom (stageRelationMap (Pi.single sourceIndex 1) targetIndex) = relationMap (Pi.single sourceIndex 1) targetIndex) :
    Nonempty ((extendScalars (CommRingCat.Hom.hom (colimit.ι diagram baseIndex))).obj
        (ModuleCat.of (diagram.obj baseIndex) (ULift.{moduleUniverse} ((Fin targetRank → diagram.obj baseIndex) ⧸ LinearMap.range stageRelationMap))) ≅
        ModuleCat.of (colimit diagram : CommRingCat)
          (ULift.{moduleUniverse} ((Fin targetRank → (colimit diagram : CommRingCat)) ⧸ LinearMap.range relationMap))) := by
  classical
  let baseRing := diagram.obj baseIndex
  let extensionRing := (colimit diagram : CommRingCat)
  let scalarMap : baseRing →+* extensionRing := (colimit.ι diagram baseIndex).hom
  let := scalarMap.toAlgebra
  let targetFreeComparison := TensorProduct.piScalarRight baseRing extensionRing extensionRing (Fin targetRank)
  let sourceFreeComparison := TensorProduct.piScalarRight baseRing extensionRing extensionRing (Fin sourceRank)
  have hcoord (element : Fin sourceRank → baseRing) (targetIndex : Fin targetRank) :
      scalarMap (stageRelationMap element targetIndex) = relationMap (fun sourceIndex ↦ scalarMap (element sourceIndex)) targetIndex := by
    have hx : element = ∑ sourceIndex : Fin sourceRank, element sourceIndex • Pi.single sourceIndex (1 : baseRing) := by
      ext sourceIndex
      simp [Pi.single_apply]
    have hy : (fun sourceIndex ↦ scalarMap (element sourceIndex)) = ∑ sourceIndex : Fin sourceRank, scalarMap (element sourceIndex) • Pi.single sourceIndex (1 : extensionRing) := by
      ext sourceIndex
      simp [Pi.single_apply]
    have hqi : stageRelationMap element = ∑ sourceIndex : Fin sourceRank, element sourceIndex • stageRelationMap (Pi.single sourceIndex 1) := by
      conv_lhs => rw [hx]
      simp only [map_sum, map_smul]
    rw [hqi, hy]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
      LinearMap.map_smul]
    apply Finset.sum_congr rfl
    intro sourceIndex _
    rw [show scalarMap (stageRelationMap (Pi.single sourceIndex 1) targetIndex) = relationMap (Pi.single sourceIndex 1) targetIndex from hcoeff targetIndex sourceIndex]
  have hmatrix : targetFreeComparison.toLinearMap ∘ₗ stageRelationMap.baseChange extensionRing = relationMap ∘ₗ sourceFreeComparison.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro scalar element
    ext targetIndex
    change targetFreeComparison (scalar ⊗ₜ[baseRing] stageRelationMap element) targetIndex = relationMap (sourceFreeComparison (scalar ⊗ₜ[baseRing] element)) targetIndex
    simp only [targetFreeComparison, sourceFreeComparison, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
    change scalarMap (stageRelationMap element targetIndex) * scalar = relationMap (fun sourceIndex ↦ scalarMap (element sourceIndex) * scalar) targetIndex
    have hy : (fun sourceIndex ↦ scalarMap (element sourceIndex) * scalar) = scalar • (fun sourceIndex ↦ scalarMap (element sourceIndex)) := by
      ext sourceIndex
      simp [mul_comm]
    rw [hy, map_smul, Pi.smul_apply, smul_eq_mul, hcoord]
    exact mul_comm _ _
  have hrange : LinearMap.range (stageRelationMap.baseChange extensionRing) =
      LinearMap.range ((LinearMap.range stageRelationMap).subtype.baseChange extensionRing) := by
    have hf : stageRelationMap = (LinearMap.range stageRelationMap).subtype ∘ₗ stageRelationMap.rangeRestrict := rfl
    nth_rewrite 1 [hf]
    rw [LinearMap.baseChange_comp]
    apply LinearMap.range_comp_of_range_eq_top
    apply LinearMap.range_eq_top.mpr
    exact LinearMap.baseChange_surjective extensionRing stageRelationMap.surjective_rangeRestrict
  have hmap : (LinearMap.range ((LinearMap.range stageRelationMap).subtype.baseChange extensionRing)).map
      targetFreeComparison.toLinearMap = LinearMap.range relationMap := by
    rw [← hrange, ← LinearMap.range_comp, hmatrix]
    exact LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr sourceFreeComparison.surjective)
  let quotientTensorComparison := TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (R := baseRing) extensionRing baseRing extensionRing
    (LinearMap.range stageRelationMap)
  let quotientComparison := Submodule.Quotient.equiv _ _ targetFreeComparison hmap
  let liftComparison := (ULift.moduleEquiv : ULift.{moduleUniverse} ((Fin targetRank → baseRing) ⧸ LinearMap.range stageRelationMap) ≃ₗ[baseRing]
    ((Fin targetRank → baseRing) ⧸ LinearMap.range stageRelationMap)).baseChange baseRing extensionRing _ _
  let comparison := liftComparison.trans (quotientTensorComparison.trans (quotientComparison.trans ULift.moduleEquiv.symm))
  exact ⟨comparison.toModuleIso⟩

private theorem exists_stage_finite_relation_cokernel
    {Index : Type ringUniverse} [Preorder Index] [Nonempty Index] [IsDirected Index (· ≤ ·)]
    (diagram : Index ⥤ CommRingCat) (targetRank sourceRank : ℕ)
    (relationMap : (Fin sourceRank → (colimit diagram : CommRingCat)) →ₗ[(colimit diagram : CommRingCat)]
      (Fin targetRank → (colimit diagram : CommRingCat))) :
    ∃ (baseIndex : Index) (stageRelationMap : (Fin sourceRank → diagram.obj baseIndex) →ₗ[diagram.obj baseIndex] (Fin targetRank → diagram.obj baseIndex)),
      Nonempty ((extendScalars (CommRingCat.Hom.hom (colimit.ι diagram baseIndex))).obj
        (ModuleCat.of (diagram.obj baseIndex) (ULift.{moduleUniverse} ((Fin targetRank → diagram.obj baseIndex) ⧸ LinearMap.range stageRelationMap))) ≅
        ModuleCat.of (colimit diagram : CommRingCat)
          (ULift.{moduleUniverse} ((Fin targetRank → (colimit diagram : CommRingCat)) ⧸ LinearMap.range relationMap))) := by
  obtain ⟨baseIndex, stageRelationMap, hqi⟩ := exists_stage_finite_relation_matrix diagram targetRank sourceRank relationMap
  exact ⟨baseIndex, stageRelationMap, finite_relation_quotient_comparison diagram targetRank sourceRank relationMap baseIndex stageRelationMap hqi⟩

/-- A finitely presented module over a directed ring colimit is extended from a stage. -/
theorem exists_finitePresentation_model
    {Index : Type ringUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] (diagram : Index ⥤ CommRingCat)
    (coefficientModule : ModuleCat.{max ringUniverse moduleUniverse} (colimit diagram : CommRingCat))
    [Module.FinitePresentation (colimit diagram : CommRingCat) coefficientModule] :
    ∃ (baseIndex : Index) (stageModule : ModuleCat.{max ringUniverse moduleUniverse} (diagram.obj baseIndex)),
      Module.FinitePresentation (diagram.obj baseIndex) stageModule ∧
      Nonempty ((extendScalars (colimit.ι diagram baseIndex).hom).obj stageModule ≅ coefficientModule) := by
  classical
  obtain ⟨targetRank, sourceRank, presentationMap, relationMap, hp, hqp⟩ :=
    Module.FinitePresentation.exists_fin' (colimit diagram : CommRingCat) coefficientModule
  obtain ⟨baseIndex, stageRelationMap, ⟨comparison⟩⟩ := exists_stage_finite_relation_cokernel diagram targetRank sourceRank relationMap
  let quotientModule := (Fin targetRank → diagram.obj baseIndex) ⧸ LinearMap.range stageRelationMap
  let stageModule := ModuleCat.of (diagram.obj baseIndex) (ULift.{moduleUniverse} quotientModule)
  have hQ : Module.FinitePresentation (diagram.obj baseIndex) quotientModule :=
    Module.finitePresentation_of_surjective (LinearMap.range stageRelationMap).mkQ
      (Submodule.mkQ_surjective _) (by
        rw [Submodule.ker_mkQ]
        exact Submodule.fg_range stageRelationMap)
  let instQ : Module.FinitePresentation (diagram.obj baseIndex) quotientModule := hQ
  have hM : Module.FinitePresentation (diagram.obj baseIndex) stageModule :=
    Module.FinitePresentation.of_equiv
      (ULift.moduleEquiv : ULift.{moduleUniverse} quotientModule ≃ₗ[diagram.obj baseIndex] quotientModule).symm
  let eN : ModuleCat.of (colimit diagram : CommRingCat)
      (ULift.{moduleUniverse} ((Fin targetRank → (colimit diagram : CommRingCat)) ⧸ LinearMap.range relationMap)) ≅ coefficientModule :=
    ((ULift.moduleEquiv :
      ULift.{moduleUniverse} ((Fin targetRank → (colimit diagram : CommRingCat)) ⧸ LinearMap.range relationMap) ≃ₗ[_]
        ((Fin targetRank → (colimit diagram : CommRingCat)) ⧸ LinearMap.range relationMap)).trans
      ((Submodule.quotEquivOfEq (LinearMap.range relationMap) (LinearMap.ker presentationMap)
        (LinearMap.exact_iff.mp hqp).symm).trans
        (LinearMap.quotKerEquivOfSurjective presentationMap hp))).toModuleIso
  exact ⟨baseIndex, stageModule, hM, ⟨comparison.trans eN⟩⟩

end ModuleCat
