import Jacobian.Algebra.Category.ModuleCat.FinitePresentation.Colimit
import Jacobian.LinearAlgebra.TensorProduct.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Data.Fintype.Order

/-!
# Descent of module maps and equalities along directed ring colimits

A finitely presented source permits descending a map between scalar extensions.
A finite source suffices to detect equality at a stage. Neither assertion requires
finite presentation of the target. Scalar extension is the native
`ModuleCat.extendScalars` throughout.
-/

set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

universe ringUniverse moduleUniverse sourceUniverse targetUniverse

noncomputable section

open CategoryTheory Limits

open scoped ChangeOfRings

namespace ModuleCat

private theorem lift_finitePresentation
    {coefficientRing : Type ringUniverse} [CommRing coefficientRing] {Tail : Type ringUniverse} [Preorder Tail] [Nonempty Tail]
    [IsDirected Tail (· ≤ ·)] {presentedModule limitModule : Type (max ringUniverse moduleUniverse)}
    [AddCommGroup presentedModule] [Module coefficientRing presentedModule] [Module.FinitePresentation coefficientRing presentedModule]
    [AddCommGroup limitModule] [Module coefficientRing limitModule]
    (stageModule : Tail → Type (max ringUniverse moduleUniverse)) [∀ stageIndex, AddCommGroup (stageModule stageIndex)] [∀ stageIndex, Module coefficientRing (stageModule stageIndex)]
    (transitionMap : ∀ stageIndex laterIndex, stageIndex ≤ laterIndex → stageModule stageIndex →ₗ[coefficientRing] stageModule laterIndex)
    [DirectedSystem stageModule (fun {stageIndex laterIndex} compatibility ↦ transitionMap stageIndex laterIndex compatibility)]
    (coconeMap : ∀ stageIndex, stageModule stageIndex →ₗ[coefficientRing] limitModule)
    (hc : ∀ stageIndex laterIndex compatibility element, coconeMap laterIndex (transitionMap stageIndex laterIndex compatibility element) = coconeMap stageIndex element)
    (hr : ∀ element : limitModule, ∃ stageIndex xj, coconeMap stageIndex xj = element)
    (hz : ∀ stageIndex element, coconeMap stageIndex element = 0 → ∃ laterIndex compatibility, transitionMap stageIndex laterIndex compatibility element = 0)
    (compatibility : presentedModule →ₗ[coefficientRing] limitModule) : ∃ (stageIndex : Tail) (liftedMap : presentedModule →ₗ[coefficientRing] stageModule stageIndex), (coconeMap stageIndex).comp liftedMap = compatibility := by
  classical
  obtain ⟨targetElement, relations, comparison, hK⟩ := Module.FinitePresentation.exists_fin coefficientRing presentedModule
  let presentationMap : (Fin targetElement → coefficientRing) →ₗ[coefficientRing] presentedModule := comparison.symm.toLinearMap.comp relations.mkQ
  let basis := Pi.basisFun coefficientRing (Fin targetElement)
  choose stageIndex element hx using fun basisIndex : Fin targetElement ↦ hr (compatibility (presentationMap (basis basisIndex)))
  obtain ⟨j₀, hj₀⟩ := (Set.finite_range stageIndex).exists_le
  let generatorImage (basisIndex : Fin targetElement) : stageModule j₀ := transitionMap (stageIndex basisIndex) j₀ (hj₀ _ ⟨basisIndex, rfl⟩) (element basisIndex)
  let a₀ := basis.constr coefficientRing generatorImage
  have ha₀ : (coconeMap j₀).comp a₀ = compatibility.comp presentationMap := by
    apply basis.ext
    intro basisIndex
    change coconeMap j₀ (basis.constr coefficientRing generatorImage (basis basisIndex)) = compatibility (presentationMap (basis basisIndex))
    rw [Module.Basis.constr_basis]
    exact (hc _ _ _ _).trans (hx basisIndex)
  obtain ⟨relationsGenerators, hs⟩ := hK
  have hs0 (element : (Fin targetElement → coefficientRing)) (hx : element ∈ relationsGenerators) : coconeMap j₀ (a₀ element) = 0 := by
    have hxK : element ∈ relations := by
      rw [← hs]
      exact Submodule.subset_span hx
    have hpx : presentationMap element = 0 := by simp [presentationMap, hxK]
    exact (LinearMap.congr_fun ha₀ element).trans (by simp [hpx])
  choose laterIndex hk hk0 using fun element : relationsGenerators ↦ hz j₀ (a₀ element) (hs0 element element.property)
  obtain ⟨k₀, hk₀⟩ := (Set.finite_range laterIndex).exists_le
  obtain ⟨commonIndex, hjl, hkl⟩ := exists_ge_ge j₀ k₀
  let a₁ := (transitionMap j₀ commonIndex hjl).comp a₀
  have hkill : relations ≤ LinearMap.ker a₁ := by
    rw [← hs, Submodule.span_le]
    intro element hx
    let relationElement : relationsGenerators := ⟨element, hx⟩
    have hzl : laterIndex relationElement ≤ commonIndex := (hk₀ _ ⟨relationElement, rfl⟩).trans hkl
    change transitionMap j₀ commonIndex hjl (a₀ element) = 0
    rw [← DirectedSystem.map_map (f := fun {stageIndex laterIndex} compatibility ↦ transitionMap stageIndex laterIndex compatibility)
      (hk relationElement) hzl (a₀ element), hk0 relationElement, map_zero]
  let liftedMap : presentedModule →ₗ[coefficientRing] stageModule commonIndex := (relations.liftQ a₁ hkill).comp comparison.toLinearMap
  refine ⟨commonIndex, liftedMap, ?_⟩
  apply LinearMap.ext
  intro element
  obtain ⟨relationElement, hz⟩ := relations.mkQ_surjective (comparison element)
  have hx : presentationMap relationElement = element := by simp [presentationMap, hz]
  rw [← hx]
  change coconeMap commonIndex ((relations.liftQ a₁ hkill) (comparison (presentationMap relationElement))) = compatibility (presentationMap relationElement)
  have hep : comparison (presentationMap relationElement) = relations.mkQ relationElement := by simp [presentationMap]
  rw [hep]
  change coconeMap commonIndex (a₁ relationElement) = compatibility (presentationMap relationElement)
  exact (hc _ _ _ _).trans (LinearMap.congr_fun ha₀ relationElement)

private theorem exists_stage_restricted_hom
    {Index : Type ringUniverse} [Preorder Index] [Nonempty Index] [IsDirected Index (· ≤ ·)]
    (diagram : Index ⥤ CommRingCat) (baseIndex : Index) (sourceModule targetModule : ModuleCat.{max ringUniverse moduleUniverse} (diagram.obj baseIndex))
    [Module.FinitePresentation (diagram.obj baseIndex) sourceModule]
    (compatibility : sourceModule ⟶ (restrictScalars (CommRingCat.Hom.hom (colimit.ι diagram baseIndex))).obj
      ((extendScalars (CommRingCat.Hom.hom (colimit.ι diagram baseIndex))).obj targetModule)) :
    ∃ (stageIndex : Index) (hij : baseIndex ≤ stageIndex),
      let rij := CommRingCat.Hom.hom (diagram.map (homOfLE hij))
      let rj := CommRingCat.Hom.hom (colimit.ι diagram stageIndex)
      let ri := CommRingCat.Hom.hom (colimit.ι diagram baseIndex)
      ∃ (liftedMap : sourceModule ⟶ (restrictScalars rij).obj ((extendScalars rij).obj targetModule)),
        ∀ (comparison : (extendScalars ri).obj targetModule ≅
          (extendScalars rj).obj ((extendScalars rij).obj targetModule)),
          (∀ targetElement : targetModule, comparison.hom ((1 : ↑(colimit diagram : CommRingCat)) ⊗ₜ[diagram.obj baseIndex, ri] targetElement) =
            (1 : ↑(colimit diagram : CommRingCat)) ⊗ₜ[diagram.obj stageIndex, rj]
              ((1 : ↑(diagram.obj stageIndex)) ⊗ₜ[diagram.obj baseIndex, rij] targetElement)) →
          ∀ moduleElement : sourceModule, comparison.hom (compatibility moduleElement) =
            (1 : ↑(colimit diagram : CommRingCat)) ⊗ₜ[diagram.obj stageIndex, rj] (liftedMap moduleElement) := by
  classical
  let baseRing := diagram.obj baseIndex
  let colimitRing := colimit diagram
  let ri := (colimit.ι diagram baseIndex).hom
  let : Algebra baseRing colimitRing := ri.toAlgebra
  let Tail := {stageIndex : Index // baseIndex ≤ stageIndex}
  let : Nonempty Tail := ⟨⟨baseIndex, le_rfl⟩⟩
  let : IsDirectedOrder Tail := ⟨fun stageIndex laterIndex ↦ by
    obtain ⟨commonIndex, hjl, hkl⟩ := exists_ge_ge stageIndex.val laterIndex.val
    exact ⟨⟨commonIndex, stageIndex.property.trans hjl⟩, hjl, hkl⟩⟩
  let stageRing (stageIndex : Tail) : Type ringUniverse := diagram.obj stageIndex.val
  let : ∀ stageIndex, CommRing (stageRing stageIndex) := fun stageIndex ↦ inferInstance
  let : ∀ stageIndex, Algebra baseRing (stageRing stageIndex) := fun stageIndex ↦ (diagram.map (homOfLE stageIndex.property)).hom.toAlgebra
  let stageModule (stageIndex : Tail) := TensorProduct baseRing (stageRing stageIndex) targetModule
  let : ∀ stageIndex, AddCommGroup (stageModule stageIndex) := fun stageIndex ↦ inferInstance
  let : ∀ stageIndex, Module baseRing (stageModule stageIndex) := fun stageIndex ↦ inferInstance
  let transitionAlgebraMap (stageIndex laterIndex : Tail) (hjk : stageIndex ≤ laterIndex) : stageRing stageIndex →ₐ[baseRing] stageRing laterIndex :=
    { (diagram.map (homOfLE hjk)).hom with
      commutes' := fun relationsGenerators ↦ congrArg (fun presentationMap : diagram.obj baseIndex ⟶ diagram.obj laterIndex.val ↦ presentationMap relationsGenerators)
        (diagram.map_comp (homOfLE stageIndex.property) (homOfLE hjk)).symm }
  let transitionMap (stageIndex laterIndex : Tail) (hjk : stageIndex ≤ laterIndex) : stageModule stageIndex →ₗ[baseRing] stageModule laterIndex :=
    (transitionAlgebraMap stageIndex laterIndex hjk).toLinearMap.rTensor targetModule
  let coconeAlgebraMap (stageIndex : Tail) : stageRing stageIndex →ₐ[baseRing] colimitRing :=
    { (colimit.ι diagram stageIndex.val).hom with
      commutes' := fun relationsGenerators ↦ congrArg (fun presentationMap : diagram.obj baseIndex ⟶ colimitRing ↦ presentationMap relationsGenerators)
        (colimit.w diagram (homOfLE stageIndex.property)) }
  let coconeMap (stageIndex : Tail) : stageModule stageIndex →ₗ[baseRing] (TensorProduct baseRing colimitRing targetModule) := (coconeAlgebraMap stageIndex).toLinearMap.rTensor targetModule
  let : DirectedSystem stageModule (fun {stageIndex laterIndex} hjk ↦ transitionMap stageIndex laterIndex hjk) :=
    { map_self := by
        intro stageIndex tensorElement
        induction tensorElement using TensorProduct.induction_on with
        | zero => simp
        | tmul scalar targetElement =>
          dsimp only [transitionMap, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
          change TensorProduct.tmul baseRing (diagram.map (homOfLE (le_refl stageIndex.val)) scalar) targetElement =
            TensorProduct.tmul baseRing scalar targetElement
          simp
        | add tensorElement otherTensorElement ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht'
      map_map := by
        intro commonIndex laterIndex stageIndex hjk hkl tensorElement
        induction tensorElement using TensorProduct.induction_on with
        | zero => simp
        | tmul scalar targetElement =>
          dsimp only [transitionMap, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
          exact congrArg (fun scalar : diagram.obj commonIndex.val ↦ TensorProduct.tmul baseRing scalar targetElement)
            (ConcreteCategory.congr_hom (diagram.map_comp (homOfLE hjk) (homOfLE hkl)) scalar).symm
        | add tensorElement otherTensorElement ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht' }
  have hc (stageIndex laterIndex : Tail) (hjk : stageIndex ≤ laterIndex) (tensorElement : stageModule stageIndex) : coconeMap laterIndex (transitionMap stageIndex laterIndex hjk tensorElement) = coconeMap stageIndex tensorElement := by
    induction tensorElement using TensorProduct.induction_on with
    | zero => simp
    | tmul scalar targetElement =>
      dsimp only [coconeMap, transitionMap, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
      exact congrArg (fun scalar : colimitRing ↦ TensorProduct.tmul baseRing scalar targetElement)
        (ConcreteCategory.congr_hom (colimit.w diagram (homOfLE hjk)) scalar)
    | add tensorElement otherTensorElement ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht'
  have hr (tensorElement : TensorProduct baseRing colimitRing targetModule) : ∃ stageIndex tj, coconeMap stageIndex tj = tensorElement := by
    obtain ⟨stageIndex, hij, tj, htj⟩ :=
      (TensorProduct.directedColimitBaseChangeElementwise diagram baseIndex targetModule).1 tensorElement
    exact ⟨⟨stageIndex, hij⟩, tj, htj⟩
  have hz (stageIndex : Tail) (tensorElement : stageModule stageIndex) (ht : coconeMap stageIndex tensorElement = 0) :
      ∃ (laterIndex : Tail) (hjk : stageIndex ≤ laterIndex), transitionMap stageIndex laterIndex hjk tensorElement = 0 := by
    obtain ⟨laterIndex, hjk, hk⟩ :=
      (TensorProduct.directedColimitBaseChangeElementwise diagram baseIndex targetModule).2 stageIndex.val stageIndex.property tensorElement ht
    exact ⟨⟨laterIndex, stageIndex.property.trans hjk⟩, hjk, hk⟩
  let uncurriedMap : sourceModule →ₗ[baseRing] (TensorProduct baseRing colimitRing targetModule) :=
    { toFun := compatibility
      map_add' := compatibility.hom.map_add
      map_smul' := by
        intro scalar moduleElement
        have hm := compatibility.hom.map_smul scalar moduleElement
        change compatibility (scalar • moduleElement) = ri scalar • (compatibility moduleElement : TensorProduct baseRing colimitRing targetModule) at hm
        change compatibility (scalar • moduleElement) = scalar • (compatibility moduleElement : TensorProduct baseRing colimitRing targetModule)
        have hs (tensorElement : TensorProduct baseRing colimitRing targetModule) : ri scalar • tensorElement = scalar • tensorElement := algebraMap_smul colimitRing scalar tensorElement
        exact hm.trans (hs (compatibility moduleElement)) }
  obtain ⟨stageIndex, liftedMap, ha⟩ := lift_finitePresentation stageModule transitionMap coconeMap hc hr hz uncurriedMap
  refine ⟨stageIndex.val, stageIndex.property, ?_⟩
  dsimp only
  let rij := (diagram.map (homOfLE stageIndex.property)).hom
  let rj := (colimit.ι diagram stageIndex.val).hom
  let liftedMap : sourceModule ⟶ (restrictScalars rij).obj ((extendScalars rij).obj targetModule) :=
    ofHom (X := sourceModule) (Y := (restrictScalars rij).obj ((extendScalars rij).obj targetModule))
      { toFun := liftedMap
        map_add' := liftedMap.map_add
        map_smul' := by
          intro scalar moduleElement
          change liftedMap (scalar • moduleElement) = (algebraMap baseRing (stageRing stageIndex)) scalar • (liftedMap moduleElement : stageModule stageIndex)
          rw [algebraMap_smul]
          exact liftedMap.map_smul scalar moduleElement }
  refine ⟨liftedMap, ?_⟩
  intro comparison he moduleElement
  let : Algebra (stageRing stageIndex) colimitRing := rj.toAlgebra
  have ht (tensorElement : stageModule stageIndex) : comparison.hom (coconeMap stageIndex tensorElement) = (1 : colimitRing) ⊗ₜ[diagram.obj stageIndex.val, rj] tensorElement := by
    induction tensorElement using TensorProduct.induction_on with
    | zero => simp
    | tmul scalar targetElement =>
      change comparison.hom ((rj scalar) ⊗ₜ[diagram.obj baseIndex, ri] targetElement) =
        (1 : colimitRing) ⊗ₜ[diagram.obj stageIndex.val, rj] (scalar ⊗ₜ[diagram.obj baseIndex, rij] targetElement)
      have hin : (rj scalar) ⊗ₜ[diagram.obj baseIndex, ri] targetElement =
          (rj scalar) • ((1 : colimitRing) ⊗ₜ[diagram.obj baseIndex, ri] targetElement) := by
        rw [ExtendScalars.smul_tmul, mul_one]
      rw [hin, comparison.hom.hom.map_smul, he]
      change (rj scalar) • ((1 : colimitRing) ⊗ₜ[diagram.obj stageIndex.val, rj]
        ((1 : stageRing stageIndex) ⊗ₜ[diagram.obj baseIndex, rij] targetElement)) =
        (1 : colimitRing) ⊗ₜ[diagram.obj stageIndex.val, rj] (scalar ⊗ₜ[diagram.obj baseIndex, rij] targetElement)
      change ((rj scalar) * 1) ⊗ₜ[diagram.obj stageIndex.val, rj]
        ((1 : stageRing stageIndex) ⊗ₜ[diagram.obj baseIndex, rij] targetElement) =
        (1 : colimitRing) ⊗ₜ[diagram.obj stageIndex.val, rj] (scalar ⊗ₜ[diagram.obj baseIndex, rij] targetElement)
      rw [mul_one]
      have hn : scalar ⊗ₜ[diagram.obj baseIndex, rij] targetElement =
          scalar • ((1 : stageRing stageIndex) ⊗ₜ[diagram.obj baseIndex, rij] targetElement) := by
        change scalar ⊗ₜ[diagram.obj baseIndex, rij] targetElement = (scalar * 1) ⊗ₜ[diagram.obj baseIndex, rij] targetElement
        rw [mul_one]
      rw [hn, TensorProduct.tmul_smul]
      change rj scalar ⊗ₜ[diagram.obj stageIndex.val, rj] ((1 : stageRing stageIndex) ⊗ₜ[diagram.obj baseIndex, rij] targetElement) =
        (rj scalar * 1) ⊗ₜ[diagram.obj stageIndex.val, rj] ((1 : stageRing stageIndex) ⊗ₜ[diagram.obj baseIndex, rij] targetElement)
      rw [mul_one]
    | add tensorElement otherTensorElement ht ht' =>
      simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) ht ht'
  exact (congrArg (fun tensorElement ↦ comparison.hom tensorElement) (LinearMap.congr_fun ha moduleElement)).symm.trans (ht (liftedMap moduleElement))

private theorem exists_stage_finite_tensor_vanishing
    {Index : Type ringUniverse} [Preorder Index] [Nonempty Index] [IsDirected Index (· ≤ ·)]
    (diagram : Index ⥤ CommRingCat) (baseIndex : Index) (targetModule : ModuleCat (diagram.obj baseIndex)) (elements : Finset targetModule)
    (hs : ∀ insertedElement ∈ elements,
      (1 : ↑(colimit diagram)) ⊗ₜ[diagram.obj baseIndex,CommRingCat.Hom.hom (colimit.ι diagram baseIndex)] insertedElement = 0) :
    ∃ (stageIndex : Index) (hij : baseIndex ≤ stageIndex), ∀ insertedElement ∈ elements,
      (1 : diagram.obj stageIndex) ⊗ₜ[diagram.obj baseIndex,CommRingCat.Hom.hom (diagram.map (homOfLE hij))] insertedElement = 0 := by
  classical
  have push (stageIndex laterIndex : Index) (hij : baseIndex ≤ stageIndex) (hjk : stageIndex ≤ laterIndex) (insertedElement : targetModule)
      (hn : (1 : diagram.obj stageIndex) ⊗ₜ[diagram.obj baseIndex,CommRingCat.Hom.hom (diagram.map (homOfLE hij))] insertedElement = 0) :
      (1 : diagram.obj laterIndex) ⊗ₜ[diagram.obj baseIndex,CommRingCat.Hom.hom
        (diagram.map (homOfLE (hij.trans hjk)))] insertedElement = 0 := by
    let : Algebra (diagram.obj baseIndex) (diagram.obj stageIndex) := (diagram.map (homOfLE hij)).hom.toAlgebra
    let : Algebra (diagram.obj baseIndex) (diagram.obj laterIndex) :=
      (diagram.map (homOfLE (hij.trans hjk))).hom.toAlgebra
    let transitionAlgebraMap : diagram.obj stageIndex →ₐ[diagram.obj baseIndex] diagram.obj laterIndex :=
      { (diagram.map (homOfLE hjk)).hom with
        commutes' := fun element =>
          congrArg (fun coefficientMap : diagram.obj baseIndex ⟶ diagram.obj laterIndex => coefficientMap element)
            (diagram.map_comp (homOfLE hij) (homOfLE hjk)).symm }
    have compatibility := congrArg (LinearMap.rTensor targetModule transitionAlgebraMap.toLinearMap) hn
    simpa only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one, map_zero] using compatibility
  have single (insertedElement : targetModule) (hn :
      (1 : ↑(colimit diagram)) ⊗ₜ[diagram.obj baseIndex,CommRingCat.Hom.hom (colimit.ι diagram baseIndex)] insertedElement = 0) :
      ∃ (stageIndex : Index) (hij : baseIndex ≤ stageIndex),
        (1 : diagram.obj stageIndex) ⊗ₜ[diagram.obj baseIndex,CommRingCat.Hom.hom (diagram.map (homOfLE hij))] insertedElement = 0 := by
    have compatibility := (TensorProduct.directedColimitBaseChangeElementwise diagram baseIndex targetModule).2 baseIndex le_rfl
    obtain ⟨stageIndex, hij, hj⟩ := compatibility
      ((1 : diagram.obj baseIndex) ⊗ₜ[diagram.obj baseIndex,CommRingCat.Hom.hom (diagram.map (homOfLE le_rfl))] insertedElement)
      (by simpa only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] using hn)
    exact ⟨stageIndex, hij, by
      simpa only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] using hj⟩
  induction elements using Finset.induction_on with
  | empty => exact ⟨baseIndex, le_rfl, by simp⟩
  | @insert insertedElement elements hns ih =>
    obtain ⟨stageIndex, hij, hj⟩ := single insertedElement (hs insertedElement (Finset.mem_insert_self insertedElement elements))
    obtain ⟨laterIndex, hik, hk⟩ := ih (fun moduleElement hm => hs moduleElement (Finset.mem_insert_of_mem hm))
    obtain ⟨commonIndex, hjl, hkl⟩ := IsDirected.directed (r := (· ≤ ·)) stageIndex laterIndex
    refine ⟨commonIndex, hij.trans hjl, ?_⟩
    intro moduleElement hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact push stageIndex commonIndex hij hjl moduleElement hj
    · exact push laterIndex commonIndex hik hkl moduleElement (hk moduleElement hm)

private theorem exists_comparison
    {coefficientRing baseRing colimitRing : Type ringUniverse} [CommRing coefficientRing] [CommRing baseRing] [CommRing colimitRing]
    (ri : coefficientRing →+* colimitRing) (rij : coefficientRing →+* baseRing) (rj : baseRing →+* colimitRing)
    (hc : rj.comp rij = ri) (moduleType : ModuleCat.{max ringUniverse moduleUniverse} coefficientRing) :
    ∃ comparison : (extendScalars ri).obj moduleType ≅ (extendScalars rj).obj ((extendScalars rij).obj moduleType),
      ∀ sourceRank : moduleType, comparison.hom ((1 : colimitRing) ⊗ₜ[coefficientRing, ri] sourceRank) =
        (1 : colimitRing) ⊗ₜ[baseRing, rj] ((1 : baseRing) ⊗ₜ[coefficientRing, rij] sourceRank) := by
  subst ri
  exact ⟨(extendScalarsComp rij rj).app moduleType,
    extendScalarsComp_hom_app_one_tmul rij rj moduleType⟩

/-- A map between extended modules descends if its source is finitely presented. -/
theorem exists_hom_at_stage
    {Index : Type ringUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] (diagram : Index ⥤ CommRingCat)
    (baseIndex : Index) (sourceModule targetModule : ModuleCat.{max ringUniverse moduleUniverse} (diagram.obj baseIndex))
    [Module.FinitePresentation (diagram.obj baseIndex) sourceModule]
    (coefficientMap : (extendScalars (colimit.ι diagram baseIndex).hom).obj sourceModule ⟶
      (extendScalars (colimit.ι diagram baseIndex).hom).obj targetModule) :
    ∃ (stageIndex : Index) (hij : baseIndex ≤ stageIndex),
      let rij := (diagram.map (homOfLE hij)).hom
      let rj := (colimit.ι diagram stageIndex).hom
      let ri := (colimit.ι diagram baseIndex).hom
      ∃ (stageMap : (extendScalars rij).obj sourceModule ⟶ (extendScalars rij).obj targetModule)
        (eM : (extendScalars ri).obj sourceModule ≅ (extendScalars rj).obj ((extendScalars rij).obj sourceModule))
        (eN : (extendScalars ri).obj targetModule ≅ (extendScalars rj).obj ((extendScalars rij).obj targetModule)),
        (∀ moduleElement : sourceModule,
          eM.hom ((1 : ↑(colimit diagram : CommRingCat)) ⊗ₜ[diagram.obj baseIndex, ri] moduleElement) =
            (1 : ↑(colimit diagram : CommRingCat)) ⊗ₜ[diagram.obj stageIndex, rj]
              ((1 : ↑(diagram.obj stageIndex)) ⊗ₜ[diagram.obj baseIndex, rij] moduleElement)) ∧
        (∀ targetElement : targetModule,
          eN.hom ((1 : ↑(colimit diagram : CommRingCat)) ⊗ₜ[diagram.obj baseIndex, ri] targetElement) =
            (1 : ↑(colimit diagram : CommRingCat)) ⊗ₜ[diagram.obj stageIndex, rj]
              ((1 : ↑(diagram.obj stageIndex)) ⊗ₜ[diagram.obj baseIndex, rij] targetElement)) ∧
        coefficientMap ≫ eN.hom = eM.hom ≫ (extendScalars rj).map stageMap := by
  classical
  let ri := CommRingCat.Hom.hom (colimit.ι diagram baseIndex)
  let compatibility := (extendRestrictScalarsAdj ri).homEquiv _ _ coefficientMap
  obtain ⟨stageIndex, hij, liftedMap, ha⟩ := exists_stage_restricted_hom diagram baseIndex sourceModule targetModule compatibility
  let rij := CommRingCat.Hom.hom (diagram.map (homOfLE hij))
  let rj := CommRingCat.Hom.hom (colimit.ι diagram stageIndex)
  have hc : rj.comp rij = ri :=
    congrArg CommRingCat.Hom.hom (colimit.w diagram (homOfLE hij))
  obtain ⟨eM, heM⟩ := exists_comparison ri rij rj hc sourceModule
  obtain ⟨eN, heN⟩ := exists_comparison ri rij rj hc targetModule
  let stageMap := ((extendRestrictScalarsAdj rij).homEquiv sourceModule _).symm liftedMap
  have hg : ∀ moduleElement : sourceModule, stageMap ((1 : diagram.obj stageIndex) ⊗ₜ[diagram.obj baseIndex, rij] moduleElement) = liftedMap moduleElement := by
    intro moduleElement
    have hm := congrArg (fun moduleMap => moduleMap moduleElement)
      (((extendRestrictScalarsAdj rij).homEquiv sourceModule _).apply_symm_apply liftedMap)
    exact hm
  refine ⟨stageIndex, hij, stageMap, eM, eN, heM, heN, ?_⟩
  apply ExtendScalars.hom_ext
  intro moduleElement
  change eN.hom (coefficientMap ((1 : ↑(colimit diagram : CommRingCat)) ⊗ₜ[diagram.obj baseIndex, ri] moduleElement)) =
    (extendScalars rj).map stageMap (eM.hom
      ((1 : ↑(colimit diagram : CommRingCat)) ⊗ₜ[diagram.obj baseIndex, ri] moduleElement))
  rw [heM, ExtendScalars.map_tmul, hg]
  exact ha eN heN moduleElement

/-- Equality after scalar extension to the colimit is detected at a stage for a finite source. -/
theorem exists_map_eq_of_map_colimit_eq
    {Index : Type ringUniverse} [Preorder Index] [Nonempty Index]
    [IsDirected Index (· ≤ ·)] (diagram : Index ⥤ CommRingCat)
    (baseIndex : Index) (sourceModule targetModule : ModuleCat.{max ringUniverse moduleUniverse} (diagram.obj baseIndex))
    [Module.Finite (diagram.obj baseIndex) sourceModule]
    (firstMap secondMap : sourceModule ⟶ targetModule)
    (hfg : (extendScalars (colimit.ι diagram baseIndex).hom).map firstMap =
      (extendScalars (colimit.ι diagram baseIndex).hom).map secondMap) :
    ∃ (stageIndex : Index) (hij : baseIndex ≤ stageIndex),
      (extendScalars (diagram.map (homOfLE hij)).hom).map firstMap =
        (extendScalars (diagram.map (homOfLE hij)).hom).map secondMap := by
  classical
  obtain ⟨generators, hs⟩ := Module.Finite.fg_top (R := diagram.obj baseIndex) (M := sourceModule)
  let differences := generators.image (fun moduleElement => firstMap moduleElement - secondMap moduleElement)
  have ht : ∀ targetElement ∈ differences,
      (1 : ↑(colimit diagram)) ⊗ₜ[diagram.obj baseIndex,CommRingCat.Hom.hom (colimit.ι diagram baseIndex)] targetElement = 0 := by
    intro targetElement hn
    obtain ⟨moduleElement, _, rfl⟩ := Finset.mem_image.mp hn
    have hm := congrArg (fun moduleMap => moduleMap
      ((1 : ↑(colimit diagram)) ⊗ₜ[diagram.obj baseIndex,CommRingCat.Hom.hom (colimit.ι diagram baseIndex)] moduleElement)) hfg
    simpa only [ExtendScalars.map_tmul, TensorProduct.tmul_sub, sub_eq_zero] using hm
  obtain ⟨stageIndex, hij, hj⟩ := exists_stage_finite_tensor_vanishing diagram baseIndex targetModule differences ht
  let rij := CommRingCat.Hom.hom (diagram.map (homOfLE hij))
  apply Exists.intro stageIndex
  apply Exists.intro hij
  apply ((extendRestrictScalarsAdj rij).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on hs
  intro moduleElement hm
  have hm' := hj (firstMap moduleElement - secondMap moduleElement) (Finset.mem_image.mpr ⟨moduleElement, hm, rfl⟩)
  change (1 : diagram.obj stageIndex) ⊗ₜ[diagram.obj baseIndex, rij] (firstMap moduleElement) =
    (1 : diagram.obj stageIndex) ⊗ₜ[diagram.obj baseIndex, rij] (secondMap moduleElement)
  simpa only [TensorProduct.tmul_sub, sub_eq_zero] using hm'

end ModuleCat
