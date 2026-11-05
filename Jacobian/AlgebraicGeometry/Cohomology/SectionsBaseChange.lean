import Jacobian.AlgebraicGeometry.Cohomology.BaseChange
import Jacobian.AlgebraicGeometry.Modules.PullbackSections

/-!
# Canonical cohomology base change on global sections

In degree zero, cohomological pullback is the adjunction unit on module sections.
The canonical scalar-extension map therefore sends a pure tensor to the scalar
multiple of its pulled-back section. This compatibility is useful for pencils
of sections after field extension.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Abelian TopologicalSpace Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

private theorem constant_adjunct_pullback
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (f : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ F) :
    (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ _ ((abelianInverseImageConstantIso g).inv ≫ (abelianInverseImage g).map f) =
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ _ f ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
        F).hom.app (op ⊤) ≫
      ((abelianInverseImage g).obj F).obj.map (homOfLE (by simp : ⊤ ≤ g ⁻¹ᵁ ⊤)).op := by
  let a := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop
  let b := (Opens.map g.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let e := (Opens.map g.base).sheafPushforwardContinuousCompSheafSectionsObjIso
    AddCommGrpCat.{u} (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y) (op ⊤)
  let c := (a.comp b).ofNatIsoRight e
  let d := constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    isTerminalTop
  have hc : d.homEquiv _ _ ((abelianInverseImageConstantIso g).inv ≫ (abelianInverseImage g).map f) =
      c.homEquiv _ _ ((abelianInverseImage g).map f) := by
    change d.homEquiv _ _ ((c.leftAdjointUniq d).inv.app _ ≫ (abelianInverseImage g).map f) = _
    rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
    rfl
  rw [hc]
  change c.homEquiv _ _ ((abelianInverseImage g).map f) = _
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change a.homEquiv _ _ (b.homEquiv _ _ ((abelianInverseImage g).map f)) ≫
    e.hom.app ((abelianInverseImage g).obj F) = _
  dsimp only [abelianInverseImage]
  rw [Adjunction.homEquiv_unit b, b.unit_naturality f,
    Adjunction.homEquiv_naturality_right]
  change a.homEquiv _ _ f ≫
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
      F).hom.app (op ⊤) ≫ 𝟙 _ =
    a.homEquiv _ _ f ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
        F).hom.app (op ⊤) ≫ ((abelianInverseImage g).obj F).obj.map (𝟙 (op ⊤))
  exact congrArg (fun m ↦ a.homEquiv _ _ f ≫
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
      F).hom.app (op ⊤) ≫ m) (((abelianInverseImage g).obj F).obj.map_id (op ⊤)).symm


private theorem ext_zero_sections
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (x : Sheaf.H F 0) :
    Sheaf.H.equiv₀ ((abelianInverseImage g).obj F) isTerminalTop
        (Sheaf.H.mapFunctor (abelianInverseImage g) (abelianInverseImageConstantIso g).symm F 0 x) =
      ((abelianInverseImage g).obj F).obj.map (homOfLE (by simp : ⊤ ≤ g ⁻¹ᵁ ⊤)).op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
          F).hom.app (op ⊤) (Sheaf.H.equiv₀ F isTerminalTop x)) := by
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ F).surjective x
  simp only [Sheaf.H.mapFunctor_apply, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀]
  have hf : Ext.addEquiv₀ (Ext.mk₀ f) = f := Ext.addEquiv₀.apply_symm_apply f
  have hf' : Ext.addEquiv₀ (Ext.mk₀ ((abelianInverseImageConstantIso g).inv ≫ (abelianInverseImage g).map f)) =
      (abelianInverseImageConstantIso g).inv ≫ (abelianInverseImage g).map f := Ext.addEquiv₀.apply_symm_apply _
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    Iso.symm_hom, hf, hf']
  have h := congrArg (((abelianInverseImage g).obj F).obj.obj (op ⊤)).uliftZMultiplesAddEquiv
    (constant_adjunct_pullback g F f)
  refine h.trans ?_
  rfl

/-- The map on zeroth cohomology induced by an adjoint coefficient map is
its actual action on global sections, restricted to the top open. -/
theorem H.mapOfAdjunction_zeroLinearEquiv {source target : Scheme.{u}}
    (morphism : source ⟶ target) (sourceModule : target.Modules) (targetModule : source.Modules)
    (coefficientMap : sourceModule ⟶ (pushforward morphism).obj targetModule)
    (cohomologyClass : sourceModule.H 0) :
    H.zeroLinearEquiv targetModule
        (H.mapOfAdjunction morphism coefficientMap 0 cohomologyClass) =
      targetModule.presheaf.map (homOfLE (by simp : ⊤ ≤ morphism ⁻¹ᵁ ⊤)).op
        (coefficientMap.app ⊤ (H.zeroLinearEquiv sourceModule cohomologyClass)) := by
  change Sheaf.H.equiv₀ ((SheafOfModules.toSheaf source.ringCatSheaf).obj targetModule)
      isTerminalTop
      (Sheaf.H.map (adjointCoefficientMap morphism coefficientMap) 0
        (Sheaf.H.mapFunctor (abelianInverseImage morphism)
          (abelianInverseImageConstantIso morphism).symm
          ((SheafOfModules.toSheaf target.ringCatSheaf).obj sourceModule) 0 cohomologyClass)) = _
  rw [← Sheaf.H.equiv₀_naturality, ext_zero_sections]
  let adjunction := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} morphism.base
  let sourceSheaf := (SheafOfModules.toSheaf target.ringCatSheaf).obj sourceModule
  let sectionValue := (adjunction.unit.app sourceSheaf).hom.app (op ⊤)
    (H.zeroLinearEquiv sourceModule cohomologyClass)
  have naturality := ConcreteCategory.congr_hom
    ((adjointCoefficientMap morphism coefficientMap).hom.naturality
      (homOfLE (by simp : ⊤ ≤ morphism ⁻¹ᵁ ⊤)).op) sectionValue
  refine naturality.trans ?_
  have transpose := (adjunction.homEquiv sourceSheaf
    ((SheafOfModules.toSheaf source.ringCatSheaf).obj targetModule)).apply_symm_apply
    ((SheafOfModules.toSheaf target.ringCatSheaf).map coefficientMap)
  rw [Adjunction.homEquiv_unit] at transpose
  have evaluated := congrArg
    (fun moduleMap ↦ moduleMap.hom.app (op ⊤) (H.zeroLinearEquiv sourceModule cohomologyClass))
    transpose
  change (adjointCoefficientMap morphism coefficientMap).hom.app (op (morphism ⁻¹ᵁ ⊤))
      sectionValue = coefficientMap.app ⊤ (H.zeroLinearEquiv sourceModule cohomologyClass)
    at evaluated
  exact congrArg
    (targetModule.presheaf.map (homOfLE (by simp : ⊤ ≤ morphism ⁻¹ᵁ ⊤)).op) evaluated

/-- Cohomological pullback in degree zero is actual pullback of sections. -/
theorem H.pullback_zeroLinearEquiv {source target : Scheme.{u}}
    (morphism : source ⟶ target) (moduleSheaf : target.Modules)
    (cohomologyClass : moduleSheaf.H 0) :
    H.zeroLinearEquiv ((Modules.pullback morphism).obj moduleSheaf)
        (H.pullback morphism moduleSheaf 0 cohomologyClass) =
      ((Modules.pullback morphism).obj moduleSheaf).presheaf.map
        (homOfLE (by simp : ⊤ ≤ morphism ⁻¹ᵁ ⊤)).op
        (pullbackSection morphism (H.zeroLinearEquiv moduleSheaf cohomologyClass)) := by
  exact H.mapOfAdjunction_zeroLinearEquiv morphism moduleSheaf _
    ((pullbackPushforwardAdjunction morphism).unit.app moduleSheaf) cohomologyClass

/-- The canonical field-extension comparison sends a pure tensor in degree zero
to the corresponding scalar multiple of the pulled-back global section. -/
theorem H.baseChange_tmul_zeroLinearEquiv {baseField extensionField : Type u}
    [Field baseField] [Field extensionField] [Algebra baseField extensionField]
    {source : Scheme.{u}} [source.Over (Spec (.of baseField))]
    (moduleSheaf : source.Modules) (scalar : extensionField)
    (cohomologyClass : moduleSheaf.H 0) :
    let projection := Limits.pullback.fst (source ↘ Spec (.of baseField))
      (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))
    let pulledModule := (Modules.pullback projection).obj moduleSheaf
    H.zeroLinearEquiv pulledModule
        (H.baseChange extensionField moduleSheaf 0 (scalar ⊗ₜ[baseField] cohomologyClass)) =
      globalSectionsRingHom extensionField
          (X := Limits.pullback (source ↘ Spec (.of baseField))
            (Spec.map (CommRingCat.ofHom (algebraMap baseField extensionField)))) scalar •
        pulledModule.presheaf.map (homOfLE (by simp : ⊤ ≤ projection ⁻¹ᵁ ⊤)).op
          (pullbackSection projection (H.zeroLinearEquiv moduleSheaf cohomologyClass)) := by
  dsimp only
  rw [H.baseChange_tmul]
  rw [smul_H_eq_globalSectionsRingHom_smul]
  exact ((H.zeroLinearEquiv _).map_smul _ _).trans
    (congrArg (fun sectionValue ↦ globalSectionsRingHom extensionField scalar • sectionValue)
      (H.pullback_zeroLinearEquiv _ moduleSheaf cohomologyClass))

end AlgebraicGeometry.Scheme.Modules
