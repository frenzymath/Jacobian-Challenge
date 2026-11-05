import Jacobian.AlgebraicGeometry.Modules.TensorInvertible
import Jacobian.CategoryTheory.Sites.LocallyBijective

/-!
# Duals of invertible module sheaves

The dual of a module sheaf is its internal hom into the structure sheaf. For
a locally free module sheaf of rank one, evaluation against the dual is an
isomorphism. Thus the dual is an invertible module sheaf and a tensor inverse.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{schemeUniverse}}

/-- The sheaf of module homomorphisms between two module sheaves. -/
abbrev homObj (moduleSheaf targetSheaf : scheme.Modules) : scheme.Modules :=
  SheafOfModules.homObj (R := scheme.sheaf) moduleSheaf targetSheaf

/-- The dual module sheaf is the internal hom into the structure sheaf. -/
abbrev dual (moduleSheaf : scheme.Modules) : scheme.Modules :=
  homObj moduleSheaf (SheafOfModules.unit _)

@[inherit_doc] scoped postfix:max "ᵛ" => AlgebraicGeometry.Scheme.Modules.dual

/-- Transposition of a module-sheaf morphism induces a morphism of duals. -/
abbrev dualMap {moduleSheaf targetSheaf : scheme.Modules} (morphism : moduleSheaf ⟶ targetSheaf) :
    targetSheafᵛ ⟶ moduleSheafᵛ :=
  SheafOfModules.homObjMap (R := scheme.sheaf) morphism (𝟙 _)

variable (scheme) in
/-- Dualization as a contravariant functor on module sheaves. -/
abbrev dualFunctor : scheme.Modulesᵒᵖ ⥤ scheme.Modules :=
  (SheafOfModules.homFunctor scheme.sheaf).flip.obj (SheafOfModules.unit _)

/-- Evaluation of the underlying presheaf against its internal-hom dual. -/
abbrev presheafDualEvaluation (moduleSheaf : scheme.Modules) :
    (moduleSheaf.val ⊗ moduleSheafᵛ.val :
      _root_.PresheafOfModules.{schemeUniverse} (scheme.sheaf.obj ⋙ forget₂ _ _)) ⟶
      (SheafOfModules.unit scheme.ringCatSheaf).val :=
  _root_.PresheafOfModules.tensorHomUncurry (R := scheme.sheaf.obj) (𝟙 _)

/-- The evaluation morphism of a module sheaf against its dual. -/
def dualEvaluation (moduleSheaf : scheme.Modules) :
    moduleSheaf ⊗ moduleSheafᵛ ⟶ 𝟙_ scheme.Modules :=
  (SheafOfModules.tensorObjIsoSheafification (R := scheme.sheaf)
      moduleSheaf moduleSheafᵛ).hom ≫
    (_root_.PresheafOfModules.sheafification (𝟙 scheme.ringCatSheaf.obj)).map
      (presheafDualEvaluation moduleSheaf) ≫
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 scheme.ringCatSheaf.obj)).counit.app
      (𝟙_ scheme.Modules)

open Opposite in
/-- Evaluation is bijective on sections over any open inside a rank-one trivialization. -/
lemma presheafDualEvaluation_app_bijective {moduleSheaf : scheme.Modules}
    {openSubset smallerOpen : scheme.Opens} (inclusion : smallerOpen ⟶ openSubset)
    (trivialization : moduleSheaf.over openSubset ≅
      SheafOfModules.unit (scheme.ringCatSheaf.over openSubset)) :
    Function.Bijective ((presheafDualEvaluation moduleSheaf).app (op smallerOpen)) := by
  refine _root_.PresheafOfModules.tensorHomUncurry_id_app_bijective (M := moduleSheaf.val)
    (trivialization.inv.val.app (op (Over.mk inclusion))
      (1 : scheme.sheaf.obj.obj (op smallerOpen)))
    { app object := trivialization.hom.val.app (op (Over.mk (object.unop.hom ≫ inclusion)))
      naturality {firstObject secondObject} morphism := trivialization.hom.val.naturality
        (Over.homMk morphism.unop.left (Subsingleton.elim _ _) :
          Over.mk (secondObject.unop.hom ≫ inclusion) ⟶
            Over.mk (firstObject.unop.hom ≫ inclusion)).op }
    (congrArg (fun morphism ↦ morphism.val.app (op (Over.mk inclusion))
      (1 : scheme.sheaf.obj.obj (op smallerOpen))) trivialization.inv_hom_id)
    fun object element ↦
      ⟨trivialization.hom.val.app (op (Over.mk (object.hom ≫ inclusion))) element, ?_⟩
  have naturality := _root_.PresheafOfModules.naturality_apply trivialization.inv.val
    (Over.homMk object.hom (Subsingleton.elim _ _) :
      Over.mk (object.hom ≫ inclusion) ⟶ Over.mk inclusion).op
    (1 : scheme.sheaf.obj.obj (op smallerOpen))
  refine (congrArg (fun morphism ↦ morphism.val.app
    (op (Over.mk (object.hom ≫ inclusion))) element) trivialization.hom_inv_id).symm.trans ?_
  refine (congrArg (trivialization.inv.val.app (op (Over.mk (object.hom ≫ inclusion))))
    (@mul_one (scheme.sheaf.obj.obj (op object.left)) _
      (trivialization.hom.val.app (op (Over.mk (object.hom ≫ inclusion))) element))).symm.trans ?_
  refine ((trivialization.inv.val.app (op (Over.mk (object.hom ≫ inclusion)))).hom.map_smul _
    (1 : scheme.sheaf.obj.obj (op object.left))).trans ?_
  congr 1
  exact (congrArg (trivialization.inv.val.app (op (Over.mk (object.hom ≫ inclusion))))
    (_root_.PresheafOfModules.unit_map_one (R := scheme.ringCatSheaf.obj) object.hom.op).symm).trans
      naturality

/-- Evaluation against the dual of an invertible module sheaf is an isomorphism. -/
instance isIso_dualEvaluation (moduleSheaf : scheme.Modules)
    [invertible : moduleSheaf.IsInvertible] : IsIso (dualEvaluation moduleSheaf) := by
  obtain ⟨indices, cover, coversTop, trivializations⟩ :=
    (SheafOfModules.isInvertible_iff_exists_over_unit.{schemeUniverse, schemeUniverse,
      schemeUniverse}).mp invertible
  have locallyBijective : (Opens.grothendieckTopology scheme).W.inverseImage
      (_root_.PresheafOfModules.toPresheaf scheme.ringCatSheaf.obj)
        (presheafDualEvaluation moduleSheaf) :=
    (GrothendieckTopology.W_iff_isLocallyBijective _ _).2
      ⟨Presheaf.isLocallyInjective_of_coversTop coversTop _ fun _ index inclusion ↦
        (presheafDualEvaluation_app_bijective inclusion (trivializations index).some).1,
      Presheaf.isLocallySurjective_of_coversTop coversTop _ fun _ index inclusion ↦
        (presheafDualEvaluation_app_bijective inclusion (trivializations index).some).2⟩
  rw [_root_.PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 scheme.ringCatSheaf.obj)] at locallyBijective
  have evaluationIso : IsIso
      ((_root_.PresheafOfModules.sheafification (𝟙 scheme.ringCatSheaf.obj)).map
        (presheafDualEvaluation moduleSheaf)) := locallyBijective
  have counitIso : IsIso
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 scheme.ringCatSheaf.obj)).counit.app
        (𝟙_ scheme.Modules)) := inferInstance
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' evaluationIso counitIso)

/-- An invertible module sheaf tensored with its dual is the structure sheaf. -/
def tensorObjDualIsoUnit (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible] :
    moduleSheaf ⊗ moduleSheafᵛ ≅ 𝟙_ scheme.Modules :=
  asIso (dualEvaluation moduleSheaf)

/-- A tensor inverse of an invertible module sheaf is invertible. -/
theorem isInvertible_of_tensorObj_iso_unit (moduleSheaf targetSheaf : scheme.Modules)
    [invertible : moduleSheaf.IsInvertible]
    (trivialization : moduleSheaf ⊗ targetSheaf ≅ 𝟙_ scheme.Modules) :
    targetSheaf.IsInvertible := by
  refine (isInvertible_iff_forall_exists_pullback_unit _).2 fun point ↦ ?_
  obtain ⟨openSubset, membership, ⟨moduleTrivialization⟩⟩ := invertible.exists_isoUnit point
  exact ⟨openSubset, membership,
    ⟨(λ_ _).symm ≪≫ whiskerRightIso moduleTrivialization.symm _ ≪≫
      (pullbackTensorObjIso openSubset.ι moduleSheaf targetSheaf).symm ≪≫
      (pullback openSubset.ι).mapIso trivialization ≪≫ pullbackObjUnitIso openSubset.ι⟩⟩

/-- The dual of an invertible module sheaf is invertible. -/
instance isInvertible_dual (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible] :
    moduleSheafᵛ.IsInvertible :=
  isInvertible_of_tensorObj_iso_unit moduleSheaf _ (tensorObjDualIsoUnit moduleSheaf)

/-- Pullback commutes with the dual of an invertible module sheaf. -/
def pullbackDualIso {source : Scheme.{schemeUniverse}} (morphism : source ⟶ scheme)
    (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible] :
    (pullback morphism).obj moduleSheafᵛ ≅ ((pullback morphism).obj moduleSheaf)ᵛ := by
  let pulledSheaf := (pullback morphism).obj moduleSheaf
  let pulledDual := (pullback morphism).obj moduleSheafᵛ
  let evaluation : pulledSheaf ⊗ pulledDual ≅ 𝟙_ source.Modules :=
    (pullbackTensorObjIso morphism moduleSheaf moduleSheafᵛ).symm ≪≫
      (pullback morphism).mapIso (tensorObjDualIsoUnit moduleSheaf) ≪≫
        pullbackObjUnitIso morphism
  exact (λ_ pulledDual).symm ≪≫
    whiskerRightIso (((β_ pulledSheafᵛ pulledSheaf) ≪≫
      tensorObjDualIsoUnit pulledSheaf).symm) pulledDual ≪≫
    (α_ pulledSheafᵛ pulledSheaf pulledDual) ≪≫
    whiskerLeftIso pulledSheafᵛ evaluation ≪≫ ρ_ pulledSheafᵛ

end AlgebraicGeometry.Scheme.Modules
