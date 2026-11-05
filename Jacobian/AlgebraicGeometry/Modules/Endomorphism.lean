import Jacobian.AlgebraicGeometry.Cohomology.Basic
import Jacobian.AlgebraicGeometry.Modules.Invertible

/-!
# Endomorphisms of invertible module sheaves

Every endomorphism of an invertible module sheaf is multiplication by a unique
global function. The scalar is obtained from a local generator and glued using
the sheaf condition. Scalar multiplication commutes with pullback.

If a scheme morphism has a section and is surjective on global functions, an
isomorphism from an invertible module sheaf is determined by pullback to that
section. This rigidity makes normalized gluing maps unique.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{schemeUniverse}}

/-- Morphisms of module sheaves commute with restriction of sections. -/
lemma Hom.app_presheaf_map {moduleSheaf targetSheaf : scheme.Modules}
    (morphism : moduleSheaf ⟶ targetSheaf) {openSubset smallerOpen : scheme.Opens}
    (inclusion : smallerOpen ⟶ openSubset) (element : Γ(moduleSheaf, openSubset)) :
    morphism.app smallerOpen (moduleSheaf.presheaf.map inclusion.op element) =
      targetSheaf.presheaf.map inclusion.op (morphism.app openSubset element) :=
  PresheafOfModules.naturality_apply morphism.val inclusion.op element

/-- An invertible module sheaf is trivial on the over-site of a neighborhood of each point. -/
lemma exists_mem_over_iso_unit (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible]
    (point : scheme) :
    ∃ openSubset : scheme.Opens, point ∈ openSubset ∧
      Nonempty (moduleSheaf.over openSubset ≅
        SheafOfModules.unit (scheme.ringCatSheaf.over openSubset)) := by
  let invertible : moduleSheaf.IsInvertible := inferInstance
  obtain ⟨openSubset, membership, ⟨trivialization⟩⟩ :=
    invertible.exists_isoUnit point
  exact ⟨openSubset, membership, ⟨overIsoUnitOfPullbackIotaIso trivialization⟩⟩

/-- A rank-one trivialization identifies sections on every smaller open with functions. -/
def sectionsLinearEquivOfOverIsoUnit {moduleSheaf : scheme.Modules} {openSubset : scheme.Opens}
    (trivialization : moduleSheaf.over openSubset ≅
      SheafOfModules.unit (scheme.ringCatSheaf.over openSubset))
    {smallerOpen : scheme.Opens} (inclusion : smallerOpen ≤ openSubset) :
    Γ(moduleSheaf, smallerOpen) ≃ₗ[Γ(scheme, smallerOpen)] Γ(scheme, smallerOpen) where
  toFun := (trivialization.hom.val.app (op (Over.mk (homOfLE inclusion)))).hom
  invFun := (trivialization.inv.val.app (op (Over.mk (homOfLE inclusion)))).hom
  map_add' := map_add _
  map_smul' := (trivialization.hom.val.app (op (Over.mk (homOfLE inclusion)))).hom.map_smul
  left_inv element := by
    rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val,
      trivialization.hom_inv_id]
    rfl
  right_inv element := by
    rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val,
      trivialization.inv_hom_id]
    rfl

section Generator

variable {moduleSheaf : scheme.Modules} {openSubset : scheme.Opens}
    (trivialization : moduleSheaf.over openSubset ≅
      SheafOfModules.unit (scheme.ringCatSheaf.over openSubset))

/-- The generator corresponding to the constant function one under a trivialization. -/
def generatorOfOverIsoUnit : Γ(moduleSheaf, openSubset) :=
  (sectionsLinearEquivOfOverIsoUnit trivialization le_rfl).symm 1

/-- The local generator restricts to the generator on every smaller open. -/
lemma sectionsLinearEquivOfOverIsoUnit_symm_one {smallerOpen : scheme.Opens}
    (inclusion : smallerOpen ≤ openSubset) :
    (sectionsLinearEquivOfOverIsoUnit trivialization inclusion).symm 1 =
      moduleSheaf.presheaf.map (homOfLE inclusion).op (generatorOfOverIsoUnit trivialization) := by
  have naturality := ConcreteCategory.congr_hom
    (trivialization.inv.val.naturality
      (Over.homMk (homOfLE inclusion) : Over.mk (homOfLE inclusion) ⟶
        Over.mk (homOfLE (le_refl openSubset))).op) (1 : Γ(scheme, openSubset))
  refine Eq.trans ?_ (naturality.trans rfl)
  exact congrArg (trivialization.inv.val.app (op (Over.mk (homOfLE inclusion)))).hom
    (map_one (scheme.presheaf.map (homOfLE inclusion).op).hom).symm

/-- Every local section is its scalar coordinate times the local generator. -/
lemma eq_smul_generatorOfOverIsoUnit {smallerOpen : scheme.Opens}
    (inclusion : smallerOpen ≤ openSubset) (element : Γ(moduleSheaf, smallerOpen)) :
    element = sectionsLinearEquivOfOverIsoUnit trivialization inclusion element •
      moduleSheaf.presheaf.map (homOfLE inclusion).op (generatorOfOverIsoUnit trivialization) := by
  rw [← sectionsLinearEquivOfOverIsoUnit_symm_one, ← LinearEquiv.map_smul, smul_eq_mul, mul_one,
    LinearEquiv.symm_apply_apply]

/-- A scalar is determined by its action on a local generator. -/
lemma smul_generatorOfOverIsoUnit_injective {smallerOpen : scheme.Opens}
    (inclusion : smallerOpen ≤ openSubset) :
    Function.Injective fun scalar : Γ(scheme, smallerOpen) ↦
      scalar • moduleSheaf.presheaf.map (homOfLE inclusion).op
        (generatorOfOverIsoUnit trivialization) := by
  intro firstScalar secondScalar equality
  have coordinates := congrArg (sectionsLinearEquivOfOverIsoUnit trivialization inclusion) equality
  simpa [← sectionsLinearEquivOfOverIsoUnit_symm_one] using coordinates

end Generator

section Invertible

variable (moduleSheaf : scheme.Modules) [moduleSheaf.IsInvertible]

/-- Every endomorphism of an invertible module sheaf is multiplication by a global function. -/
theorem exists_eq_smulHom (endomorphism : moduleSheaf ⟶ moduleSheaf) :
    ∃ scalar : Γ(scheme, ⊤), endomorphism = moduleSheaf.smulHom scalar := by
  choose cover membership trivializations using fun point : scheme ↦
    exists_mem_over_iso_unit moduleSheaf point
  let generator (point : scheme) := generatorOfOverIsoUnit (trivializations point).some
  let coordinates (point : scheme) : Γ(scheme, cover point) :=
    sectionsLinearEquivOfOverIsoUnit (trivializations point).some le_rfl
      (endomorphism.app (cover point) (generator point))
  have localScalar (point : scheme) {smallerOpen : scheme.Opens}
      (inclusion : smallerOpen ≤ cover point) (element : Γ(moduleSheaf, smallerOpen)) :
      endomorphism.app smallerOpen element =
        scheme.presheaf.map (homOfLE inclusion).op (coordinates point) • element := by
    have generatorImage := eq_smul_generatorOfOverIsoUnit (trivializations point).some
      (le_refl (cover point)) (endomorphism.app (cover point) (generator point))
    have identityRestriction : moduleSheaf.presheaf.map (homOfLE (le_refl (cover point))).op
        (generator point) = generator point := by
      rw [show homOfLE (le_refl (cover point)) = 𝟙 _ from rfl, op_id, moduleSheaf.presheaf.map_id]
      rfl
    rw [identityRestriction] at generatorImage
    rw [eq_smul_generatorOfOverIsoUnit (trivializations point).some inclusion element,
      Hom.app_smul, Hom.app_presheaf_map, generatorImage, map_smul, smul_comm]
  have compatible : TopCat.Presheaf.IsCompatible scheme.sheaf.1 cover coordinates := by
    intro firstPoint secondPoint
    refine smul_generatorOfOverIsoUnit_injective (trivializations firstPoint).some
      (inf_le_left : cover firstPoint ⊓ cover secondPoint ≤ cover firstPoint) ?_
    exact (localScalar firstPoint (smallerOpen := cover firstPoint ⊓ cover secondPoint)
      inf_le_left _).symm.trans (localScalar secondPoint inf_le_right _)
  obtain ⟨scalar, restrictions, -⟩ : ∃! scalar : Γ(scheme, ⊤), ∀ point,
      scheme.presheaf.map (homOfLE le_top : cover point ⟶ ⊤).op scalar = coordinates point :=
    scheme.sheaf.existsUnique_gluing' cover ⊤ (fun _ ↦ homOfLE le_top)
      (fun point _ ↦ Opens.mem_iSup.mpr ⟨point, membership point⟩) coordinates compatible
  refine ⟨scalar, hom_ext _ _ fun openSubset ↦ ?_⟩
  ext element
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨moduleSheaf.presheaf, moduleSheaf.isSheaf⟩
    (fun point ↦ openSubset ⊓ cover point) openSubset (fun _ ↦ homOfLE inf_le_left)
    (fun point pointMembership ↦ Opens.mem_iSup.mpr
      ⟨point, pointMembership, membership point⟩) _ _ fun point ↦ ?_
  change moduleSheaf.presheaf.map (homOfLE inf_le_left : openSubset ⊓ cover point ⟶ openSubset).op
      (endomorphism.app openSubset element) =
    moduleSheaf.presheaf.map (homOfLE inf_le_left : openSubset ⊓ cover point ⟶ openSubset).op
      ((moduleSheaf.smulHom scalar).app openSubset element)
  rw [← Hom.app_presheaf_map, localScalar point inf_le_right, smulHom_app_apply, map_smul,
    ← restrictions point]
  congr 1
  change (scheme.presheaf.map _ ≫ scheme.presheaf.map _) scalar =
    (scheme.presheaf.map _ ≫ scheme.presheaf.map _) scalar
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- Multiplication by global functions is faithful on an invertible module sheaf. -/
theorem eq_of_smulHom_eq {firstScalar secondScalar : Γ(scheme, ⊤)}
    (equality : moduleSheaf.smulHom firstScalar = moduleSheaf.smulHom secondScalar) :
    firstScalar = secondScalar := by
  choose cover membership trivializations using fun point : scheme ↦
    exists_mem_over_iso_unit moduleSheaf point
  refine TopCat.Sheaf.eq_of_locally_eq' scheme.sheaf cover ⊤ (fun _ ↦ homOfLE le_top)
    (fun point _ ↦ Opens.mem_iSup.mpr ⟨point, membership point⟩)
    firstScalar secondScalar fun point ↦ ?_
  refine smul_generatorOfOverIsoUnit_injective (trivializations point).some
    (le_refl (cover point)) ?_
  have generatorEquality := congrArg (fun endomorphism ↦ endomorphism.app (cover point)
    (moduleSheaf.presheaf.map (homOfLE (le_refl (cover point))).op
      (generatorOfOverIsoUnit (trivializations point).some))) equality
  simp only [smulHom_app_apply] at generatorEquality
  exact generatorEquality

end Invertible

/-- Pullback of scalar multiplication is multiplication by the pulled-back function. -/
lemma pullback_map_smulHom {target : Scheme.{schemeUniverse}} (morphism : scheme ⟶ target)
    (moduleSheaf : target.Modules) (scalar : Γ(target, ⊤)) :
    (pullback morphism).map (moduleSheaf.smulHom scalar) =
      ((pullback morphism).obj moduleSheaf).smulHom (morphism.appTop scalar) := by
  apply ((pullbackPushforwardAdjunction morphism).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, pushforward_map_smulHom]
  erw [← (pullbackPushforwardAdjunction morphism).unit.naturality (moduleSheaf.smulHom scalar)]
  exact smulHom_naturality _ _

/-- Morphisms from an invertible sheaf, one an isomorphism, are determined by a rigid section. -/
theorem eq_of_pullback_map_eq {source base : Scheme.{schemeUniverse}}
    (projection : source ⟶ base) (sectionMorphism : base ⟶ source)
    (sectionCondition : sectionMorphism ≫ projection = 𝟙 base)
    (surjective : Function.Surjective projection.appTop)
    {moduleSheaf targetSheaf : source.Modules} [moduleSheaf.IsInvertible]
    (firstMorphism secondMorphism : moduleSheaf ⟶ targetSheaf) [IsIso secondMorphism]
    (equality : (pullback sectionMorphism).map firstMorphism =
      (pullback sectionMorphism).map secondMorphism) : firstMorphism = secondMorphism := by
  obtain ⟨scalar, scalarEquation⟩ := exists_eq_smulHom moduleSheaf
    (firstMorphism ≫ inv secondMorphism)
  obtain ⟨baseScalar, rfl⟩ := surjective scalar
  have baseEquation : ((pullback sectionMorphism).obj moduleSheaf).smulHom baseScalar =
      ((pullback sectionMorphism).obj moduleSheaf).smulHom 1 := by
    have sectionEquation : sectionMorphism.appTop (projection.appTop baseScalar) = baseScalar := by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, sectionCondition]
      rfl
    rw [smulHom_one, ← sectionEquation, ← pullback_map_smulHom, ← scalarEquation,
      Functor.map_comp, equality, Functor.map_inv, IsIso.hom_inv_id]
  rw [eq_of_smulHom_eq _ baseEquation, map_one, smulHom_one] at scalarEquation
  rw [← cancel_mono (inv secondMorphism), IsIso.hom_inv_id, scalarEquation]

end AlgebraicGeometry.Scheme.Modules
